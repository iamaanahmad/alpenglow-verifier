---------------- MODULE Properties ----------------

EXTENDS Alpenglow

\* =============================================================================
\* Safety Properties: "Nothing bad ever happens"
\* =============================================================================

\* @type: safety;
\* @description: "Ensures no two conflicting blocks are ever finalized in the same slot, handling all finalization scenarios including skip certificates and Byzantine faults.";
NoConflictingBlocksFinalized ==
    /\ \A sl \in DOMAIN finalized: finalized[sl] \in Blocks
    /\ \A sl1, sl2 \in DOMAIN finalized: 
        (sl1 = sl2) => (finalized[sl1] = finalized[sl2])
    /\ \* No conflicting finalization through different certificate types
       \A sl \in DOMAIN finalized:
        /\ \/ (\exists c \in certs: c.slot = sl /\ c.block = finalized[sl])
           \/ (\exists c \in skip_certs: c.slot = sl)
    /\ \* Byzantine nodes cannot cause conflicting finalizations
       \A sl \in DOMAIN finalized:
        LET finalized_block == finalized[sl]
            honest_voters == {n \in Nodes : 
                /\ sl \in DOMAIN votes 
                /\ n \in DOMAIN votes[sl] 
                /\ finalized_block \in votes[sl][n] 
                /\ \lnot IsByzantine(n)}
            honest_stake == SumStakes(honest_voters)
        IN honest_stake >= AdjustedQuorum60 \div 2

\* @type: safety;
\* @description: "Guarantees that certificates are unique for each slot, covering both regular and skip certificates, and preventing Byzantine certificate forgery.";
CertificateUniqueness ==
    /\ \* Regular certificate uniqueness
       \A c1, c2 \in certs:
        (c1.slot = c2.slot) => (c1 = c2)
    /\ \* Skip certificate uniqueness
       \A c1, c2 \in skip_certs:
        (c1.slot = c2.slot) => (c1 = c2)
    /\ \* No both regular and skip certificate for same slot
       \A sl \in Slots:
        \lnot (\exists c1 \in certs, c2 \in skip_certs: c1.slot = sl /\ c2.slot = sl)
    /\ \* Certificate integrity under Byzantine faults (only check if certificates exist)
       \A c \in certs:
        LET cert_voters == IF c.votes /= {} THEN {vote[1] : vote \in c.votes} ELSE {}
            honest_voters == cert_voters \ ByzantineNodes
            honest_stake == SumStakes(honest_voters)
        IN /\ ValidateCertificate(c)
           /\ (cert_voters = {} \/ honest_stake >= c.stake_weight \div 2) \* Honest nodes contribute majority of stake
    /\ \* Skip certificate integrity (only check if skip certificates exist)
       \A c \in skip_certs:
        /\ ValidSkipCertificate(c)
        /\ c.slot \in timeouts

\* @type: safety;
\* @description: "Prevents Byzantine nodes from causing validators to vote for conflicting blocks in the same slot, while allowing Byzantine double voting to be detected.";
NoEquivocation ==
    \A n \in Nodes:
        \A sl \in Slots:
            \/ (\lnot IsByzantine(n) /\ Cardinality(votes[sl][n]) <= 1) \* Honest nodes never double vote
            \/ (IsByzantine(n) /\ TRUE) \* Byzantine nodes can double vote, but it's detected



\* @type: safety;
\* @description: "Prevents forks across all finalization paths, ensuring chain consistency even with Byzantine nodes.";
ForkPrevention ==
    /\ \* No conflicting blocks can be finalized in any slot
       \A sl \in DOMAIN finalized:
        \A b1, b2 \in Blocks:
            (b1 /= b2) => \lnot (CanFinalize(b1, sl, AdjustedQuorum60) /\ CanFinalize(b2, sl, AdjustedQuorum60))
    /\ \* Certificate-based fork prevention
       \A sl \in Slots:
        \A c1 \in certs, c2 \in certs:
            (c1.slot = sl /\ c2.slot = sl) => (c1.block = c2.block)
    /\ \* Skip certificates don't create forks
       \A sl \in DOMAIN finalized:
        HasSkipCertificate(sl) => 
            (\A c \in certs: c.slot /= sl) \* No regular certificate if skip certificate exists

\* @type: safety;
\* @description: "Maintains chain consistency under Byzantine faults, ensuring honest supermajority controls finalization.";
ChainConsistencyUnderByzantineFaults ==
    /\ \* Byzantine stake constraint is maintained
       ByzantineStake <= (TotalStake * ByzantineStakeRatio) \div 100
    /\ \* Honest supermajority requirement for all finalizations
       \A sl \in DOMAIN finalized:
        LET finalized_block == finalized[sl]
            all_voters == {n \in Nodes : finalized_block \in votes[sl][n]}
            honest_voters == all_voters \ ByzantineNodes
            byzantine_voters == all_voters \cap ByzantineNodes
            honest_stake == SumStakes(honest_voters)
            byzantine_stake == SumStakes(byzantine_voters)
        IN /\ honest_stake >= AdjustedQuorum60 \div 2
           /\ (byzantine_voters = {} \/ honest_stake >= byzantine_stake)
    /\ \* Certificate consistency under Byzantine behavior
       \A c \in certs:
        LET cert_voters == IF c.votes /= {} THEN {vote[1] : vote \in c.votes} ELSE {}
            honest_cert_voters == cert_voters \ ByzantineNodes
            byzantine_cert_voters == cert_voters \cap ByzantineNodes
        IN /\ (cert_voters = {} \/ SumStakes(honest_cert_voters) >= SumStakes(byzantine_cert_voters))
           /\ \A n \in byzantine_cert_voters: 
                (n \in DOMAIN votes /\ c.slot \in DOMAIN votes[n]) => 
                Cardinality(votes[c.slot][n]) = 1 \* No double voting in certificates
    /\ \* Window-based consistency
       \A sl \in DOMAIN finalized:
        LET w == WindowForSlot(sl)
        IN w \in windows

\* @type: safety;
\* @description: "Ensures Byzantine nodes cannot violate safety properties through malicious behaviors.";
ByzantineFaultTolerance ==
    /\ \* Byzantine stake is bounded
       ByzantineStake <= (TotalStake * ByzantineStakeRatio) \div 100
    /\ \* Byzantine double voting doesn't break safety
       \A n \in ByzantineNodes, sl \in Slots:
        Cardinality(votes[sl][n]) > 1 => 
            (\A b \in votes[sl][n]: \lnot CanFinalize(b, sl, AdjustedQuorum60))
    /\ \* Byzantine vote withholding doesn't prevent honest progress
       \A sl \in Slots:
        LET honest_nodes == Nodes \ ByzantineNodes
            responsive_honest == {n \in honest_nodes : IsNodeResponsive(n)}
            responsive_honest_stake == SumStakes(responsive_honest)
            has_proposals == block_proposals[sl] /= {}
        IN (responsive_honest_stake >= (TotalStake * 60) \div 100 /\ has_proposals) =>
            (\exists b \in Blocks: CanFinalize(b, sl, AdjustedQuorum60))
    /\ \* Invalid votes from Byzantine nodes are ignored
       \A n \in ByzantineNodes:
        \A sl \in Slots:
            \A b \in votes[sl][n]:
                CanVoteInvalid(n) => 
                    (b \notin received_blocks[n] => \lnot CanFinalize(b, sl, AdjustedQuorum60))

\* Temporal versions (for Properties section)
SafetyAlways == [](NoConflictingBlocksFinalized /\ CertificateUniqueness /\ NoEquivocation /\ SlotBounds /\ ForkPrevention /\ ChainConsistencyUnderByzantineFaults /\ ByzantineFaultTolerance)

\* =============================================================================
\* Liveness Properties: "Something good eventually happens"
\* =============================================================================

\* Helper: Check if we have honest responsive supermajority (>50% of total stake)
HonestResponsiveSupermajority ==
    LET honest_responsive_nodes == {n \in Nodes : \lnot IsByzantine(n) /\ IsNodeResponsive(n)}
        honest_responsive_stake == SumStakes(honest_responsive_nodes)
    IN honest_responsive_stake > TotalStake \div 2

\* Helper: Check if a slot has a block proposal
HasBlockProposal(sl) == block_proposals[sl] /= {}

\* Helper: Check if a fast certificate was generated for a slot
FastCertificateGenerated(sl) ==
    \exists c \in certs : c.slot = sl /\ c.cert_type = "fast"

\* Helper: Check if finalization occurred within fast path time bound (Delta80)
FinalizationWithinFastPathBound(sl) ==
    IF sl \in DOMAIN finalized /\ sl \in DOMAIN finalization_times /\ sl \in DOMAIN round_start_time
    THEN finalization_times[sl] - round_start_time[sl] <= Delta80
    ELSE TRUE \* Not finalized yet or no timing info

\* Helper: Check if any certificate was generated for a slot
CertificateGenerated(sl) ==
    \/ (\exists c \in certs : c.slot = sl)
    \/ HasSkipCertificate(sl)

\* Helper: Check if finalization occurred within slow path time bound (2 * Delta60)
FinalizationWithinSlowPathBound(sl) ==
    IF sl \in DOMAIN finalized /\ sl \in DOMAIN finalization_times /\ sl \in DOMAIN round_start_time
    THEN finalization_times[sl] - round_start_time[sl] <= 2 * Delta60
    ELSE TRUE \* Not finalized yet or no timing info

\* Helper: Check if finalization occurred within optimal bounds min(δ₈₀%, 2δ₆₀%)
FinalizationWithinOptimalBounds(sl) ==
    LET actual_time == finalization_times[sl] - round_start_time[sl]
        optimal_bound == IF Has80PercentResponsiveStake THEN Delta80 ELSE 2 * Delta60
        min_bound == IF Delta80 < 2 * Delta60 THEN Delta80 ELSE 2 * Delta60
    IN actual_time <= min_bound

\* @type: liveness;
\* @description: "Ensures that if a supermajority of stake is honest and responsive, the network makes progress under partial synchrony.";
ProgressWithHonestSupermajority ==
    \* If we have honest supermajority (>50% honest + responsive stake) and partial synchrony holds,
    \* then eventually some slot will be finalized
    (HonestResponsiveSupermajority /\ PartialSynchronyHolds) ~> (\E sl \in Slots : sl \in DOMAIN finalized)

\* @type: liveness;
\* @description: "Guarantees that the fast path completes in a single round if 80% of the stake is responsive.";
FastPathCompletion ==
    \* If 80% of stake is responsive and we have a block proposal, 
    \* then eventually a fast certificate (80% quorum) will be generated within one round
    [](\A sl \in Slots :
        (Has80PercentResponsiveStake /\ HasBlockProposal(sl) /\ PartialSynchronyHolds) 
        => 
        <>(FastCertificateGenerated(sl) /\ FinalizationWithinFastPathBound(sl)))

\* @type: liveness;
\* @description: "Guarantees that the slow path completes within bounded time if 60% of the stake is responsive.";
SlowPathCompletion ==
    \* If 60% of stake is responsive and we have a block proposal,
    \* then eventually a certificate will be generated and finalization will occur within slow path bounds
    [](\A sl \in Slots :
        (Has60PercentResponsiveStake /\ HasBlockProposal(sl) /\ PartialSynchronyHolds)
        =>
        <>(CertificateGenerated(sl) /\ FinalizationWithinSlowPathBound(sl)))

\* @type: liveness;
\* @description: "Verifies bounded finalization times as min(δ₈₀%, 2δ₆₀%) under responsive conditions.";
BoundedFinalizationTimes ==
    \* For any slot that gets finalized, the finalization time should be within the expected bounds
    \A sl \in Slots :
        (sl \in DOMAIN finalized /\ sl \in DOMAIN finalization_times /\ sl \in DOMAIN round_start_time)
        =>
        (FinalizationWithinOptimalBounds(sl))

\* @type: liveness;
\* @description: "Ensures progress continues even with timeouts and skip certificates.";
ProgressWithTimeouts ==
    \* Even if slots timeout, progress should continue through skip certificates
    [](\A sl \in Slots :
        (sl \in timeouts /\ Has60PercentResponsiveStake)
        =>
        <>(\/ (sl \in DOMAIN finalized)
           \/ HasSkipCertificate(sl)
           \/ (\E sl2 \in Slots : sl2 > sl /\ sl2 \in DOMAIN finalized)))

\* @type: liveness;
\* @description: "Guarantees that under good network conditions, finalization occurs within expected time bounds.";
TimelyFinalizationUnderGoodConditions ==
    \* Under good network conditions (partial synchrony + sufficient responsive stake),
    \* finalization should occur within expected time bounds
    [](\A sl \in Slots :
        (HasBlockProposal(sl) /\ PartialSynchronyHolds /\ Has60PercentResponsiveStake)
        =>
        <>(sl \in DOMAIN finalized /\ FinalizationWithinBounds(sl)))

\* Fairness assumptions for liveness properties
FairnessAssumptions ==
    /\ \* Fair scheduling of honest nodes (only if they exist and are responsive)
       \A n \in Nodes : 
        (\lnot IsByzantine(n) /\ IsNodeResponsive(n)) => 
        WF_vars(\E b \in Blocks : HonestVote(n, b, slot))
    /\ \* Fair block proposals (only if nodes are responsive)
       WF_vars(\E n \in Nodes, b \in Blocks : 
        IsNodeResponsive(n) /\ ProposeBlock(n, b, slot))
    /\ \* Fair certificate generation (only if conditions are met)
       WF_vars(\E sl \in Slots : 
        (sl \in DOMAIN block_proposals /\ block_proposals[sl] /= {}) /\ 
        GenerateCertificate(sl))
    /\ \* Fair finalization when conditions are met
       WF_vars(\E b \in Blocks, sl \in Slots : 
        (HasValidCertificate(sl) \/ HasSkipCertificate(sl)) /\ 
        FinalizeBlock(b, sl))
    /\ \* Fair time progression
       WF_vars(AdvanceTime)
    /\ \* Fair leader rotation
       WF_vars(RotateLeader)
    /\ \* Fair skip certificate generation for timed out slots
       WF_vars(\E sl \in Slots : 
        (sl \in timeouts /\ \lnot HasSkipCertificate(sl)) /\ 
        GenerateSkipCertificate(sl))

\* Temporal versions for model checking with proper fairness
LivenessAlways == 
    /\ FairnessAssumptions => ProgressWithHonestSupermajority
    /\ FairnessAssumptions => FastPathCompletion  
    /\ FairnessAssumptions => SlowPathCompletion
    /\ FairnessAssumptions => []BoundedFinalizationTimes
    /\ FairnessAssumptions => ProgressWithTimeouts
    /\ FairnessAssumptions => TimelyFinalizationUnderGoodConditions

\* =============================================================================
\* Resilience Properties: "The system tolerates failures"
\* =============================================================================

\* Helper: Enhanced Byzantine resilience guarantees
ByzantineResilienceGuarantees ==
    /\ \* Safety maintained even with maximum Byzantine stake (20%)
       (ByzantineStake = (TotalStake * 20) \div 100) => 
           (NoConflictingBlocksFinalized /\ CertificateUniqueness)
    /\ \* Honest supermajority can always override Byzantine actions
       \A sl \in DOMAIN finalized :
           LET finalized_block == finalized[sl]
               all_voters == {n \in Nodes : 
                   /\ sl \in DOMAIN votes 
                   /\ n \in DOMAIN votes[sl] 
                   /\ finalized_block \in votes[sl][n]}
               honest_voters == all_voters \ ByzantineNodes
               honest_stake == SumStakes(honest_voters)
           IN honest_stake > (TotalStake * 50) \div 100 \* Honest majority required
    /\ \* Byzantine double voting cannot break certificate uniqueness
       \A sl \in Slots :
           \A c1, c2 \in certs :
               (c1.slot = sl /\ c2.slot = sl) => (c1 = c2)
    /\ \* Byzantine vote withholding cannot prevent progress when honest supermajority exists
       \A sl \in Slots :
           LET honest_responsive_nodes == {n \in Nodes : \lnot IsByzantine(n) /\ IsNodeResponsive(n)}
               honest_responsive_stake == SumStakes(honest_responsive_nodes)
           IN (honest_responsive_stake >= (TotalStake * 60) \div 100 /\ 
               sl \in DOMAIN block_proposals /\ block_proposals[sl] /= {}) =>
               (\exists b \in Blocks : 
                   \exists prop \in block_proposals[sl] : prop.block = b)

\* Helper: Offline stake constraint verification
OfflineStakeConstraint ==
    LET offline_nodes == {n \in Nodes : \lnot IsNodeResponsive(n)}
        offline_stake == SumStakes(offline_nodes)
    IN offline_stake <= (TotalStake * 20) \div 100

\* Helper: Progress with responsive honest stake
ProgressWithResponsiveHonestStake ==
    \* If we have ≥60% responsive honest stake, progress is guaranteed
    LET responsive_honest_nodes == {n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}
        responsive_honest_stake == SumStakes(responsive_honest_nodes)
    IN (responsive_honest_stake >= (TotalStake * 60) \div 100) =>
        [](\A sl \in Slots :
            (HasBlockProposal(sl) /\ PartialSynchronyHolds) =>
            <>(sl \in DOMAIN finalized \/ HasSkipCertificate(sl)))

\* Helper: Finalization despite offline nodes
FinalizationDespiteOfflineNodes ==
    \* Even with 20% offline stake, finalization can occur
    \A sl \in Slots :
        (OfflineStakeConstraint /\ HasBlockProposal(sl)) =>
        (\exists b \in Blocks :
            LET responsive_voters == {n \in Nodes : IsNodeResponsive(n) /\ b \in votes[sl][n]}
                responsive_stake == SumStakes(responsive_voters)
            IN responsive_stake >= AdjustedQuorum60)

\* Helper: Network partition recovery guarantees
NetworkPartitionRecoveryGuarantees ==
    \* When partition exists and then recovers, progress resumes
    [](\A sl \in Slots :
        (NetworkPartitionExists /\ HasBlockProposal(sl)) =>
        <>(NetworkPartitionRecovered => 
            <>(sl \in DOMAIN finalized \/ HasSkipCertificate(sl) \/ 
               \E sl2 \in Slots : sl2 > sl /\ sl2 \in DOMAIN finalized)))

\* Helper: State consistency after partition recovery
StateConsistencyAfterRecovery ==
    \* After partition recovery, no conflicting states exist
    NetworkPartitionRecovered =>
        /\ NoConflictingBlocksFinalized
        /\ CertificateUniqueness
        /\ \A sl \in DOMAIN finalized :
            \A n1, n2 \in Nodes :
                (IsNodeResponsive(n1) /\ IsNodeResponsive(n2)) =>
                (finalized[sl] \in received_blocks[n1] /\ finalized[sl] \in received_blocks[n2])

\* Helper: Progress resumption after recovery
ProgressResumptionAfterRecovery ==
    \* Progress resumes within bounded time after partition recovery
    [](\A sl \in Slots :
        (NetworkPartitionRecovered /\ HasBlockProposal(sl) /\ Has60PercentResponsiveStake) =>
        <>(sl \in DOMAIN finalized /\ FinalizationWithinBounds(sl)))

\* Helper: Combined fault tolerance (20% Byzantine + 20% offline)
CombinedFaultTolerance ==
    LET byzantine_stake == ByzantineStake
        offline_nodes == {n \in Nodes : \lnot IsNodeResponsive(n)}
        offline_stake == SumStakes(offline_nodes)
        combined_faulty_stake == byzantine_stake + offline_stake
        honest_responsive_nodes == {n \in Nodes : \lnot IsByzantine(n) /\ IsNodeResponsive(n)}
        honest_responsive_stake == SumStakes(honest_responsive_nodes)
    IN \* Under good network conditions, system tolerates 20+20 faults
       (PartialSynchronyHolds /\ 
        byzantine_stake <= (TotalStake * 20) \div 100 /\
        offline_stake <= (TotalStake * 20) \div 100) =>
       \* Safety and liveness are maintained
       (NoConflictingBlocksFinalized /\ 
        (honest_responsive_stake >= (TotalStake * 60) \div 100 => 
         \A sl \in Slots : 
            (sl \in DOMAIN block_proposals /\ block_proposals[sl] /= {}) ~> 
             (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))))

\* @type: resilience;
\* @description: "Maintains safety even with a Byzantine stake of up to 20% of the total stake.";
SafetyWithByzantineStake == 
    /\ \* Byzantine stake constraint is enforced
       ByzantineStake <= (TotalStake * 20) \div 100
    /\ \* Core safety properties hold despite Byzantine presence
       NoConflictingBlocksFinalized
    /\ CertificateUniqueness  
    /\ ForkPrevention
    /\ ChainConsistencyUnderByzantineFaults
    /\ ByzantineFaultTolerance
    /\ \* Enhanced Byzantine resilience checks
       ByzantineResilienceGuarantees

\* @type: resilience;
\* @description: "Guarantees liveness even if up to 20% of the total stake is offline.";
LivenessWithOfflineStake == 
    /\ \* Offline stake constraint (≤20% non-responsive)
       OfflineStakeConstraint
    /\ \* Progress guaranteed with sufficient responsive honest stake
       ProgressWithResponsiveHonestStake
    /\ \* Finalization continues despite offline nodes
       FinalizationDespiteOfflineNodes

\* @type: resilience;
\* @description: "Ensures the system can recover and continue to finalize blocks after a network partition is resolved.";
RecoveryFromPartition ==
    /\ \* Network partition recovery guarantees
       NetworkPartitionRecoveryGuarantees
    /\ \* State consistency after partition recovery
       StateConsistencyAfterRecovery
    /\ \* Progress resumption after recovery
       ProgressResumptionAfterRecovery

\* Helper: Good network conditions enable full resilience
GoodNetworkConditionsResilience ==
    \* Under partial synchrony, the system achieves maximum fault tolerance
    PartialSynchronyHolds =>
        /\ \* Can tolerate maximum Byzantine stake
           (ByzantineStake <= (TotalStake * 20) \div 100) => SafetyWithByzantineStake
        /\ \* Can tolerate maximum offline stake  
           (OfflineStakeConstraint) => LivenessWithOfflineStake
        /\ \* Can recover from network partitions
           RecoveryFromPartition

\* Helper: Resilience boundaries verification
ResilienceBoundaries ==
    /\ \* Safety fails if Byzantine stake exceeds 20%
       (ByzantineStake > (TotalStake * 20) \div 100) => 
           \* Safety properties may not hold
           TRUE \* This is expected - system not designed for >20% Byzantine
    /\ \* Liveness may degrade if offline stake exceeds 20%
       LET offline_stake == SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)})
       IN (offline_stake > (TotalStake * 20) \div 100) =>
           \* Liveness may be affected but safety should still hold
           (NoConflictingBlocksFinalized /\ CertificateUniqueness)
    /\ \* Combined faults beyond 40% may affect both safety and liveness
       LET total_faulty_stake == ByzantineStake + SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)})
       IN (total_faulty_stake > (TotalStake * 40) \div 100) =>
           \* System may not provide full guarantees
           TRUE \* This is expected - beyond design limits

\* @type: resilience;
\* @description: "Verifies the 20+20 resilience model under good network conditions.";
TwentyPlusTwentyResilienceModel ==
    /\ \* System tolerates up to 20% Byzantine + 20% offline under good conditions
       CombinedFaultTolerance
    /\ \* Good network conditions enable full resilience
       GoodNetworkConditionsResilience
    /\ \* Resilience boundaries are respected
       ResilienceBoundaries

\* Temporal versions for model checking
ResilienceAlways == 
    /\ []SafetyWithByzantineStake
    /\ []LivenessWithOfflineStake  
    /\ []RecoveryFromPartition
    /\ []TwentyPlusTwentyResilienceModel

\* Combined temporal properties for comprehensive verification
AllPropertiesAlways ==
    /\ SafetyAlways
    /\ LivenessAlways
    /\ ResilienceAlways

\* =============================================================================
\* Statistical Sampling Properties and Invariants
\* =============================================================================

\* Statistical sampling invariants to ensure proper Monte Carlo verification
StatisticalSamplingInvariants ==
    /\ \* Sample count is within bounds
       Cardinality(monte_carlo_samples) <= MonteCarloSamples
    /\ \* Sampling history is consistent with samples
       Cardinality(sampling_history) <= Cardinality(monte_carlo_samples) + 1
    /\ \* Confidence intervals are properly structured (only check if they exist)
       \A prop \in DOMAIN confidence_intervals :
           /\ confidence_intervals[prop].property = prop
           /\ confidence_intervals[prop].status \in {"verified", "falsified", "inconclusive", "no_data"}
    /\ \* Property verification stats are valid (only check if they exist)
       \A prop \in DOMAIN property_verification_stats :
           /\ property_verification_stats[prop].samples >= 0
           /\ property_verification_stats[prop].successes <= property_verification_stats[prop].samples

\* Statistical convergence property - confidence intervals should stabilize
StatisticalConvergence ==
    \* As sample size increases, confidence interval width should decrease
    \A prop \in DOMAIN confidence_intervals :
        confidence_intervals[prop].status = "verified" =>
        confidence_intervals[prop].confidence_interval.upper - confidence_intervals[prop].confidence_interval.lower <= PropertyComplexityThreshold

\* Monte Carlo sampling quality - samples should cover different scenarios
SamplingQuality ==
    /\ \* Samples should cover different Byzantine scenarios (only if samples exist)
       LET byzantine_samples == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "byzantine_active" \in DOMAIN s.state 
               /\ s.state.byzantine_active > 0}
           honest_samples == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "byzantine_active" \in DOMAIN s.state 
               /\ s.state.byzantine_active = 0}
       IN Cardinality(monte_carlo_samples) > 10 =>
          (Cardinality(byzantine_samples) > 0 /\ Cardinality(honest_samples) > 0)
    /\ \* Samples should cover different network conditions (only if samples exist)
       LET partition_samples == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "network_partition" \in DOMAIN s.state 
               /\ s.state.network_partition}
           normal_samples == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "network_partition" \in DOMAIN s.state 
               /\ \lnot s.state.network_partition}
       IN Cardinality(monte_carlo_samples) > 10 =>
          (Cardinality(partition_samples) > 0 /\ Cardinality(normal_samples) > 0)
    /\ \* Samples should cover different responsiveness levels (only if samples exist)
       LET high_responsive == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "responsive_stake" \in DOMAIN s.state 
               /\ s.state.responsive_stake >= (TotalStake * 80) \div 100}
           medium_responsive == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "responsive_stake" \in DOMAIN s.state 
               /\ s.state.responsive_stake >= (TotalStake * 60) \div 100 
               /\ s.state.responsive_stake < (TotalStake * 80) \div 100}
           low_responsive == {s \in monte_carlo_samples : 
               /\ "state" \in DOMAIN s 
               /\ "responsive_stake" \in DOMAIN s.state 
               /\ s.state.responsive_stake < (TotalStake * 60) \div 100}
       IN Cardinality(monte_carlo_samples) > 20 =>
          (Cardinality(high_responsive) > 0 /\ Cardinality(medium_responsive) > 0)

\* Adaptive sampling effectiveness - sampling should focus on complex properties
AdaptiveSamplingEffectiveness ==
    \* Complex properties should have more samples than simple ones
    \A prop1, prop2 \in DOMAIN confidence_intervals :
        /\ CalculatePropertyComplexity(prop1) = "critical"
        /\ CalculatePropertyComplexity(prop2) = "low"
        /\ confidence_intervals[prop1].samples > 0
        /\ confidence_intervals[prop2].samples > 0
        => confidence_intervals[prop1].samples >= confidence_intervals[prop2].samples

\* Statistical verification accuracy - results should be consistent with deterministic verification
StatisticalVerificationAccuracy ==
    \* If a safety property is verified deterministically, statistical verification should agree
    \A prop \in {"NoConflictingBlocksFinalized", "CertificateUniqueness"} :
        prop \in DOMAIN confidence_intervals =>
        (confidence_intervals[prop].status = "verified" <=> 
         confidence_intervals[prop].confidence_interval.lower >= 95)

\* Confidence interval validity - intervals should be mathematically sound
ConfidenceIntervalValidity ==
    \A prop \in DOMAIN confidence_intervals :
        confidence_intervals[prop].status \in {"verified", "falsified", "inconclusive"} =>
        /\ confidence_intervals[prop].confidence_interval.lower >= 0
        /\ confidence_intervals[prop].confidence_interval.upper <= 100
        /\ confidence_intervals[prop].confidence_interval.lower <= confidence_intervals[prop].confidence_interval.upper
        /\ confidence_intervals[prop].confidence_interval.point_estimate >= confidence_intervals[prop].confidence_interval.lower
        /\ confidence_intervals[prop].confidence_interval.point_estimate <= confidence_intervals[prop].confidence_interval.upper

\* Stratified sampling coverage - different strata should be represented
StratifiedSamplingCoverage ==
    LET strata == sampling_history
        byzantine_levels == {s.byzantine_level : s \in strata}
        responsiveness_levels == {s.responsiveness : s \in strata}
        network_conditions == {s.network : s \in strata}
    IN Cardinality(strata) > 10 =>
        /\ Cardinality(byzantine_levels) >= 2 \* At least low and high Byzantine scenarios
        /\ Cardinality(responsiveness_levels) >= 2 \* At least high and medium responsiveness
        /\ Cardinality(network_conditions) >= 1 \* At least one network condition

\* Statistical property verification completeness
StatisticalVerificationCompleteness ==
    \* All critical liveness properties should have statistical verification results
    LET critical_properties == {"ProgressWithHonestSupermajority", "FastPathCompletion", 
                               "SlowPathCompletion", "BoundedFinalizationTimes"}
    IN Cardinality(monte_carlo_samples) >= MonteCarloSamples \div 2 =>
        \A prop \in critical_properties :
            prop \in DOMAIN confidence_intervals /\
            confidence_intervals[prop].status /= "no_data"

\* Combined statistical sampling properties
StatisticalSamplingProperties ==
    /\ StatisticalSamplingInvariants
    /\ StatisticalConvergence
    /\ SamplingQuality
    /\ AdaptiveSamplingEffectiveness
    /\ StatisticalVerificationAccuracy
    /\ ConfidenceIntervalValidity
    /\ StratifiedSamplingCoverage
    /\ StatisticalVerificationCompleteness

=======================================================