---------------- MODULE MC_10Nodes ----------------

EXTENDS Alpenglow, Properties

\* 10-node test configuration for statistical model checking for large scale
\* This configuration implements stress testing with high Byzantine ratios and performance boundary testing

\* =============================================================================
\* 10-Node Specific Constants and Constraints
\* =============================================================================

\* Node stake distribution for 10-node setup (equal stakes for simplicity)
\* Note: Nodes are defined in the .cfg file as {n1, n2, n3, n4, n5, n6, n7, n8, n9, n10}
NodeStakes == [n \in Nodes |-> TotalStake \div Cardinality(Nodes)]

\* High Byzantine ratio scenarios for stress testing
\* With 10 nodes at 10% stake each, we can test up to 2 Byzantine nodes (20% = limit)
StressByzantineScenarios == 
    { {},                                      \* No Byzantine nodes (honest case)
      {CHOOSE n \in Nodes : TRUE},             \* Single Byzantine node (10%)
      LET n1 == CHOOSE n \in Nodes : TRUE
          n2 == CHOOSE n \in Nodes : n /= n1
      IN {n1, n2}                              \* Double Byzantine nodes (20%)
    }

\* Network responsiveness scenarios for large-scale offline testing
\* Test various combinations of offline nodes up to and beyond 20% stake limit
ResponsivenessStressScenarios ==
    LET offline_node == CHOOSE n \in Nodes : TRUE
        offline_pair == LET n1 == CHOOSE n \in Nodes : TRUE
                            n2 == CHOOSE n \in Nodes : n /= n1
                        IN {n1, n2}
    IN { [n \in Nodes |-> TRUE],                                 \* All responsive
         [n \in Nodes |-> IF n = offline_node THEN FALSE ELSE TRUE], \* One offline
         [n \in Nodes |-> IF n \in offline_pair THEN FALSE ELSE TRUE] \* Two offline
       }

\* Combined high-stress fault scenarios for performance boundary testing
HighStressFaultScenarios ==
    { \* Maximum allowed Byzantine + Offline combinations
      [byzantine |-> {}, offline |-> {}],                                    \* No faults
      [byzantine |-> {CHOOSE n \in Nodes : TRUE}, offline |-> {}],           \* 1 Byzantine (10%)
      [byzantine |-> {}, offline |-> {CHOOSE n \in Nodes : TRUE}],           \* 1 Offline (10%)
      [byzantine |-> {CHOOSE n \in Nodes : TRUE}, 
       offline |-> {CHOOSE n \in Nodes : n /= (CHOOSE m \in Nodes : TRUE)}]     \* 1 Byzantine + 1 Offline (20%)
    }

\* =============================================================================
\* State Constraints for Statistical Model Checking
\* =============================================================================

\* Optimized state constraint for 10-node statistical model checking
\* Focus on key states while allowing sufficient exploration for statistical validity
TenNodeStateConstraint ==
    /\ StateConstraint  \* Basic constraint from Alpenglow
    /\ current_time <= MaxTime
    /\ Cardinality(DOMAIN finalized) <= MaxSlot
    /\ Cardinality(certs) <= MaxSlot * 4  \* Allow more certificates for larger network
    /\ Cardinality(skip_certs) <= MaxSlot
    /\ Cardinality(timeouts) <= MaxSlot
    /\ \A sl \in Slots : Cardinality(block_proposals[sl]) <= 3  \* Limit proposals per slot for efficiency
    /\ \A n \in Nodes : Cardinality(received_blocks[n]) <= Cardinality(Blocks)
    /\ current_window <= MaxWindow
    /\ \* Statistical sampling constraints for large-scale efficiency
       Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 3  \* Max 3 offline nodes (30%)
    /\ Cardinality(ByzantineNodes) <= 2  \* Max 2 Byzantine nodes (20%) for stress testing
    /\ \* Performance boundary constraints
       \A n \in Nodes : Cardinality({sl \in Slots : \exists b \in Blocks : VotorVote(n, b, sl)}) <= MaxSlot * 2

\* =============================================================================
\* 10-Node Stress Test Scenarios
\* =============================================================================

\* Test scenario: All nodes honest and responsive (baseline for 10 nodes)
AllHonestResponsiveScenario10 ==
    /\ ByzantineNodes = {}
    /\ \A n \in Nodes : IsNodeResponsive(n)
    /\ ValidByzantineStake

\* Test scenario: Maximum Byzantine nodes at 20% limit (2 nodes = 20%)
MaxByzantineStressScenario10 ==
    /\ Cardinality(ByzantineNodes) = 2
    /\ ByzantineStake = (TotalStake * 20) \div 100  \* Exactly 20%
    /\ ByzantineStake <= (TotalStake * 20) \div 100

\* Test scenario: Maximum offline nodes at 20% limit
MaxOfflineStressScenario10 ==
    /\ ByzantineNodes = {}
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 2
    /\ SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) = (TotalStake * 20) \div 100

\* Test scenario: Combined maximum stress (2 Byzantine + 2 offline = 40% total)
MaxCombinedStressScenario10 ==
    /\ Cardinality(ByzantineNodes) = 2
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 2
    /\ ByzantineNodes \cap {n \in Nodes : \lnot IsNodeResponsive(n)} = {}  \* Different nodes
    /\ ByzantineStake + SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) = (TotalStake * 40) \div 100

\* Test scenario: Fast path stress conditions (exactly 80% responsive stake)
FastPathStressScenario10 ==
    /\ ByzantineNodes = {}
    /\ Cardinality({n \in Nodes : IsNodeResponsive(n)}) = 8  \* 8/10 = 80% exactly
    /\ SumStakes({n \in Nodes : IsNodeResponsive(n)}) = Quorum80

\* Test scenario: Slow path stress conditions (exactly 60% responsive stake)
SlowPathStressScenario10 ==
    /\ Cardinality(ByzantineNodes) <= 2
    /\ Cardinality({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) = 6  \* 6/10 = 60% exactly
    /\ SumStakes({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) = Quorum60

\* Test scenario: Performance boundary testing (high network delays)
PerformanceBoundaryScenario10 ==
    /\ ByzantineNodes = {}
    /\ \A n \in Nodes : IsNodeResponsive(n)
    /\ NetworkDelay = MaxNetworkDelay  \* Maximum network delay
    /\ SlotTimeout = MaxTime \div MaxSlot  \* Tight timing constraints

\* =============================================================================
\* Action Constraints for Statistical Model Checking
\* =============================================================================

\* Action constraint optimized for statistical sampling and performance testing
TenNodeActionConstraint ==
    \* Focus on critical actions for statistical validity while maintaining performance
    \/ (\exists n \in Nodes, b \in Blocks, sl \in Slots : VotorVote(n, b, sl))
    \/ (\exists n \in Nodes, b \in Blocks, sl \in Slots : ProposeBlock(n, b, sl))
    \/ (\exists sender, receiver \in Nodes, b \in Blocks, sl \in Slots : RelayBlock(sender, receiver, b, sl))
    \/ (\exists sl \in Slots : GenerateCertificate(sl))
    \/ (\exists b \in Blocks, sl \in Slots : FinalizeBlock(b, sl))
    \/ (\exists sl \in Slots : TimeoutSlot(sl))
    \/ (\exists sl \in Slots : GenerateSkipCertificate(sl))
    \/ AdvanceTime
    \/ RotateLeader
    \/ AdvanceWindow
    \/ (\exists n \in Nodes : NodeGoesOffline(n))
    \/ (\exists n \in Nodes : NodeComesOnline(n))
    \/ \* Additional actions for stress testing
       (\exists n \in ByzantineNodes, b1, b2 \in Blocks, sl \in Slots : 
           b1 /= b2 /\ ByzantineDoubleVote(n, b1, b2, sl))
    \/ (\exists n \in ByzantineNodes, sl \in Slots : ByzantineWithholdVote(n, sl))

\* =============================================================================
\* 10-Node Stress Testing Properties
\* =============================================================================

\* Property: Fast path should work with 8+ responsive nodes (80% exactly)
FastPathWith8Nodes10 ==
    (Cardinality({n \in Nodes : IsNodeResponsive(n)}) >= 8 /\ 
     \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>FastCertificateGenerated(sl)

\* Property: Slow path should work with 6+ honest responsive nodes (60% exactly)
SlowPathWith6Nodes10 ==
    (Cardinality({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= 6 /\
     \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>CertificateGenerated(sl)

\* Property: Safety should hold with 2 Byzantine nodes (20% exactly)
SafetyWith2Byzantine10Nodes ==
    (Cardinality(ByzantineNodes) = 2 /\ ByzantineStake = (TotalStake * 20) \div 100) =>
    (NoConflictingBlocksFinalized /\ CertificateUniqueness /\ ForkPrevention)

\* Property: Liveness should hold with 2 offline nodes (20% exactly)
LivenessWith2Offline10Nodes ==
    (Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 2 /\
     SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) = (TotalStake * 20) \div 100) =>
    \A sl \in Slots : HasBlockProposal(sl) ~> 
        (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))

\* Property: Maximum stress fault tolerance (2 Byzantine + 2 offline = 40% total)
MaxStressFaultTolerance10Nodes ==
    (Cardinality(ByzantineNodes) = 2 /\
     Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 2 /\
     ByzantineNodes \cap {n \in Nodes : \lnot IsNodeResponsive(n)} = {}) =>
    \* Safety should still hold under maximum stress
    (NoConflictingBlocksFinalized /\ CertificateUniqueness)

\* Property: Performance under high network delays
PerformanceUnderHighDelays10Nodes ==
    (NetworkDelay = MaxNetworkDelay /\ \A n \in Nodes : IsNodeResponsive(n)) =>
    \A sl \in Slots : HasBlockProposal(sl) ~> 
        <>(\exists c \in certs : c.slot = sl)

\* Property: Byzantine stake validation for 10-node stress testing
ByzantineStakeStressValidation10Nodes ==
    /\ \* Up to 2 Byzantine nodes should be within limits
       (Cardinality(ByzantineNodes) <= 2) => (ByzantineStake <= (TotalStake * 20) \div 100)
    /\ \* More than 2 Byzantine nodes should exceed limits and be detected
       (Cardinality(ByzantineNodes) > 2) => \lnot ValidByzantineStake

\* Property: Scalability verification for 10-node network
ScalabilityVerification10Nodes ==
    /\ \* Certificate generation scales with larger network
       \A sl \in Slots : HasBlockProposal(sl) => 
           <>(\exists c \in certs : c.slot = sl /\ c.stake_weight >= Quorum60)
    /\ \* Block propagation efficiency with 10 nodes
       \A b \in Blocks, sl \in Slots :
           (\exists n \in Nodes : b \in block_proposals[sl]) =>
           <>(\A n \in Nodes : IsNodeResponsive(n) => b \in received_blocks[n])
    /\ \* Erasure coding effectiveness with larger network
       \A b \in Blocks, sl \in Slots :
           (block_proposals[sl] /= {}) =>
           <>(\A receiver \in Nodes : 
               IsNodeResponsive(receiver) =>
               \/ b \in received_blocks[receiver]
               \/ CanReconstructFromErasureCodingWithReceiver(receiver, b, sl))

\* Property: Resilience boundaries for 10-node stress configuration
ResilienceBoundariesStress10Nodes ==
    /\ \* Up to 2 Byzantine nodes: safety maintained
       (Cardinality(ByzantineNodes) <= 2) => SafetyWithByzantineStake
    /\ \* Up to 2 offline nodes: liveness maintained if sufficient honest responsive stake
       (Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 2) => 
           (SumStakes({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= Quorum60 =>
            LivenessWithOfflineStake)
    /\ \* Combined stress faults: safety always, liveness conditionally
       (Cardinality(ByzantineNodes) <= 2 /\
        Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 2) =>
       (SafetyWithByzantineStake /\
        (SumStakes({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= Quorum60 =>
         LivenessWithOfflineStake))

\* =============================================================================
\* Statistical Model Checking Configuration
\* =============================================================================

\* Statistical sampling configuration for large-scale verification
StatisticalSamplingConfig ==
    /\ stake \in {NodeStakes}
    /\ byzantine_behaviors \in [Nodes -> ByzantineBehaviorTypes]
    /\ node_responsiveness \in ResponsivenessStressScenarios

\* Monte Carlo simulation parameters (to be used with TLC statistical features)
SampleSize == 1000
ErrorTolerance == 5

MonteCarloParameters ==
    /\ SampleSize = 1000
    /\ ConfidenceLevel = 95  \* Using the constant from Alpenglow.tla
    /\ ErrorTolerance = 5

\* =============================================================================
\* Verification Goals for 10-Node Stress Configuration
\* =============================================================================

\* Goal 1: Verify safety properties under maximum stress scenarios
SafetyStressVerificationGoal10 ==
    \A byzantine_set \in StressByzantineScenarios :
        (ByzantineNodes = byzantine_set /\ Cardinality(byzantine_set) <= 2) =>
        (NoConflictingBlocksFinalized /\ CertificateUniqueness /\ ForkPrevention /\ ChainConsistencyUnderByzantineFaults)

\* Goal 2: Verify liveness properties under stress conditions
LivenessStressVerificationGoal10 ==
    \A responsiveness \in ResponsivenessStressScenarios :
        (node_responsiveness = responsiveness /\
         SumStakes({n \in Nodes : responsiveness[n] /\ \lnot IsByzantine(n)}) >= Quorum60) =>
        \A sl \in Slots : HasBlockProposal(sl) ~> 
            (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))

\* Goal 3: Verify resilience under maximum combined stress
ResilienceStressVerificationGoal10 ==
    \A scenario \in HighStressFaultScenarios :
        LET byzantine_stake == SumStakes(scenario.byzantine)
            offline_stake == SumStakes(scenario.offline)
            total_faulty_stake == byzantine_stake + offline_stake
            honest_responsive_stake == SumStakes({n \in Nodes : n \notin scenario.byzantine /\ n \notin scenario.offline})
        IN (total_faulty_stake <= (TotalStake * 40) \div 100) =>
            \* Safety always maintained under stress
            (NoConflictingBlocksFinalized /\ CertificateUniqueness /\
             \* Liveness maintained if sufficient honest responsive stake
             (honest_responsive_stake >= Quorum60 =>
              \A sl \in Slots : HasBlockProposal(sl) ~> 
                  (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))))

\* Goal 4: Verify performance boundaries and scalability
PerformanceBoundaryVerificationGoal10 ==
    /\ \* Performance under maximum network delays
       PerformanceUnderHighDelays10Nodes
    /\ \* Scalability with 10 nodes
       ScalabilityVerification10Nodes
    /\ \* Stress testing with maximum allowed faults
       MaxStressFaultTolerance10Nodes
    /\ \* Byzantine stake validation under stress
       ByzantineStakeStressValidation10Nodes
    /\ \* Resilience boundaries under stress
       ResilienceBoundariesStress10Nodes

\* Goal 5: Statistical verification of probabilistic properties
StatisticalVerificationGoal10 ==
    /\ \* Fast path completion probability with 80%+ responsive stake
       (SumStakes({n \in Nodes : IsNodeResponsive(n)}) >= Quorum80) =>
       \A sl \in Slots : HasBlockProposal(sl) => 
           Probability(FastCertificateGenerated(sl)) >= 95
    /\ \* Slow path completion probability with 60%+ responsive stake
       (SumStakes({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= Quorum60) =>
       \A sl \in Slots : HasBlockProposal(sl) => 
           Probability(CertificateGenerated(sl)) >= 90
    /\ \* Safety probability under Byzantine stress
       (Cardinality(ByzantineNodes) <= 2) =>
       Probability(NoConflictingBlocksFinalized /\ CertificateUniqueness) >= 99

\* Goal 6: Complete stress testing verification
CompleteStressTestingGoal10 ==
    /\ SafetyStressVerificationGoal10
    /\ LivenessStressVerificationGoal10  
    /\ ResilienceStressVerificationGoal10
    /\ PerformanceBoundaryVerificationGoal10
    /\ StatisticalVerificationGoal10

=======================================================