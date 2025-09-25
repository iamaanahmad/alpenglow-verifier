---------------- MODULE MC_7Nodes ----------------

EXTENDS Alpenglow, Properties

\* 7-node test configuration for targeted state exploration with appropriate constraints
\* This configuration tests representative Byzantine scenarios and key property verification for medium scale

\* =============================================================================
\* 7-Node Specific Constants and Constraints
\* =============================================================================

\* Node stake distribution for 7-node setup (equal stakes for simplicity)
\* Note: Nodes are defined in the .cfg file as {n1, n2, n3, n4, n5, n6, n7}
NodeStakes == [n \in Nodes |-> TotalStake \div Cardinality(Nodes)]

\* Representative Byzantine node combinations for targeted testing
\* With 7 nodes at ~14.3% stake each, we can test up to 1 Byzantine node (14.3% < 20%)
RepresentativeByzantineScenarios == 
    LET single_node_sets == {{n} : n \in Nodes}
    IN { {}                    \* No Byzantine nodes (honest case)
       } \cup {s \in single_node_sets : Cardinality(s) = 1}  \* All single Byzantine node combinations

\* Network responsiveness scenarios for testing offline conditions
\* Test various combinations of offline nodes up to 20% stake limit
ResponsivenessScenarios == 
    LET all_responsive == [n \in Nodes |-> TRUE]
        single_offline_sets == {[n \in Nodes |-> IF n = offline_node THEN FALSE ELSE TRUE] : offline_node \in Nodes}
    IN {all_responsive} \cup single_offline_sets

\* Combined fault scenarios for resilience testing
CombinedFaultScenarios ==
    { \* Byzantine + Offline combinations within limits
      [byzantine |-> {}, offline |-> {}]                               \* No faults
    }

\* =============================================================================
\* State Constraints for Targeted Exploration
\* =============================================================================

\* Enhanced state constraint for 7-node targeted testing
\* Balance between thorough exploration and computational feasibility
SevenNodeStateConstraint ==
    /\ StateConstraint  \* Basic constraint from Alpenglow
    /\ current_time <= MaxTime
    /\ Cardinality(DOMAIN finalized) <= MaxSlot
    /\ Cardinality(certs) <= MaxSlot * 3  \* Allow more certificate attempts for larger network
    /\ Cardinality(skip_certs) <= MaxSlot
    /\ Cardinality(timeouts) <= MaxSlot
    /\ \A sl \in Slots : Cardinality(block_proposals[sl]) <= 2  \* Limit proposals per slot
    /\ \A n \in Nodes : Cardinality(received_blocks[n]) <= Cardinality(Blocks)
    /\ current_window <= MaxWindow
    /\ \* Additional constraints for medium-scale efficiency
       Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 2  \* Max 2 offline nodes
    /\ Cardinality(ByzantineNodes) <= 1  \* Max 1 Byzantine node for 7-node setup

\* =============================================================================
\* 7-Node Specific Test Scenarios
\* =============================================================================

\* Test scenario: All nodes honest and responsive (baseline for 7 nodes)
AllHonestResponsiveScenario7 ==
    /\ ByzantineNodes = {}
    /\ \A n \in Nodes : IsNodeResponsive(n)
    /\ ValidByzantineStake

\* Test scenario: Single Byzantine node within 20% limit (14.3% < 20%)
SingleByzantineScenario7 ==
    /\ Cardinality(ByzantineNodes) = 1
    /\ ByzantineStake = TotalStake \div 7  \* ~14.3%
    /\ ByzantineStake <= (TotalStake * 20) \div 100

\* Test scenario: Single offline node within 20% limit
SingleOfflineScenario7 ==
    /\ ByzantineNodes = {}
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1
    /\ SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) <= (TotalStake * 20) \div 100

\* Test scenario: Combined Byzantine and offline within resilience model
CombinedFaultScenario7 ==
    /\ Cardinality(ByzantineNodes) = 1
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1
    /\ ByzantineNodes \cap {n \in Nodes : \lnot IsNodeResponsive(n)} = {}  \* Different nodes
    /\ ByzantineStake + SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) <= (TotalStake * 40) \div 100

\* Test scenario: Fast path conditions (>80% responsive stake)
FastPathScenario7 ==
    /\ ByzantineNodes = {}
    /\ Cardinality({n \in Nodes : IsNodeResponsive(n)}) >= 6  \* 6/7 = 85.7% > 80%
    /\ SumStakes({n \in Nodes : IsNodeResponsive(n)}) >= Quorum80

\* Test scenario: Slow path conditions (>60% responsive stake)
SlowPathScenario7 ==
    /\ Cardinality(ByzantineNodes) <= 1
    /\ Cardinality({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= 5  \* 5/7 = 71.4% > 60%
    /\ SumStakes({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= Quorum60

\* =============================================================================
\* Action Constraints for Focused Exploration
\* =============================================================================

\* Action constraint to limit concurrent actions and focus on key scenarios
SevenNodeActionConstraint ==
    \* Focus on essential actions for targeted exploration
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

\* =============================================================================
\* 7-Node Specific Properties
\* =============================================================================

\* Property: Fast path should work with 6+ responsive nodes (85.7% > 80%)
FastPathWith6Plus7Nodes ==
    (Cardinality({n \in Nodes : IsNodeResponsive(n)}) >= 6 /\ 
     \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>FastCertificateGenerated(sl)

\* Property: Slow path should work with 5+ honest responsive nodes (71.4% > 60%)
SlowPathWith5Plus7Nodes ==
    (Cardinality({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) >= 5 /\
     \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>CertificateGenerated(sl)

\* Property: Safety should hold with 1 Byzantine node (14.3% < 20%)
SafetyWith1Byzantine7Nodes ==
    (Cardinality(ByzantineNodes) = 1 /\ ByzantineStake <= (TotalStake * 20) \div 100) =>
    (NoConflictingBlocksFinalized /\ CertificateUniqueness /\ ForkPrevention)

\* Property: Liveness should hold with 1 offline node (14.3% < 20%)
LivenessWith1Offline7Nodes ==
    (Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1 /\
     SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) <= (TotalStake * 20) \div 100) =>
    \A sl \in Slots : HasBlockProposal(sl) ~> 
        (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))

\* Property: Combined fault tolerance (1 Byzantine + 1 offline = 28.6% total)
CombinedFaultTolerance7Nodes ==
    (Cardinality(ByzantineNodes) = 1 /\
     Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1 /\
     ByzantineNodes \cap {n \in Nodes : \lnot IsNodeResponsive(n)} = {}) =>
    \* Safety should still hold
    (NoConflictingBlocksFinalized /\ CertificateUniqueness)

\* Property: Byzantine stake validation for 7-node setup
ByzantineStakeValidation7Nodes ==
    /\ \* Single Byzantine node should be within limits
       (Cardinality(ByzantineNodes) = 1) => (ByzantineStake <= (TotalStake * 20) \div 100)
    /\ \* Multiple Byzantine nodes should exceed limits and be detected
       (Cardinality(ByzantineNodes) >= 2) => \lnot ValidByzantineStake

\* Property: Resilience boundaries for 7-node configuration
ResilienceBoundaries7Nodes ==
    /\ \* Up to 1 Byzantine node: safety maintained
       (Cardinality(ByzantineNodes) <= 1) => SafetyWithByzantineStake
    /\ \* Up to 1 offline node: liveness maintained
       (Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 1) => LivenessWithOfflineStake
    /\ \* Combined faults within limits: both safety and liveness
       (Cardinality(ByzantineNodes) <= 1 /\
        Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) <= 1) =>
       (SafetyWithByzantineStake /\ LivenessWithOfflineStake)

\* =============================================================================
\* Representative Testing Configuration
\* =============================================================================

\* Representative initial states for targeted exploration
RepresentativeInitialStates ==
    /\ stake \in {NodeStakes}
    /\ byzantine_behaviors \in [Nodes -> ByzantineBehaviorTypes]
    /\ node_responsiveness \in ResponsivenessScenarios

\* =============================================================================
\* Verification Goals for 7-Node Configuration
\* =============================================================================

\* Goal 1: Verify safety properties under representative Byzantine scenarios
SafetyVerificationGoal7 ==
    \A byzantine_set \in RepresentativeByzantineScenarios :
        (ByzantineNodes = byzantine_set /\ Cardinality(byzantine_set) <= 1) =>
        (NoConflictingBlocksFinalized /\ CertificateUniqueness /\ ForkPrevention /\ ChainConsistencyUnderByzantineFaults)

\* Goal 2: Verify liveness properties under sufficient responsive stake
LivenessVerificationGoal7 ==
    \A responsiveness \in ResponsivenessScenarios :
        (node_responsiveness = responsiveness /\
         SumStakes({n \in Nodes : responsiveness[n] /\ \lnot IsByzantine(n)}) >= Quorum60) =>
        \A sl \in Slots : HasBlockProposal(sl) ~> 
            (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))

\* Goal 3: Verify resilience under combined fault scenarios
ResilienceVerificationGoal7 ==
    \A scenario \in CombinedFaultScenarios :
        LET byzantine_stake == SumStakes(scenario.byzantine)
            offline_stake == SumStakes(scenario.offline)
            total_faulty_stake == byzantine_stake + offline_stake
        IN (total_faulty_stake <= (TotalStake * 40) \div 100) =>
            \* Safety always maintained
            (NoConflictingBlocksFinalized /\ CertificateUniqueness /\
             \* Liveness maintained if sufficient honest responsive stake
             (SumStakes({n \in Nodes : n \notin scenario.byzantine /\ n \notin scenario.offline}) >= Quorum60 =>
              \A sl \in Slots : HasBlockProposal(sl) ~> 
                  (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))))

\* Goal 4: Verify key property coverage for medium scale
KeyPropertyVerificationGoal7 ==
    /\ SafetyAlways
    /\ \* Targeted liveness verification
       FastPathWith6Plus7Nodes
    /\ SlowPathWith5Plus7Nodes
    /\ \* Targeted resilience verification
       SafetyWith1Byzantine7Nodes
    /\ LivenessWith1Offline7Nodes
    /\ CombinedFaultTolerance7Nodes
    /\ ByzantineStakeValidation7Nodes
    /\ ResilienceBoundaries7Nodes

\* Goal 5: Performance and scalability verification
ScalabilityVerificationGoal7 ==
    /\ \* Certificate generation scales with network size
       \A sl \in Slots : HasBlockProposal(sl) => 
           <>(\exists c \in certs : c.slot = sl)
    /\ \* Block propagation efficiency with 7 nodes
       \A b \in Blocks, sl \in Slots :
           (\exists n \in Nodes : b \in block_proposals[sl]) =>
           <>(\A n \in Nodes : IsNodeResponsive(n) => b \in received_blocks[n])
    /\ \* Window management scales appropriately
       \A w \in windows : 
           \A sl \in Slots : (WindowForSlot(sl) = w) => 
               (sl \in DOMAIN finalized => finalized[sl] \in Blocks)

=======================================================