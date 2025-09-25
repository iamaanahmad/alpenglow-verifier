---------------- MODULE MC_4Nodes ----------------

EXTENDS Alpenglow, Properties

\* 4-node test configuration for exhaustive state exploration
\* This configuration tests all Byzantine combinations and complete property verification

\* =============================================================================
\* 4-Node Specific Constants and Constraints
\* =============================================================================

\* Node stake distribution for 4-node setup (equal stakes for simplicity)
\* Note: Nodes are defined in the .cfg file as {n1, n2, n3, n4}
NodeStakes == [n \in Nodes |-> TotalStake \div Cardinality(Nodes)]

\* Byzantine node combinations for exhaustive testing
\* Test all possible Byzantine combinations up to 20% stake (1 node = 25% > 20%, so max 0 Byzantine for safety)
\* But we'll test edge cases including 1 Byzantine node to verify safety violations are caught
ByzantineNodeCombinations == 
    LET single_node_sets == {{n} : n \in Nodes}
    IN {{}  \* No Byzantine nodes (honest case)
       } \cup single_node_sets  \* Single Byzantine node combinations (exceeds 20% limit)

\* Network responsiveness combinations for testing offline scenarios
ResponsivenessCombinations == 
    LET all_responsive == [n \in Nodes |-> TRUE]
        single_offline_sets == {[n \in Nodes |-> IF n = offline_node THEN FALSE ELSE TRUE] : offline_node \in Nodes}
    IN {all_responsive} \cup single_offline_sets

\* =============================================================================
\* State Constraints for Exhaustive Exploration
\* =============================================================================

\* Enhanced state constraint for 4-node exhaustive testing
\* We inherit the basic StateConstraint from Alpenglow and add 4-node specific constraints
FourNodeStateConstraint ==
    /\ StateConstraint  \* Basic constraint from Alpenglow
    /\ current_time <= MaxTime
    /\ Cardinality(DOMAIN finalized) <= MaxSlot
    /\ Cardinality(certs) <= MaxSlot * 2  \* Allow multiple certificate attempts per slot
    /\ Cardinality(skip_certs) <= MaxSlot
    /\ Cardinality(timeouts) <= MaxSlot
    /\ \A sl \in Slots : Cardinality(block_proposals[sl]) <= Cardinality(Nodes)
    /\ \A n \in Nodes : Cardinality(received_blocks[n]) <= Cardinality(Blocks)
    /\ current_window <= MaxWindow

\* =============================================================================
\* 4-Node Specific Test Scenarios
\* =============================================================================

\* Test scenario: All nodes honest and responsive (baseline)
AllHonestResponsiveScenario ==
    /\ ByzantineNodes = {}
    /\ \A n \in Nodes : IsNodeResponsive(n)
    /\ ValidByzantineStake

\* Test scenario: Maximum allowed Byzantine stake (should fail with 1 node = 25%)
MaxByzantineScenario ==
    /\ Cardinality(ByzantineNodes) = 1
    /\ ByzantineStake = 25  \* This exceeds 20% limit and should be caught

\* Test scenario: Maximum allowed offline stake (should fail with 1 node = 25%)
MaxOfflineScenario ==
    /\ ByzantineNodes = {}
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1
    /\ SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)}) = 25  \* Exceeds 20% limit

\* Test scenario: Combined Byzantine and offline (should definitely fail)
CombinedFaultScenario ==
    /\ Cardinality(ByzantineNodes) = 1
    /\ Cardinality({n \in Nodes : \lnot IsNodeResponsive(n)}) = 1
    /\ ByzantineNodes \cap {n \in Nodes : \lnot IsNodeResponsive(n)} = {}  \* Different nodes

\* =============================================================================
\* 4-Node Specific Properties
\* =============================================================================

\* Property: Fast path should work with 4 honest responsive nodes (100% > 80%)
FastPathWith4Nodes ==
    (AllHonestResponsiveScenario /\ \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>FastCertificateGenerated(sl)

\* Property: Slow path should work with 3 honest responsive nodes (75% > 60%)
SlowPathWith3Nodes ==
    (/\ Cardinality({n \in Nodes : IsNodeResponsive(n) /\ \lnot IsByzantine(n)}) = 3
     /\ \A sl \in Slots : HasBlockProposal(sl)) =>
    \A sl \in Slots : <>CertificateGenerated(sl)

\* Property: Safety should hold even with 1 Byzantine node (though it exceeds 20% limit)
SafetyWith1Byzantine ==
    (Cardinality(ByzantineNodes) = 1) =>
    (NoConflictingBlocksFinalized /\ CertificateUniqueness)

\* Property: System should detect when Byzantine stake exceeds limits
ByzantineStakeViolationDetection ==
    (Cardinality(ByzantineNodes) >= 1) => \lnot ValidByzantineStake

\* =============================================================================
\* Exhaustive Testing Configuration
\* =============================================================================

\* All possible initial states for exhaustive exploration
ExhaustiveInitialStates ==
    /\ stake \in {NodeStakes}
    /\ byzantine_behaviors \in [Nodes -> ByzantineBehaviorTypes]
    /\ node_responsiveness \in ResponsivenessCombinations

\* =============================================================================
\* Model Checking Directives
\* =============================================================================

\* Symmetry reduction would be handled by TLC configuration if needed
\* For exhaustive 4-node testing, we explore all states without symmetry reduction

\* Action constraints for focused exploration
ActionConstraint ==
    /\ \* Limit concurrent actions to reduce state explosion
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
\* Verification Goals for 4-Node Configuration
\* =============================================================================

\* Goal 1: Verify all safety properties hold under all Byzantine combinations
SafetyVerificationGoal ==
    \A byzantine_set \in ByzantineNodeCombinations :
        (ByzantineNodes = byzantine_set) =>
        (NoConflictingBlocksFinalized /\ CertificateUniqueness /\ ForkPrevention)

\* Goal 2: Verify liveness properties under sufficient honest responsive stake
LivenessVerificationGoal ==
    \A responsiveness \in ResponsivenessCombinations :
        (node_responsiveness = responsiveness /\
         SumStakes({n \in Nodes : responsiveness[n] /\ \lnot IsByzantine(n)}) >= 60) =>
        \A sl \in Slots : HasBlockProposal(sl) ~> (sl \in DOMAIN finalized \/ HasSkipCertificate(sl))

\* Goal 3: Verify resilience boundaries are correctly enforced
ResilienceVerificationGoal ==
    /\ \* Byzantine stake > 20% should be detected
       (ByzantineStake > 20) => \lnot ValidByzantineStake
    /\ \* Offline stake > 20% should affect liveness but not safety
       LET offline_stake == SumStakes({n \in Nodes : \lnot IsNodeResponsive(n)})
       IN (offline_stake > 20) => 
           (NoConflictingBlocksFinalized /\ CertificateUniqueness)

\* Goal 4: Verify complete property coverage
CompletePropertyVerificationGoal ==
    /\ SafetyAlways
    /\ LivenessAlways  
    /\ ResilienceAlways

=======================================================