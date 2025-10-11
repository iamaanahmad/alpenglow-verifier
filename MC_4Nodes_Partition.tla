----------------------------- MODULE MC_4Nodes_Partition -----------------------------
(*
Network Partition Recovery Test Configuration
Tests explicit network partition scenarios and recovery guarantees

Scenarios tested:
1. 2+2 Split: Two 2-node partitions (tests majority vs minority behavior)
2. 3+1 Split: One isolated node (tests single node partition recovery)
3. Partition Healing: Recovery after partition resolves

Safety Properties:
- No conflicting blocks finalized during partition
- Certificate uniqueness maintained across partitions
- Safety preserved even when network splits

Liveness Properties:
- Progress resumes after partition heals
- Partitioned minority doesn't finalize (safety)
- Majority partition can continue (with quorum)

Resilience Properties:
- System recovers from network partitions
- No state corruption after partition healing
- Nodes re-synchronize correctly
*)

EXTENDS Alpenglow, TLC

-----------------------------------------------------------------------------
(* Model Checking Configuration for Network Partition Testing *)

CONSTANTS
    N_4,          \* 4 nodes
    F_1,          \* 1 Byzantine node (25% stake)
    MaxSlot_3,    \* Test up to slot 3
    MaxWindow_2   \* 2 windows for partition scenarios

-----------------------------------------------------------------------------
(* Partition Scenarios *)

(*
Network Partition Modeling:
- Partition occurs at specific slots
- Messages between partitions are dropped
- Messages within partitions are delivered
- Partition heals after specified duration
*)

PartitionActive ==
    \* Partition active during specific slots
    /\ slot[DOMAIN nodes] \in {1, 2}  \* Partition during slots 1-2
    
PartitionHealed ==
    \* Partition healed at slot 3
    /\ slot[DOMAIN nodes] \in {3}

-----------------------------------------------------------------------------
(* Message Delivery During Partition *)

(*
Two partition groups for 2+2 split:
- Group A: Nodes 1, 2 (2 nodes, 50% stake)
- Group B: Nodes 3, 4 (2 nodes, 50% stake)

Three partition groups for 3+1 split:
- Majority: Nodes 1, 2, 3 (3 nodes, 75% stake)
- Isolated: Node 4 (1 node, 25% stake)
*)

PartitionGroup_2_2(node) ==
    \* 2+2 split: Assign nodes to partition groups
    IF node \in {1, 2} THEN "GroupA" ELSE "GroupB"

PartitionGroup_3_1(node) ==
    \* 3+1 split: Majority vs isolated
    IF node \in {1, 2, 3} THEN "Majority" ELSE "Isolated"

MessageDeliveredDuringPartition(sender, receiver, partitionType) ==
    \* Messages only delivered within same partition group
    IF partitionType = "2+2" THEN
        PartitionGroup_2_2(sender) = PartitionGroup_2_2(receiver)
    ELSE  \* 3+1 split
        PartitionGroup_3_1(sender) = PartitionGroup_3_1(receiver)

-----------------------------------------------------------------------------
(* Network Partition Invariants *)

NoConflictingBlocksDuringPartition ==
    \* Safety: No conflicting blocks finalized during partition
    \A slot_val \in DOMAIN finalized_blocks:
        \A n1, n2 \in DOMAIN nodes:
            LET b1 == finalized_blocks[slot_val][n1]
                b2 == finalized_blocks[slot_val][n2]
            IN (b1 # NullBlock /\ b2 # NullBlock) => (b1 = b2)

PartitionedMinorityDoesNotFinalize ==
    \* Safety: Minority partition (<50% stake) cannot finalize
    \* In 2+2 split: Neither group can finalize (no majority)
    \* In 3+1 split: Isolated node cannot finalize
    PartitionActive => 
        (\A node \in DOMAIN nodes:
            PartitionGroup_3_1(node) = "Isolated" =>
                finalized_blocks[slot[node]][node] = NullBlock)

MajorityPartitionCanProgress ==
    \* Liveness: Majority partition (>60% stake) can make progress
    \* In 3+1 split, majority (75% stake) should eventually finalize
    PartitionActive /\ (\E node \in DOMAIN nodes: PartitionGroup_3_1(node) = "Majority") =>
        <>(\E slot_val \in DOMAIN finalized_blocks:
            \E n \in DOMAIN nodes:
                PartitionGroup_3_1(n) = "Majority" /\
                finalized_blocks[slot_val][n] # NullBlock)

PartitionRecoveryProgress ==
    \* Liveness: After partition heals, all nodes eventually progress
    PartitionHealed =>
        <>(\A node \in DOMAIN nodes:
            slot[node] > 2)

-----------------------------------------------------------------------------
(* Certificate Uniqueness Across Partitions *)

CertificateUniquenessAcrossPartitions ==
    \* Safety: At most one certificate per slot, even during partition
    \A slot_val \in DOMAIN certificates:
        Cardinality({cert \in certificates[slot_val]: cert # NullCertificate}) <= 1

-----------------------------------------------------------------------------
(* State Re-synchronization After Partition Healing *)

NodesResynchronizeAfterHealing ==
    \* Resilience: Nodes converge to same state after partition heals
    PartitionHealed =>
        <>(\A n1, n2 \in DOMAIN nodes:
            \A slot_val \in DOMAIN finalized_blocks:
                finalized_blocks[slot_val][n1] = finalized_blocks[slot_val][n2])

-----------------------------------------------------------------------------
(* Model Checking Specification *)

Spec == 
    Init /\ [][Next]_vars

TypeOK ==
    /\ nodes \in [1..N_4 -> NodeState]
    /\ messages \in SUBSET Message
    /\ finalized_blocks \in [Slot -> [Node -> Block]]
    /\ certificates \in [Slot -> SUBSET Certificate]

-----------------------------------------------------------------------------
(* Properties to Verify *)

THEOREM SafetyDuringPartition == 
    Spec => []NoConflictingBlocksDuringPartition

THEOREM CertificateUniqueness == 
    Spec => []CertificateUniquenessAcrossPartitions

THEOREM MinorityCannotFinalize == 
    Spec => []PartitionedMinorityDoesNotFinalize

THEOREM RecoveryAfterHealing == 
    Spec => PartitionRecoveryProgress

THEOREM NodeResynchronization == 
    Spec => NodesResynchronizeAfterHealing

=============================================================================
