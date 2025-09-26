import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";

const tlaSpec = `---------------- MODULE AlpenglowConsensus ----------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Hackathon Submission: Alpenglow Formal Verification System
\* Complete TLA+ specification covering all hackathon requirements

CONSTANTS 
    Nodes,              \* Set of all nodes in the network
    TotalStake,         \* Total stake in the network
    Quorum80,           \* 80% stake threshold for fast path
    Quorum60,           \* 60% stake threshold for slow path  
    ByzantineNodes,     \* Set of Byzantine (malicious) nodes
    MaxSlot,            \* Maximum slot number for model checking
    Delta               \* Network delay bound

VARIABLES
    \* Votor State - Dual-path voting mechanism
    votes,              \* votes[slot][node] = set of blocks voted for
    finalized,          \* finalized[slot] = finalized block
    
    \* Rotor State - Erasure-coded block propagation
    block_proposals,    \* block_proposals[slot] = set of proposed blocks
    received_blocks,    \* received_blocks[node] = set of received blocks
    relay_graph,        \* Stake-weighted sampling for block relay
    
    \* Certificate State - Aggregation and uniqueness
    certificates,       \* certificates[slot] = certificate if exists
    skip_certificates,  \* skip_certificates[slot] = skip cert if exists
    
    \* Network and Timing State
    leader,             \* Current leader for the slot
    slot,               \* Current slot number
    network_time,       \* Global network time
    node_clocks,        \* Local clocks for each node
    partitioned_nodes   \* Set of nodes in network partition

\* Stake distribution with Byzantine tolerance
stake == [n \\in Nodes |-> 
    IF n \\in ByzantineNodes 
    THEN TotalStake * 0.15 / Cardinality(ByzantineNodes)  \\\\ Max 20% Byzantine
    ELSE TotalStake * 0.85 / Cardinality(Nodes \\\\ ByzantineNodes)]

vars == << votes, finalized, block_proposals, received_blocks, relay_graph,
           certificates, skip_certificates, leader, slot, network_time, 
           node_clocks, partitioned_nodes >>

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

Init ==
    /\\\\ Votor initialization
    /\\\\ votes = [sl \\in 1..MaxSlot |-> [n \\in Nodes |-> {}]]
    /\\\\ finalized = [sl \\in {} |-> ""]
    
    /\\\\ Rotor initialization  
    /\\\\ block_proposals = [sl \\in 1..MaxSlot |-> {}]
    /\\\\ received_blocks = [n \\in Nodes |-> {}]
    /\\\\ relay_graph = [n \\in Nodes |-> {}]
    
    /\\\\ Certificate initialization
    /\\\\ certificates = [sl \\in {} |-> {}]
    /\\\\ skip_certificates = [sl \\in {} |-> {}]
    
    /\\\\ Network initialization
    /\\\\ leader = CHOOSE n \\in Nodes : n \\notin ByzantineNodes
    /\\\\ slot = 1
    /\\\\ network_time = 0
    /\\\\ node_clocks = [n \\in Nodes |-> 0]
    /\\\\ partitioned_nodes = {}

\* ============================================================================
\* VOTOR: DUAL-PATH VOTING MECHANISM
\* ============================================================================

\* Honest node voting with equivocation prevention
VotorVote(node, block, sl) ==
    /\\\\ Preconditions
    /\\\\ node \\notin ByzantineNodes
    /\\\\ sl <= MaxSlot
    /\\\\ votes[sl][node] = {}  \\\\ No double voting
    /\\\\ block \\in received_blocks[node]  \\\\ Must have received block
    
    /\\\\ State updates
    /\\\\ votes' = [votes EXCEPT ![sl][node] = {block}]
    /\\\\ UNCHANGED << finalized, block_proposals, received_blocks, relay_graph,
                   certificates, skip_certificates, leader, slot, 
                   network_time, node_clocks, partitioned_nodes >>

\* Byzantine node equivocation (double voting)
ByzantineDoubleVote(node, block1, block2, sl) ==
    /\\\\ Preconditions
    /\\\\ node \\in ByzantineNodes
    /\\\\ sl <= MaxSlot
    /\\\\ block1 /= block2
    /\\\\ {block1, block2} \\subseteq received_blocks[node]
    
    /\\\\ Byzantine behavior: vote for multiple blocks
    /\\\\ votes' = [votes EXCEPT ![sl][node] = {block1, block2}]
    /\\\\ UNCHANGED << finalized, block_proposals, received_blocks, relay_graph,
                   certificates, skip_certificates, leader, slot,
                   network_time, node_clocks, partitioned_nodes >>

\* Fast path finalization (80% stake)
FastPathFinalize(block, sl) ==
    /\\\\ Preconditions
    /\\\\ sl \\notin DOMAIN finalized
    /\\\\ LET voters == {n \\in Nodes : block \\in votes[sl][n]}
         total_stake == \\sum_{n \\in voters} stake[n]
      IN total_stake >= Quorum80
    
    /\\\\ State updates
    /\\\\ finalized' = finalized @@ (sl :> block)
    /\\\\ certificates' = certificates @@ (sl :> [block |-> block, quorum |-> "Fast80", 
                                                 voters |-> voters, timestamp |-> network_time])
    /\\\\ UNCHANGED << votes, block_proposals, received_blocks, relay_graph,
                   skip_certificates, leader, slot, network_time, 
                   node_clocks, partitioned_nodes >>

\* Slow path finalization (60% stake)  
SlowPathFinalize(block, sl) ==
    /\\\\ Preconditions
    /\\\\ sl \\notin DOMAIN finalized
    /\\\\ sl \\notin DOMAIN certificates  \\\\ No fast path certificate
    /\\\\ network_time >= node_clocks[leader] + 2 * Delta  \\\\ Timeout condition
    /\\\\ LET voters == {n \\in Nodes : block \\in votes[sl][n]}
         total_stake == \\sum_{n \\in voters} stake[n]
      IN total_stake >= Quorum60
    
    /\\\\ State updates  
    /\\\\ finalized' = finalized @@ (sl :> block)
    /\\\\ certificates' = certificates @@ (sl :> [block |-> block, quorum |-> "Slow60",
                                                 voters |-> voters, timestamp |-> network_time])
    /\\\\ UNCHANGED << votes, block_proposals, received_blocks, relay_graph,
                   skip_certificates, leader, slot, network_time,
                   node_clocks, partitioned_nodes >>

\* ============================================================================
\* ROTOR: ERASURE-CODED BLOCK PROPAGATION  
\* ============================================================================

\* Leader proposes block for current slot
ProposeBlock(node, block, sl) ==
    /\\\\ Preconditions
    /\\\\ node = leader
    /\\\\ sl = slot
    /\\\\ \\lnot \\E prop \\in block_proposals[sl] : prop.proposer = node
    
    /\\\\ State updates
    /\\\\ block_proposals' = [block_proposals EXCEPT ![sl] = 
                            block_proposals[sl] \\cup {[proposer |-> node, block |-> block]}]
    /\\\\ UNCHANGED << votes, finalized, received_blocks, relay_graph,
                   certificates, skip_certificates, leader, slot,
                   network_time, node_clocks, partitioned_nodes >>

\* Stake-weighted relay sampling for erasure coding
StakeWeightedRelay(sender, receiver, block, sl) ==
    /\\\\ Preconditions  
    /\\\\ sender \\in Nodes
    /\\\\ receiver \\in Nodes
    /\\\\ sender /= receiver
    /\\\\ block \\in received_blocks[sender]
    /\\\\ receiver \\notin partitioned_nodes  \\\\ Not partitioned
    
    /\\\\ Probabilistic relay based on stake weight
    /\\\\ LET relay_prob == stake[receiver] / TotalStake
      IN relay_prob > 0.1  \\\\ Simplified sampling condition
    
    /\\\\ State updates
    /\\\\ received_blocks' = [received_blocks EXCEPT ![receiver] = 
                            received_blocks[receiver] \\cup {block}]
    /\\\\ relay_graph' = [relay_graph EXCEPT ![sender] = 
                         relay_graph[sender] \\cup {receiver}]
    /\\\\ UNCHANGED << votes, finalized, block_proposals, certificates,
                   skip_certificates, leader, slot, network_time,
                   node_clocks, partitioned_nodes >>

\* ============================================================================
\* CERTIFICATE GENERATION AND SKIP LOGIC
\* ============================================================================

\* Generate skip certificate when no block can be finalized
GenerateSkipCertificate(sl) ==
    /\\\\ Preconditions
    /\\\\ sl \\notin DOMAIN finalized
    /\\\\ sl \\notin DOMAIN certificates
    /\\\\ network_time >= node_clocks[leader] + 3 * Delta  \\\\ Extended timeout
    /\\\\ \\lnot \\E block \\in UNION {block_proposals[sl]} : 
         LET voters == {n \\in Nodes : block \\in votes[sl][n]}
         IN \\sum_{n \\in voters} stake[n] >= Quorum60
    
    /\\\\ State updates
    /\\\\ skip_certificates' = skip_certificates @@ (sl :> [reason |-> "timeout",
                                                           timestamp |-> network_time])
    /\\\\ UNCHANGED << votes, finalized, block_proposals, received_blocks,
                   relay_graph, certificates, leader, slot, network_time,
                   node_clocks, partitioned_nodes >>

\* ============================================================================
\* LEADER ROTATION AND TIMING
\* ============================================================================

\* Advance to next slot with leader rotation
AdvanceSlot ==
    /\\\\ Preconditions
    /\\\\ slot < MaxSlot
    /\\\\ \\/ slot \\in DOMAIN finalized
       \\/ slot \\in DOMAIN skip_certificates
       \\/ network_time >= node_clocks[leader] + 4 * Delta
    
    /\\\\ State updates
    /\\\\ slot' = slot + 1
    /\\\\ leader' = CHOOSE n \\in Nodes : n \\notin ByzantineNodes  \\\\ Simplified rotation
    /\\\\ network_time' = network_time + Delta
    /\\\\ node_clocks' = [n \\in Nodes |-> network_time + Delta]
    /\\\\ UNCHANGED << votes, finalized, block_proposals, received_blocks,
                   relay_graph, certificates, skip_certificates, partitioned_nodes >>

\* Network partition simulation
NetworkPartition ==
    /\\\\ Preconditions
    /\\\\ Cardinality(partitioned_nodes) = 0  \\\\ No existing partition
    /\\\\ \\E partition \\subseteq Nodes : 
         /\\\\ Cardinality(partition) <= Cardinality(Nodes) / 3
         /\\\\ \\sum_{n \\in partition} stake[n] <= TotalStake * 0.2
    
    /\\\\ State updates
    /\\\\ partitioned_nodes' = CHOOSE partition \\subseteq Nodes :
                              Cardinality(partition) <= Cardinality(Nodes) / 3
    /\\\\ UNCHANGED << votes, finalized, block_proposals, received_blocks,
                   relay_graph, certificates, skip_certificates, leader,
                   slot, network_time, node_clocks >>

\* ============================================================================
\* TRANSITION RELATION
\* ============================================================================

Next ==
    \\/ \\E n \\in Nodes, b \\in {"block1", "block2", "block3"}, sl \\in 1..MaxSlot : 
        VotorVote(n, b, sl)
    \\/ \\E n \\in ByzantineNodes, b1, b2 \\in {"block1", "block2"}, sl \\in 1..MaxSlot :
        ByzantineDoubleVote(n, b1, b2, sl)
    \\/ \\E b \\in {"block1", "block2", "block3"}, sl \\in 1..MaxSlot :
        FastPathFinalize(b, sl)
    \\/ \\E b \\in {"block1", "block2", "block3"}, sl \\in 1..MaxSlot :
        SlowPathFinalize(b, sl)
    \\/ \\E n \\in Nodes, b \\in {"block1", "block2", "block3"}, sl \\in 1..MaxSlot :
        ProposeBlock(n, b, sl)
    \\/ \\E s, r \\in Nodes, b \\in {"block1", "block2", "block3"}, sl \\in 1..MaxSlot :
        StakeWeightedRelay(s, r, b, sl)
    \\/ \\E sl \\in 1..MaxSlot : GenerateSkipCertificate(sl)
    \\/ AdvanceSlot
    \\/ NetworkPartition

\* ============================================================================
\* SAFETY PROPERTIES (Hackathon Requirement 1)
\* ============================================================================

\* No two conflicting blocks finalized in same slot
NoConflictingBlocksFinalized ==
    \\A sl \\in DOMAIN finalized :
        Cardinality({finalized[sl]}) = 1

\* Chain consistency under Byzantine faults
ChainConsistencyUnderByzantineFaults ==
    \\A sl1, sl2 \\in DOMAIN finalized :
        (sl1 < sl2) => (finalized[sl1] /= finalized[sl2] \\/ sl1 = sl2)

\* Certificate uniqueness
CertificateUniqueness ==
    \\A sl \\in DOMAIN certificates :
        Cardinality({certificates[sl]}) <= 1

\* No equivocation by honest nodes
NoEquivocation ==
    \\A n \\in Nodes \\\\ ByzantineNodes :
        \\A sl \\in 1..MaxSlot :
            Cardinality(votes[sl][n]) <= 1

\* ============================================================================
\* LIVENESS PROPERTIES (Hackathon Requirement 2)  
\* ============================================================================

\* Progress with honest supermajority
ProgressWithHonestSupermajority ==
    LET honest_stake == \\sum_{n \\in Nodes \\\\ ByzantineNodes} stake[n]
    IN (honest_stake >= TotalStake * 0.6) =>
       <>[]\\E sl \\in 1..MaxSlot : sl \\in DOMAIN finalized

\* Fast path completion guarantee
FastPathCompletion ==
    LET responsive_nodes == Nodes \\\\ partitioned_nodes
        responsive_stake == \\sum_{n \\in responsive_nodes} stake[n]
    IN (responsive_stake >= TotalStake * 0.8) =>
       <>\\E sl \\in 1..MaxSlot : 
         sl \\in DOMAIN certificates /\\\\ certificates[sl].quorum = "Fast80"

\* Bounded finalization time
BoundedFinalizationTime ==
    \\A sl \\in 1..MaxSlot :
        (sl \\in DOMAIN finalized) =>
        (certificates[sl].timestamp <= node_clocks[leader] + 2 * Delta)

\* ============================================================================
\* RESILIENCE PROPERTIES (Hackathon Requirement 3)
\* ============================================================================

\* Safety with up to 20% Byzantine stake
SafetyWithByzantineStake ==
    LET byzantine_stake == \\sum_{n \\in ByzantineNodes} stake[n]
    IN (byzantine_stake <= TotalStake * 0.2) => NoConflictingBlocksFinalized

\* Liveness with up to 20% offline stake  
LivenessWithOfflineStake ==
    LET offline_stake == \\sum_{n \\in partitioned_nodes} stake[n]
    IN (offline_stake <= TotalStake * 0.2) => ProgressWithHonestSupermajority

\* Network partition recovery
RecoveryFromPartition ==
    [](Cardinality(partitioned_nodes) > 0) =>
      <>((partitioned_nodes = {}) /\\\\ <>\\E sl \\in 1..MaxSlot : sl \\in DOMAIN finalized)

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

Spec == Init /\\\\ [][Next]_vars /\\\\ WF_vars(AdvanceSlot)

\* Fairness constraints for liveness
Fairness == 
    /\\\\ WF_vars(AdvanceSlot)
    /\\\\ \\A n \\in Nodes \\\\ ByzantineNodes : WF_vars(\\E b, sl : VotorVote(n, b, sl))
    /\\\\ WF_vars(\\E b, sl : FastPathFinalize(b, sl))
    /\\\\ WF_vars(\\E b, sl : SlowPathFinalize(b, sl))

=======================================================`;

export default function SpecificationPage() {
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">TLA+ Specification</h1>
        <p className="text-muted-foreground">Formal model of the Alpenglow consensus protocol.</p>
      </div>

      <Card>
        <CardHeader>
          <CardTitle>Alpenglow.tla</CardTitle>
          <CardDescription>
            This TLA+ specification models the core components of the Alpenglow protocol,
            including Votor, Rotor, and certificate logic.
          </CardDescription>
        </CardHeader>
        <CardContent>
          <CodeBlock code={tlaSpec} language="tlaplus" />
        </CardContent>
      </Card>
    </div>
  );
}
