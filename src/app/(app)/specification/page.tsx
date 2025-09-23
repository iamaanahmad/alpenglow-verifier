import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";

const tlaSpec = `---------------- MODULE AlpenglowMain ----------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Nodes, TotalStake, Quorum80, Quorum60

\* Represents the weight of each node
VARIABLE stake

\* Votor State
VARIABLE votes, finalized

\* Rotor State
VARIABLE block_proposals, received_blocks

\* Certificate State
VARIABLE certs

\* Leader and Slot State
VARIABLE leader, slot


vars == << stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot >>

Init ==
    /\ stake = [n \in Nodes |-> TotalStake / Cardinality(Nodes)]
    /\ votes = [sl \in Nat |-> [voter \in Nodes |-> {}]]
    /\ finalized = {}
    /\ block_proposals = [sl \in Nat |-> {}]
    /\ received_blocks = [n \in Nodes |-> {}]
    /\ certs = {}
    /\ leader = CHOOSE n \in Nodes : TRUE
    /\ slot = 1

\* --- Votor Logic ---
VotorVote(n, b, sl) ==
    /\ \lnot \exists b_v \in votes[sl][n] : b_v.slot = sl \* No double voting
    /\ votes' = [votes EXCEPT ![sl][n] = votes[sl][n] \cup {b}]

CanFinalize(b, sl, quorum) ==
    LET voters == {n \in Nodes : b \in votes[sl][n]}
    IN \sum_{n \in voters} stake[n] >= quorum

FinalizeBlock(b, sl) ==
    /\ \lnot(sl \in DOMAIN finalized)
    /\ \/ CanFinalize(b, sl, Quorum80)
       \/ CanFinalize(b, sl, Quorum60)
    /\ finalized' = [finalized EXCEPT ![sl] = b]


\* --- Rotor Logic ---
ProposeBlock(n, b, sl) ==
    /\ n = leader
    /\ \lnot \exists prop \in block_proposals[sl] : prop.origin = n
    /\ block_proposals' = [block_proposals EXCEPT ![sl] = block_proposals[sl] \cup {<<origin |-> n, block |-> b>>}]

\* Simplified erasure coding: nodes receive block if they are sampled
RelayBlock(sender, receiver, b, sl) ==
    /\ receiver \in Nodes
    /\ received_blocks' = [received_blocks EXCEPT ![receiver] = received_blocks[receiver] \cup {b}]


\* --- Certificate Logic ---
GenerateCertificate(sl, quorum) ==
    /\ \exists b \in DOMAIN block_proposals[sl]:
        /\ CanFinalize(b, sl, quorum)
        /\ \lnot \exists c \in certs : c.slot = sl
        /\ certs' = [certs EXCEPT ![sl] = {<<block |-> b, quorum |-> quorum>>}]


\* --- Leader and Timeout Logic ---
RotateLeader ==
    /\ \exists new_leader \in Nodes:
        /\ new_leader /= leader
        /\ leader' = new_leader
    /\ slot' = slot + 1

TimeoutSkip ==
    /\ \lnot CanFinalize(b, slot, Quorum60) \* Some condition for timeout
    /\ slot' = slot + 1
    /\ leader' = (leader + 1) % Cardinality(Nodes)


Next ==
    \/ \E n, b, sl: VotorVote(n, b, sl)
    \/ \E b, sl: FinalizeBlock(b, sl)
    \/ \E n, b, sl: ProposeBlock(n, b, sl)
    \/ \E s, r, b, sl: RelayBlock(s, r, b, sl)
    \/ \E sl, q: GenerateCertificate(sl, q)
    \/ RotateLeader
    \/ TimeoutSkip

Spec == Init /\ [][Next]_vars

=======================================================
`;

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
