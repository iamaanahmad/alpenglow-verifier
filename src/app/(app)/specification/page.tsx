import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";

const tlaSpec = `---------------- MODULE Alpenglow ----------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Nodes,      \* The set of all nodes, e.g., {n1, n2, n3, n4}
    Quorum80,   \* Stake threshold for the fast 80% path
    Quorum60    \* Stake threshold for the conservative 60% path

VARIABLES
    leader,     \* The current leader
    slot,       \* The current slot number
    blocks,     \* A function mapping slots to proposed blocks
    certs,      \* A set of generated certificates
    chain       \* The finalized blockchain (a sequence of blocks)
    
\* Define the types of variables.
TypeOK ==
    /\ leader \in Nodes
    /\ slot \in Nat
    /\ blocks \in [Slots -> SUBSET Blocks]
    /\ certs \in SUBSET Certificates
    /\ chain \in Seq(Blocks)
    
Init ==
    /\ leader = CHOOSE n \in Nodes : TRUE
    /\ slot = 1
    /\ blocks = [s \in {} |-> {}]
    /\ certs = {}
    /\ chain = <<>>

Next ==
    \/ RotateLeader
    \/ ProposeBlock
    \/ AggregateCertificates
    \/ FinalizeBlock
    
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
