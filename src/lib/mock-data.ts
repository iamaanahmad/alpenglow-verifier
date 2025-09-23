
export type State = {
  [variable: string]: any;
};

export type CounterexampleStep = {
  step: number;
  action: string;
  state: State;
};

export type Counterexample = {
  id: string;
  violatedProperty: string;
  trace: CounterexampleStep[];
  tlaSpec: string;
};

export const mockCounterexample: Counterexample = {
  id: "violation-123",
  violatedProperty: "Safety: No two blocks finalized at the same slot.",
  tlaSpec: `
---- MODULE Alpenglow ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, QuorumSize

VARIABLES
    blockchain,
    votes,
    leader

Begin ==
    /\ blockchain = <<>>
    /\ votes = [n \in Nodes |-> {}]
    /\ leader = 0

Next ==
    \/ Propose(leader)
    \/ Vote(Nodes)
    \/ Finalize(leader)

Propose(p) ==
    /\ \exists b \in NewBlocks:
        /\ ...

Vote(n) ==
    /\ ...
====
  `,
  trace: [
    {
      step: 1,
      action: "Node 0 proposes Block A for slot 5",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "idle" },
          { id: 2, status: "idle" },
          { id: 3, status: "byzantine" },
        ],
        messages: [{ from: 0, to: 1, type: "PROPOSE" }, { from: 0, to: 2, type: "PROPOSE" }],
        finalizedBlocks: {},
      },
    },
    {
      step: 2,
      action: "Nodes 1 and 2 vote for Block A",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "voted", vote: "A" },
          { id: 2, status: "voted", vote: "A" },
          { id: 3, status: "byzantine" },
        ],
        messages: [{ from: 1, to: 0, type: "VOTE" }, { from: 2, to: 0, type: "VOTE" }],
        finalizedBlocks: {},
      },
    },
    {
      step: 3,
      action: "Byzantine node 3 equivocates, proposes Block B for slot 5 to node 2",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "voted", vote: "A" },
          { id: 2, status: "voted", vote: "A" },
          { id: 3, status: "byzantine" },
        ],
        messages: [{ from: 3, to: 2, type: "PROPOSE", block: "B" }],
        finalizedBlocks: {},
      },
    },
    {
      step: 4,
      action: "Node 0 finalizes Block A. Node 2 is tricked and also votes for Block B, leading to split brain.",
      state: {
        nodes: [
          { id: 0, status: "idle" },
          { id: 1, status: "voted", vote: "A" },
          { id: 2, status: "voted", vote: "B" },
          { id: 3, status: "byzantine" },
        ],
        messages: [{ from: 2, to: 3, type: "VOTE" }],
        finalizedBlocks: { "5": "A" },
      },
    },
    {
        step: 5,
        action: "Byzantine node 3 uses vote from node 2 to finalize Block B",
        state: {
          nodes: [
            { id: 0, status: "idle" },
            { id: 1, status: "idle" },
            { id: 2, status: "idle" },
            { id: 3, status: "byzantine" },
          ],
          messages: [],
          finalizedBlocks: { "5": ["A", "B"] }, // VIOLATION!
        },
    },
  ],
};
