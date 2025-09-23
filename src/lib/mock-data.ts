
export type NodeState = {
  id: number;
  status: 'idle' | 'proposing' | 'voted' | 'byzantine';
  [key: string]: any;
};

export type Message = {
  from: number;
  to: number;
  type: 'PROPOSE' | 'VOTE';
  [key: string]: any;
};

export type State = {
  nodes: NodeState[];
  messages: Message[];
  finalizedBlocks: { [slot: string]: any };
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
  violatedProperty: "NoConflictingBlocksFinalized",
  tlaSpec: `
---------------- MODULE AlpenglowMain ----------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Nodes, TotalStake, Quorum80, Quorum60

VARIABLES stake, votes, finalized, leader, slot

vars == << stake, votes, finalized, leader, slot >>

Init ==
    /\\ stake = [n \\in Nodes |-> TotalStake / Cardinality(Nodes)]
    /\\ votes = [sl \\in Nat |-> [voter \\in Nodes |-> {}]]
    /\\ finalized = {}
    /\\ leader = CHOOSE n \\in Nodes : TRUE
    /\\ slot = 1

VotorVote(n, b, sl) ==
    /\\ \\lnot \\exists b_v \\in votes[sl][n] : b_v.slot = sl
    /\\ votes' = [votes EXCEPT ![sl][n] = votes[sl][n] \\cup {b}]

CanFinalize(b, sl, quorum) ==
    LET voters == {n \\in Nodes : b \\in votes[sl][n]}
    IN \\sum_{n \\in voters} stake[n] >= quorum

FinalizeBlock(b, sl) ==
    /\\ \\lnot(sl \\in DOMAIN finalized)
    /\\ CanFinalize(b, sl, Quorum60)
    /\\ finalized' = [finalized EXCEPT ![sl] = b]

Next ==
    \\/ \\E n, b, sl: VotorVote(n, b, sl)
    \\/ \\E b, sl: FinalizeBlock(b, sl)

=======================================================
  `,
  trace: [
    {
      step: 1,
      action: "Node 0 (Leader) proposes Block A for slot 5.",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "idle" },
          { id: 2, status: "idle" },
          { id: 3, status: "byzantine" },
        ],
        messages: [
          { from: 0, to: 1, type: "PROPOSE", block: "A" },
          { from: 0, to: 2, type: "PROPOSE", block: "A" },
          { from: 0, to: 3, type: "PROPOSE", block: "A" }
        ],
        finalizedBlocks: {},
      },
    },
    {
      step: 2,
      action: "Honest nodes 1 and 2 receive Block A and vote for it.",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "voted", vote: "A" },
          { id: 2, status: "voted", vote: "A" },
          { id: 3, status: "byzantine" },
        ],
        messages: [
            { from: 1, to: 0, type: "VOTE" },
            { from: 2, to: 0, type: "VOTE" }
        ],
        finalizedBlocks: {},
      },
    },
    {
      step: 3,
      action: "Byzantine node 3 equivocates, proposing Block B for the same slot 5 to node 2, pretending to be a leader.",
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
      action: "Node 2 incorrectly processes the message from node 3 and changes its vote to Block B.",
      state: {
        nodes: [
          { id: 0, status: "proposing", block: "A" },
          { id: 1, status: "voted", vote: "A" },
          { id: 2, status: "voted", vote: "B" },
          { id: 3, status: "byzantine" },
        ],
        messages: [{ from: 2, to: 3, type: "VOTE" }],
        finalizedBlocks: {},
      },
    },
    {
        step: 5,
        action: "Node 0 has enough votes for Block A and finalizes it. At the same time, Byzantine node 3 has faked enough votes to finalize Block B.",
        state: {
          nodes: [
            { id: 0, status: "idle" },
            { id: 1, status: "idle" },
            { id: 2, status: "idle" },
            { id: 3, status: "byzantine" },
          ],
          messages: [],
          finalizedBlocks: { "5": ["A", "B"] }, // VIOLATION! Two blocks finalized in the same slot.
        },
    },
  ],
};
