
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs";

const specificationSections = {
  main: {
    title: "Main Specification & State",
    description: "The core variables, initialization, and next-state relation for the Alpenglow model.",
    code: `---------------- MODULE Alpenglow ----------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Nodes, TotalStake, Quorum80, Quorum60, MaxSlot, ByzantineNodes, WindowSize

VARIABLES 
    stake, votes, finalized, block_proposals, received_blocks, certs, 
    leader, slot, byzantine_behaviors, timeouts, skip_certs, 
    current_time, MaxTime, finalization_times, round_start_time,
    windows, window_bounds, current_window

vars == << stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, timeouts, skip_certs, current_time, finalization_times, round_start_time, windows, window_bounds, current_window >>

Init ==
    /\\ stake = [n \\in Nodes |-> IF n \\in ByzantineNodes THEN 20 ELSE 25]
    /\\ votes = [sl \\in 1..MaxSlot |-> [n \\in Nodes |-> {}]]
    /\\ finalized = [sl \\in {} |-> ""]
    /\\ block_proposals = [sl \\in 1..MaxSlot |-> {}]
    /\\ received_blocks = [n \\in Nodes |-> {}]
    /\\ certs = {}
    /\\ skip_certs = {}
    /\\ leader = CHOOSE n \\in Nodes : n \\notin ByzantineNodes
    /\\ slot = 1
    /\\ byzantine_behaviors = [n \\in ByzantineNodes |-> "normal"]
    /\\ timeouts = {}
    /\\ current_time = 0
    /\\ finalization_times = [sl \\in {} |-> 0]
    /\\ round_start_time = [sl \\in 1..MaxSlot |-> 0]
    /\\ windows = {1}
    /\\ current_window = 1
    /\\ window_bounds = [w \\in {1} |-> [start |-> 1, end |-> WindowSize]]

Next ==
    \\/ \\E n \\in Nodes, b \\in {"blockA", "blockB"}, sl \\in 1..MaxSlot: VotorVote(n, b, sl)
    \\/ \\E n \\in ByzantineNodes, b1, b2 \\in {"blockA", "blockB"}, sl \\in 1..MaxSlot: ByzantineDoubleVote(n, b1, b2, sl)
    \\/ \\E b \\in {"blockA", "blockB"}, sl \\in 1..MaxSlot: FinalizeBlock(b, sl)
    \\/ RotateLeader
    \\/ TimeoutSkip
`
  },
  votor: {
    title: "Votor (Dual-Path Consensus)",
    description: "Handles voting logic and block finalization based on fast-path (80% stake) or slow-path (60% stake) quorums.",
    code: `\* --- Votor Logic ---
VotorVote(n, b, sl) ==
    /\\ \\lnot(n \\in ByzantineNodes)
    /\\ votes[sl][n] = {}
    /\\ votes' = [votes EXCEPT ![sl][n] = {b}]
    /\\ UNCHANGED <<stake, finalized, certs, leader, slot, byzantine_behaviors, timeouts, skip_certs, current_time, finalization_times, round_start_time, windows, window_bounds, current_window>>

CanFinalize(b, sl, quorum) ==
    LET voters == {n \\in Nodes : b \\in votes[sl][n]}
    IN \\sum_{n \\in voters} stake[n] >= quorum

FinalizeBlock(b, sl) ==
    /\\ sl \\notin DOMAIN finalized
    /\\ \\/ CanFinalize(b, sl, Quorum80)
       \\/ CanFinalize(b, sl, Quorum60)
    /\\ finalized' = finalized @@ (sl :> b)
    /\\ finalization_times' = [finalization_times EXCEPT ![sl] = current_time]
    /\\ UNCHANGED <<stake, votes, certs, leader, slot, byzantine_behaviors, timeouts, skip_certs, current_time, round_start_time, windows, window_bounds, current_window>>
`
  },
  rotor: {
    title: "Rotor (Block Propagation)",
    description: "Models stake-weighted block proposal and relay logic. Erasure coding is abstracted to a simple relay action.",
    code: `\* --- Rotor Logic (Abstracted) ---
ProposeBlock(n, b, sl) ==
    /\\ n = leader
    /\\ \\lnot \\exists prop \\in block_proposals[sl] : prop.origin = n
    /\\ block_proposals' = [block_proposals EXCEPT ![sl] = block_proposals[sl] \\cup {<<origin |-> n, block |-> b>>}]
    /\\ UNCHANGED <<vars>>

\* Simplified erasure coding: nodes receive block if they are sampled.
RelayBlock(sender, receiver, b, sl) ==
    /\\ receiver \\in Nodes
    /\\ b \\in received_blocks[sender]
    /\\ received_blocks' = [received_blocks EXCEPT ![receiver] = received_blocks[receiver] \\cup {b}]
    /\\ UNCHANGED <<vars>>
`
  },
  certificates: {
    title: "Certificates & Timeouts",
    description: "Logic for generating certificates upon finalization, and handling timeouts with skip certificates to ensure liveness.",
    code: `\* --- Certificate & Timeout Logic ---
GenerateCertificate(sl, quorum) ==
    /\\ \\exists b \\in DOMAIN block_proposals[sl]:
        /\\ CanFinalize(b, sl, quorum)
        /\\ \\lnot \\exists c \\in certs : c.slot = sl
        /\\ certs' = [certs EXCEPT ![sl] = {<<block |-> b, quorum |-> quorum>>}]
        /\\ UNCHANGED <<vars>>

TimeoutSkip ==
    /\\ \\forall b \\in {"blockA", "blockB"}: \\lnot CanFinalize(b, slot, Quorum60)
    /\\ slot \\notin DOMAIN timeouts
    /\\ timeouts' = timeouts \\cup {slot}
    /\\ skip_certs' = skip_certs \\cup {[slot |-> slot, type |-> "skip"]}
    /\\ slot' = slot + 1
    /\\ leader' = CHOOSE n \\in Nodes: n /= leader
    /\\ UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, byzantine_behaviors, current_time, finalization_times, round_start_time, windows, window_bounds, current_window>>
`
  },
  byzantine: {
    title: "Byzantine Behavior",
    description: "Models malicious actions that Byzantine nodes can take, such as double-voting to try and break safety.",
    code: `\* --- Byzantine Logic ---
ByzantineDoubleVote(node, block1, block2, sl) ==
    /\\ node \\in ByzantineNodes
    /\\ sl <= MaxSlot
    /\\ block1 /= block2
    /\\ votes' = [votes EXCEPT ![sl][node] = {block1, block2}]
    /\\ byzantine_behaviors' = [byzantine_behaviors EXCEPT ![node] = "double_vote"]
    /\\ UNCHANGED <<stake, finalized, certs, leader, slot, timeouts, skip_certs, current_time, finalization_times, round_start_time, windows, window_bounds, current_window>>

\* Other Byzantine actions like withholding votes are modeled by them not taking an action.
`
  },
};

export default function SpecificationPage() {
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">TLA+ Specification</h1>
        <p className="text-muted-foreground">
          The formal model of the Alpenglow consensus protocol, broken down by its core components.
        </p>
      </div>

      <Tabs defaultValue="main" className="w-full">
        <TabsList className="grid w-full grid-cols-2 md:grid-cols-5">
          <TabsTrigger value="main">Main</TabsTrigger>
          <TabsTrigger value="votor">Votor</TabsTrigger>
          <TabsTrigger value="rotor">Rotor</TabsTrigger>
          <TabsTrigger value="certificates">Certificates</TabsTrigger>
          <TabsTrigger value="byzantine">Byzantine</TabsTrigger>
        </TabsList>
        {Object.entries(specificationSections).map(([key, section]) => (
          <TabsContent key={key} value={key}>
            <Card>
              <CardHeader>
                <CardTitle>{section.title}</CardTitle>
                <CardDescription>{section.description}</CardDescription>
              </CardHeader>
              <CardContent>
                <CodeBlock code={section.code} language="tlaplus" />
              </CardContent>
            </Card>
          </TabsContent>
        ))}
      </Tabs>
    </div>
  );
}
