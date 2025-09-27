---------------- MODULE MC_Simple_Byzantine_Test ----------------

EXTENDS Alpenglow, Properties

\* Simple test to verify Byzantine double voting fix
SimpleInit ==
    /\ stake = [n1 |-> 25, n2 |-> 25, n3 |-> 30, n4 |-> 20]
    /\ votes = [sl \in 1..MaxSlot |-> [n \in Nodes |-> {}]]
    /\ finalized = <<>>
    /\ block_proposals = [sl \in 1..MaxSlot |-> {}]
    /\ received_blocks = [n \in Nodes |-> {"block1", "block2"}]
    /\ certs = {}
    /\ leader = "n1"
    /\ slot = 1
    /\ byzantine_behaviors = [n \in Nodes |-> IF n \in ByzantineNodes THEN "double_vote" ELSE "normal"]
    /\ relay_graph = [n \in Nodes |-> {}]
    /\ network_topology = [<<n1, n2>> \in Nodes \X Nodes |-> NetworkDelay]
    /\ timeouts = {}
    /\ skip_certs = {}
    /\ slot_start_time = [sl \in 1..MaxSlot |-> 0]
    /\ current_time = 0
    /\ round_start_time = [sl \in 1..MaxSlot |-> 0]
    /\ node_responsiveness = [n \in Nodes |-> TRUE]
    /\ network_delays = [<<n1, n2>> \in Nodes \X Nodes |-> NetworkDelay]
    /\ partial_sync_violations = {}
    /\ finalization_times = <<>>
    /\ windows = {1}
    /\ window_bounds = [w \in {1} |-> [start |-> 1, end |-> MaxSlot]]
    /\ current_window = 1
    /\ monte_carlo_samples = {}
    /\ confidence_intervals = <<>>
    /\ sampling_history = {}
    /\ property_verification_stats = <<>>

\* Test Byzantine double voting
SimpleByzantineDoubleVote ==
    /\ slot = 1
    /\ "n4" \in ByzantineNodes
    /\ votes' = [votes EXCEPT ![1]["n4"] = {"block1", "block2"}]
    /\ UNCHANGED <<stake, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>

\* Test honest voting
SimpleHonestVote ==
    /\ slot = 1
    /\ \E n \in Nodes \ ByzantineNodes:
        /\ \E b \in {"block1", "block2"}:
            /\ votes[1][n] = {}
            /\ votes' = [votes EXCEPT ![1][n] = {b}]
    /\ UNCHANGED <<stake, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>

SimpleNext ==
    \/ SimpleByzantineDoubleVote
    \/ SimpleHonestVote

SimpleSpec == SimpleInit /\ [][SimpleNext]_vars

\* Test that Byzantine double voting cannot cause finalization
TestByzantineCannotFinalize ==
    \A sl \in 1..MaxSlot:
        \A b \in {"block1", "block2"}:
            LET honest_voters == {n \in Nodes \ ByzantineNodes : b \in votes[sl][n]}
                honest_stake == SumStakes(honest_voters)
            IN (honest_stake < Quorum60) => \lnot CanFinalize(b, sl, Quorum60)

====