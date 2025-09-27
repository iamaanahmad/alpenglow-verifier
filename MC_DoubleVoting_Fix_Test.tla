---------------- MODULE MC_DoubleVoting_Fix_Test ----------------

EXTENDS Alpenglow, Properties

\* Test configuration for Byzantine double voting fix
CONSTANTS 
    TestNodes, TestTotalStake, TestQuorum80, TestQuorum60, TestMaxSlot, 
    TestByzantineNodes, TestByzantineStakeRatio, TestErasureCodingFactor, 
    TestNetworkDelay, TestSlotTimeout, TestMaxTime, TestWindowSize,
    TestDelta80, TestDelta60, TestMaxNetworkDelay, TestMinNetworkDelay, 
    TestPartialSynchronyBound, TestRoundTimeout, TestFastPathTimeout, 
    TestSlowPathTimeout, TestOptimizationLevel, TestMonteCarloSamples, 
    TestConfidenceLevel, TestSamplingStrategy, TestPropertyComplexityThreshold

\* Override constants for focused testing
ASSUME TestNodes = {"n1", "n2", "n3", "n4"}
ASSUME TestTotalStake = 100
ASSUME TestQuorum80 = 80
ASSUME TestQuorum60 = 60
ASSUME TestMaxSlot = 2
ASSUME TestByzantineNodes = {"n4"}
ASSUME TestByzantineStakeRatio = 20
ASSUME TestErasureCodingFactor = 50
ASSUME TestNetworkDelay = 1
ASSUME TestSlotTimeout = 10
ASSUME TestMaxTime = 50
ASSUME TestWindowSize = 5
ASSUME TestDelta80 = 5
ASSUME TestDelta60 = 8
ASSUME TestMaxNetworkDelay = 3
ASSUME TestMinNetworkDelay = 1
ASSUME TestPartialSynchronyBound = 5
ASSUME TestRoundTimeout = 10
ASSUME TestFastPathTimeout = 5
ASSUME TestSlowPathTimeout = 15
ASSUME TestOptimizationLevel = 1
ASSUME TestMonteCarloSamples = 100
ASSUME TestConfidenceLevel = 95
ASSUME TestSamplingStrategy = "uniform"
ASSUME TestPropertyComplexityThreshold = 5

\* Test initial state with Byzantine double voting scenario
TestInit ==
    /\ stake = [n1 |-> 25, n2 |-> 25, n3 |-> 30, n4 |-> 20]
    /\ votes = [sl \in 1..TestMaxSlot |-> [n \in TestNodes |-> {}]]
    /\ finalized = <<>>
    /\ block_proposals = [sl \in 1..TestMaxSlot |-> {}]
    /\ received_blocks = [n \in TestNodes |-> {"block1", "block2"}]
    /\ certs = {}
    /\ leader = "n1"
    /\ slot = 1
    /\ byzantine_behaviors = [n \in TestNodes |-> IF n \in TestByzantineNodes THEN "double_vote" ELSE "normal"]
    /\ relay_graph = [n \in TestNodes |-> {}]
    /\ network_topology = [<<n1, n2>> \in TestNodes \X TestNodes |-> TestNetworkDelay]
    /\ timeouts = {}
    /\ skip_certs = {}
    /\ slot_start_time = [sl \in 1..TestMaxSlot |-> 0]
    /\ current_time = 0
    /\ round_start_time = [sl \in 1..TestMaxSlot |-> 0]
    /\ node_responsiveness = [n \in TestNodes |-> TRUE]
    /\ network_delays = [<<n1, n2>> \in TestNodes \X TestNodes |-> TestNetworkDelay]
    /\ partial_sync_violations = {}
    /\ finalization_times = <<>>
    /\ windows = {1}
    /\ window_bounds = [w \in {1} |-> [start |-> 1, end |-> TestMaxSlot]]
    /\ current_window = 1
    /\ monte_carlo_samples = {}
    /\ confidence_intervals = <<>>
    /\ sampling_history = {}
    /\ property_verification_stats = <<>>

\* Test action that creates Byzantine double voting scenario
TestByzantineDoubleVote ==
    /\ slot = 1
    /\ byzantine_behaviors["n4"] = "double_vote"
    /\ votes' = [votes EXCEPT ![1]["n4"] = {"block1", "block2"}] \* Byzantine node votes for both blocks
    /\ UNCHANGED <<stake, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>

\* Test honest votes
TestHonestVotes ==
    /\ slot = 1
    /\ \E n \in TestNodes \ TestByzantineNodes:
        /\ \E b \in {"block1", "block2"}:
            /\ votes' = [votes EXCEPT ![1][n] = {b}]
    /\ UNCHANGED <<stake, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>

\* Test finalization attempt
TestFinalizationAttempt ==
    /\ slot = 1
    /\ \E b \in {"block1", "block2"}:
        /\ LET honest_voters == {n \in TestNodes : n \notin TestByzantineNodes /\ b \in votes[1][n]}
               honest_stake == SumStakes(honest_voters)
           IN honest_stake >= TestQuorum60 \* Only honest stake should count
        /\ finalized' = finalized @@ (1 :> b)
        /\ finalization_times' = finalization_times @@ (1 :> current_time)
    /\ UNCHANGED <<stake, votes, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>

\* Test specification
TestNext ==
    \/ TestByzantineDoubleVote
    \/ TestHonestVotes  
    \/ TestFinalizationAttempt

TestSpec == TestInit /\ [][TestNext]_vars

\* Properties to verify the fix
TestNoConflictingFinalization ==
    \A sl \in DOMAIN finalized: 
        LET finalized_block == finalized[sl]
            honest_voters == {n \in TestNodes : 
                /\ sl \in DOMAIN votes 
                /\ n \in DOMAIN votes[sl] 
                /\ finalized_block \in votes[sl][n] 
                /\ n \notin TestByzantineNodes}
            honest_stake == SumStakes(honest_voters)
        IN honest_stake >= TestQuorum60

TestByzantineCannotFinalize ==
    \A sl \in 1..TestMaxSlot:
        \A b \in {"block1", "block2"}:
            LET byzantine_voters == {n \in TestByzantineNodes : b \in votes[sl][n]}
                byzantine_stake == SumStakes(byzantine_voters)
                honest_voters == {n \in TestNodes \ TestByzantineNodes : b \in votes[sl][n]}
                honest_stake == SumStakes(honest_voters)
            IN (byzantine_stake > 0 /\ honest_stake < TestQuorum60) => 
               \lnot CanFinalize(b, sl, TestQuorum60)

TestEquivocationDetection ==
    \A n \in TestByzantineNodes:
        \A sl \in 1..TestMaxSlot:
            Cardinality(votes[sl][n]) > 1 =>
                \A b \in votes[sl][n]: \lnot CanFinalize(b, sl, TestQuorum60)

====