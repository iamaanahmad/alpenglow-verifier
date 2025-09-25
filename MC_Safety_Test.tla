---------------- MODULE MC_Safety_Test ----------------

EXTENDS Alpenglow, Properties

\* Model checking constants
CONSTANTS
    Nodes, TotalStake, Quorum80, Quorum60, MaxSlot, ByzantineNodes, ByzantineStakeRatio,
    ErasureCodingFactor, NetworkDelay, SlotTimeout, MaxTime, WindowSize,
    Delta80, Delta60, MaxNetworkDelay, MinNetworkDelay, PartialSynchronyBound,
    RoundTimeout, FastPathTimeout, SlowPathTimeout

\* State constraint for safety property testing
SafetyStateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime
    /\ current_window <= MaxWindow
    /\ Cardinality(windows) <= MaxWindow
    /\ Cardinality(timeouts) <= MaxSlot
    /\ Cardinality(certs) <= MaxSlot
    /\ Cardinality(skip_certs) <= MaxSlot

=======================================================