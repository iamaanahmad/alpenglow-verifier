---- MODULE MC_Timeout_Test ----
EXTENDS Alpenglow

\* Model checking configuration for timeout and skip certificate testing
\* This configuration focuses on testing timeout mechanisms and skip certificate generation

\* Override constants for focused testing
CONSTANTS
    Nodes, TotalStake, Quorum80, Quorum60, MaxSlot, 
    ByzantineNodes, ByzantineStakeRatio, ErasureCodingFactor, 
    NetworkDelay, SlotTimeout, MaxTime

\* Additional properties specific to timeout testing
TimeoutEventuallyHappens ==
    \* If no progress is made, timeout should eventually occur
    \A sl \in Slots : 
        (NoProgressInSlot(sl) /\ current_time >= SlotTimeout) => <>(sl \in timeouts)

SkipCertificateEventuallyGenerated ==
    \* If slot times out, skip certificate should eventually be generated
    \A sl \in timeouts : <>(HasSkipCertificate(sl))

NoConflictingCertificates ==
    \* No slot should have both regular and skip certificate
    \A sl \in Slots :
        \lnot (\exists c1 \in certs, c2 \in skip_certs : c1.slot = sl /\ c2.slot = sl)

CascadingTimeoutBounded ==
    \* Cascading timeouts should be bounded
    \A sl \in Slots : CountConsecutiveTimeouts(sl) <= 3

====