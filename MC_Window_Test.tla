---------------- MODULE MC_Window_Test ----------------

EXTENDS Alpenglow

\* Model constants for window management testing
CONSTANTS n1, n2, n3, n4

\* Override state constraint for window testing
StateConstraint == 
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime
    /\ current_window <= MaxWindow
    /\ Cardinality(windows) <= MaxWindow

=======================================================