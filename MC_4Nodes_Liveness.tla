---- MODULE MC_4Nodes_Liveness ----
EXTENDS Alpenglow

MC_StateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime

====
