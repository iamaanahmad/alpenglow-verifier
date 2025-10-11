---- MODULE MC_10Nodes_Working ----
EXTENDS Alpenglow

MC_StateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime

====
