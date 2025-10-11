---- MODULE MC_7Nodes_Working ----
EXTENDS Alpenglow

MC_StateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime

====
