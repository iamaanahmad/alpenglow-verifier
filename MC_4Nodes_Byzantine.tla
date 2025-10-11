---- MODULE MC_4Nodes_Byzantine ----
EXTENDS Alpenglow

MC_StateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime

====
