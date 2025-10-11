---- MODULE MC_4Nodes_Working ----
EXTENDS Alpenglow

MC_StateConstraint ==
    /\ slot <= MaxSlot
    /\ current_time <= MaxTime
    /\ Cardinality(DOMAIN certs) <= MaxSlot * 2

====
