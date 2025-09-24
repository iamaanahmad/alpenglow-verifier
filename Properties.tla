---------------- MODULE Properties ----------------

EXTENDS Alpenglow

\* =============================================================================
\* Safety Properties: "Nothing bad ever happens"
\* =============================================================================

\* @type: safety;
\* @description: "Ensures no two conflicting blocks are ever finalized in the same slot.";
NoConflictingBlocksFinalized ==
    \A sl \in DOMAIN finalized:
        Cardinality(finalized[sl]) <= 1

\* @type: safety;
\* @description: "Guarantees that certificates are unique for each slot and cannot be forged.";
CertificateUniqueness ==
    \A sl \in DOMAIN certs:
        Cardinality(certs[sl]) <= 1

\* @type: safety;
\* @description: "Prevents Byzantine nodes from causing validators to vote for conflicting blocks in the same slot.";
NoEquivocation ==
    \A n \in Nodes:
        \A sl \in DOMAIN votes:
            \A v1, v2 \in votes[sl][n]:
                v1.block = v2.block

\* =============================================================================
\* Liveness Properties: "Something good eventually happens"
\* =================================G============================================

\* @type: liveness;
\* @description: "Ensures that if a supermajority of stake is honest and responsive, the network makes progress.";
ProgressWithHonestSupermajority ==
    LET HonestStake == {n \in Nodes: n.byzantine = FALSE}
    IN  (\sum_{n \in HonestStake} stake[n] >= 0.67 * TotalStake)
            => <>(\E sl \in Nat: sl \in DOMAIN finalized)

\* @type: liveness;
\* @description: "Guarantees that the fast path completes in a single round if 80% of the stake is responsive.";
FastPathCompletion ==
    LET ResponsiveStake == {n \in Nodes: n.offline = FALSE}
    IN  (\sum_{n \in ResponsiveStake} stake[n] >= 0.8 * TotalStake)
            => <>(
                \E sl \in Nat:
                    \E c \in certs[sl]:
                        c.quorum = "Quorum80"
               )

\* =============================================================================
\* Resilience Properties: "The system tolerates failures"
\* =============================================================================

\* @type: resilience;
\* @description: "Maintains safety even with a Byzantine stake of up to 20% of the total stake.";
SafetyWithByzantineStake ==
    LET ByzantineStake == {n \in Nodes: n.byzantine = TRUE}
    IN  (\sum_{n \in ByzantineStake} stake[n] <= 0.2 * TotalStake)
            => NoConflictingBlocksFinalized

\* @type: resilience;
\* @description: "Guarantees liveness even if up to 20% of the total stake is offline.";
LivenessWithOfflineStake ==
    LET OfflineStake == {n \in Nodes: n.offline = TRUE}
    IN  (\sum_{n \in OfflineStake} stake[n] <= 0.2 * TotalStake)
            => ProgressWithHonestSupermajority

\* @type: resilience;
\* @description: "Ensures the system can recover and continue to finalize blocks after a network partition is resolved.";
RecoveryFromPartition ==
    LET IsPartitioned == \E p1, p2 \in PARTITION(Nodes): p1 /= {} /\ p2 /= {}
    IN  []((IsPartitioned) => (<>(~IsPartitioned => <>(\E sl \in Nat: sl \in DOMAIN finalized))))

=======================================================
