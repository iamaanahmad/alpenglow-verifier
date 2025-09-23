
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";
import { Accordion, AccordionContent, AccordionItem, AccordionTrigger } from "@/components/ui/accordion";
import { ShieldCheck, Zap, HeartPulse } from "lucide-react";

const safetyProperties = `
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
`;

const livenessProperties = `
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
`;

const resilienceProperties = `
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
`;

export default function PropertiesPage() {
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Property Definitions</h1>
        <p className="text-muted-foreground">Formal definitions for safety, liveness, and resilience properties of Alpenglow.</p>
      </div>

      <Accordion type="single" collapsible defaultValue="safety" className="w-full">
        <AccordionItem value="safety">
          <AccordionTrigger className="text-xl font-medium">
            <div className="flex items-center gap-3">
              <ShieldCheck className="w-6 h-6 text-green-500" />
              Safety Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4 bg-card/80">
              <CardHeader>
                <CardTitle>Ensuring Correctness</CardTitle>
                <CardDescription>These properties ensure that nothing bad ever happens, such as finalizing conflicting blocks or accepting forged certificates.</CardDescription>
              </CardHeader>
              <CardContent>
                <CodeBlock code={safetyProperties} language="tlaplus" />
              </CardContent>
            </Card>
          </AccordionContent>
        </AccordionItem>
        <AccordionItem value="liveness">
          <AccordionTrigger className="text-xl font-medium">
            <div className="flex items-center gap-3">
              <Zap className="w-6 h-6 text-yellow-500" />
              Liveness Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4 bg-card/80">
              <CardHeader>
                <CardTitle>Ensuring Progress</CardTitle>
                <CardDescription>These properties ensure that something good eventually happens, like the network making progress or reaching finality.</CardDescription>
              </Header>
              <CardContent>
                <CodeBlock code={livenessProperties} language="tlaplus" />
              </CardContent>
            </Card>
          </AccordionContent>
        </AccordionItem>
        <AccordionItem value="resilience">
          <AccordionTrigger className="text-xl font-medium">
            <div className="flex items-center gap-3">
              <HeartPulse className="w-6 h-6 text-blue-500" />
              Resilience Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4 bg-card/80">
              <CardHeader>
                <CardTitle>Ensuring Fault Tolerance</CardTitle>
                <CardDescription>These properties define the fault tolerance limits of the protocol, ensuring it remains safe and live under adversarial conditions.</CardDescription>
              </Header>
              <CardContent>
                <CodeBlock code={resilienceProperties} language="tlaplus" />
              </CardContent>
            </Card>
          </AccordionContent>
        </AccordionItem>
      </Accordion>
    </div>
  );
}
