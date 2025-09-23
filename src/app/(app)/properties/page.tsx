import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";
import { Accordion, AccordionContent, AccordionItem, AccordionTrigger } from "@/components/ui/accordion";
import { ShieldCheck, Zap, HeartPulse } from "lucide-react";

const safetyProperties = `
NoConflictingBlocksFinalized ==
    \A s1, s2 \in DOMAIN blockchain:
        s1.slot = s2.slot => s1.block = s2.block

ChainConsistency ==
    \A n1, n2 \in ByzantineQuorum:
        ConsistentChains(n1.chain, n2.chain)
`;

const livenessProperties = `
Progress ==
    \A honest_stake >= 0.6 * TotalStake: <>(\A n \in honest_stake: EventuallyFinalizes(n))

FastPathCompletion ==
    \A responsive_stake >= 0.8 * TotalStake:
        <>(RoundCompletesInOnePhase)
`;

const resilienceProperties = `
SafetyWithByzantine ==
    (ByzantineStake <= 0.2 * TotalStake) => NoConflictingBlocksFinalized

LivenessWithOffline ==
    (OfflineStake <= 0.2 * TotalStake) => Progress
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
          <AccordionTrigger className="text-xl">
            <div className="flex items-center gap-3">
              <ShieldCheck className="w-6 h-6 text-green-500" />
              Safety Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4">
              <CardHeader>
                <CardTitle>Safety</CardTitle>
                <CardDescription>These properties ensure that nothing bad ever happens.</CardDescription>
              </CardHeader>
              <CardContent>
                <CodeBlock code={safetyProperties} language="tlaplus" />
              </CardContent>
            </Card>
          </AccordionContent>
        </AccordionItem>
        <AccordionItem value="liveness">
          <AccordionTrigger className="text-xl">
            <div className="flex items-center gap-3">
              <Zap className="w-6 h-6 text-yellow-500" />
              Liveness Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4">
              <CardHeader>
                <CardTitle>Liveness</CardTitle>
                <CardDescription>These properties ensure that something good eventually happens.</CardDescription>
              </Header>
              <CardContent>
                <CodeBlock code={livenessProperties} language="tlaplus" />
              </CardContent>
            </Card>
          </AccordionContent>
        </AccordionItem>
        <AccordionItem value="resilience">
          <AccordionTrigger className="text-xl">
            <div className="flex items-center gap-3">
              <HeartPulse className="w-6 h-6 text-blue-500" />
              Resilience Properties
            </div>
          </AccordionTrigger>
          <AccordionContent>
            <Card className="mt-4">
              <CardHeader>
                <CardTitle>Resilience</CardTitle>
                <CardDescription>These properties define the fault tolerance limits of the protocol.</CardDescription>
              </CardHeader>
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
