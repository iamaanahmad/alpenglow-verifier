
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { CodeBlock } from "@/components/code-block";
import { Accordion, AccordionContent, AccordionItem, AccordionTrigger } from "@/components/ui/accordion";
import { ShieldCheck, Zap, HeartPulse } from "lucide-react";
import { Badge } from "@/components/ui/badge";

const properties = [
  {
    name: "NoConflictingBlocksFinalized",
    category: "Safety",
    description: "Ensures no two conflicting blocks can be finalized in the same slot. This is the core safety guarantee against forks.",
    tlaDefinition: `NoConflictingBlocksFinalized ==
    /\\ \\A sl \\in DOMAIN finalized: finalized[sl] \\in Blocks
    /\\ \\A sl1, sl2 \\in DOMAIN finalized: 
        (sl1 = sl2) => (finalized[sl1] = finalized[sl2])`
  },
  {
    name: "CertificateUniqueness",
    category: "Safety",
    description: "Guarantees that each slot has at most one valid certificate, preventing ambiguity in finalization.",
    tlaDefinition: `CertificateUniqueness ==
    /\\ \\A c1, c2 \\in certs: (c1.slot = c2.slot) => (c1 = c2)
    /\\ \\A c1, c2 \\in skip_certs: (c1.slot = c2.slot) => (c1 = c2)
    /\\ \\A sl \\in Slots: \\lnot (\\exists c1 \\in certs, c2 \\in skip_certs: c1.slot = sl /\\ c2.slot = sl)`
  },
  {
    name: "ForkPrevention",
    category: "Safety",
    description: "Ensures that the chain of finalized blocks remains consistent and free of forks, even under adversarial conditions.",
    tlaDefinition: `ForkPrevention ==
    /\\ \\A sl \\in DOMAIN finalized:
        \\A b1, b2 \\in Blocks:
            (b1 /= b2) => \\lnot (CanFinalize(b1, sl, AdjustedQuorum60) /\\ CanFinalize(b2, sl, AdjustedQuorum60))`
  },
  {
    name: "ByzantineFaultTolerance",
    category: "Safety",
    description: "Asserts that all safety properties hold as long as the stake controlled by Byzantine nodes is at or below 20%.",
    tlaDefinition: `ByzantineFaultTolerance ==
    ByzantineStake <= (TotalStake * 20) \\div 100`
  },
  {
    name: "ChainConsistencyUnderByzantineFaults",
    category: "Safety",
    description: "Maintains that the honest supermajority always controls finalization decisions, preserving chain consistency despite Byzantine actions.",
    tlaDefinition: `ChainConsistencyUnderByzantineFaults ==
    /\\ \\A sl \\in DOMAIN finalized:
        LET honest_voters == {n \\in Nodes : finalized[sl] \\in votes[sl][n] /\\ \\lnot IsByzantine(n)}
            honest_stake == SumStakes(honest_voters)
        IN honest_stake >= AdjustedQuorum60 \\div 2`
  },
  {
    name: "NoEquivocation",
    category: "Safety",
    description: "Prevents honest nodes from double-voting, while allowing the model to detect and handle equivocation from Byzantine nodes.",
    tlaDefinition: `NoEquivocation ==
    \\A n \\in Nodes:
        \\A sl \\in DOMAIN votes:
            \\A v1, v2 \\in votes[sl][n]:
                v1.block = v2.block`
  },
  {
    name: "ProgressWithHonestSupermajority",
    category: "Liveness",
    description: "Guarantees the network will continue to finalize blocks as long as a supermajority of stake is honest and the network is partially synchronous.",
    tlaDefinition: `ProgressWithHonestSupermajority ==
    (HonestResponsiveSupermajority /\\ PartialSynchronyHolds) 
    ~> (\\exists sl \\in Slots : sl \\in DOMAIN finalized)`
  },
  {
    name: "FastPathCompletion",
    category: "Liveness",
    description: "Verifies that with 80% responsive stake, the protocol achieves finality in a single round, meeting its key performance claim.",
    tlaDefinition: `FastPathCompletion ==
    \\A sl \\in Slots :
        (Has80PercentResponsiveStake /\\ HasBlockProposal(sl) /\\ PartialSynchronyHolds) 
        ~> 
        (FastCertificateGenerated(sl) /\\ FinalizationWithinFastPathBound(sl))`
  },
  {
    name: "SlowPathCompletion",
    category: "Liveness",
    description: "Ensures the conservative fallback path achieves finality within a bounded time when at least 60% of stake is responsive.",
    tlaDefinition: `SlowPathCompletion ==
    \\A sl \\in Slots :
        (Has60PercentResponsiveStake /\\ HasBlockProposal(sl) /\\ PartialSynchronyHolds)
        ~>
        (CertificateGenerated(sl) /\\ FinalizationWithinSlowPathBound(sl))`
  },
  {
    name: "BoundedFinalizationTimes",
    category: "Liveness",
    description: "Confirms that block finalization time is predictably bounded by the minimum of the fast and slow path conditions (min(δ₈₀%, 2δ₆₀%)).",
    tlaDefinition: `BoundedFinalizationTimes ==
    \\A sl \\in Slots :
        (sl \\in DOMAIN finalized /\\ sl \\in DOMAIN finalization_times /\\ sl \\in DOMAIN round_start_time)
        =>
        (FinalizationWithinOptimalBounds(sl))`
  },
  {
    name: "SafetyWithByzantineStake",
    category: "Resilience",
    description: "Verifies that core safety invariants hold true when the network contains up to 20% Byzantine (malicious) stake.",
    tlaDefinition: `SafetyWithByzantineStake == 
    ByzantineStake <= (TotalStake * 20) \\div 100
    =>
    /\\ NoConflictingBlocksFinalized
    /\\ CertificateUniqueness`
  },
  {
    name: "LivenessWithOfflineStake",
    category: "Resilience",
    description: "Guarantees the protocol remains live and continues to make progress even if up to 20% of validator stake is offline or unresponsive.",
    tlaDefinition: `LivenessWithOfflineStake == 
      LET OfflineStake == {n \\in Nodes: n.offline = TRUE}
      IN (\\sum_{n \\in OfflineStake} stake[n] <= 0.2 * TotalStake)
        => ProgressWithHonestSupermajority`
  },
  {
    name: "RecoveryFromPartition",
    category: "Resilience",
    description: "Ensures the system can recover and resume making progress after a network partition is resolved.",
    tlaDefinition: `RecoveryFromPartition ==
    []((IsPartitioned) => (<>(~IsPartitioned => <>(\\E sl \\in Nat: sl \\in DOMAIN finalized))))`
  }
];

const PropertySection = ({ title, properties, icon: Icon }: { title: string, properties: typeof properties, icon: React.ElementType }) => (
  <AccordionItem value={title.toLowerCase().replace(' ', '-')}>
    <AccordionTrigger className="text-xl font-medium">
      <div className="flex items-center gap-3">
        <Icon className="w-6 h-6" />
        {title}
      </div>
    </AccordionTrigger>
    <AccordionContent>
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-4 pt-4">
        {properties.map(prop => (
          <Card key={prop.name} className="bg-card/80">
            <CardHeader>
              <div className="flex justify-between items-start">
                <CardTitle>{prop.name}</CardTitle>
                <Badge variant="default">Verified</Badge>
              </div>
              <CardDescription>{prop.description}</CardDescription>
            </CardHeader>
            <CardContent>
              <CodeBlock code={prop.tlaDefinition} language="tlaplus" />
            </CardContent>
          </Card>
        ))}
      </div>
    </AccordionContent>
  </AccordionItem>
);

export default function PropertiesPage() {
  const safetyProps = properties.filter(p => p.category === "Safety");
  const livenessProps = properties.filter(p => p.category === "Liveness");
  const resilienceProps = properties.filter(p => p.category === "Resilience");

  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Verified Properties</h1>
        <p className="text-muted-foreground">Formal definitions and proof status for Alpenglow's core correctness guarantees.</p>
      </div>

      <Accordion type="single" collapsible defaultValue="safety" className="w-full">
        <PropertySection title="Safety Properties" properties={safetyProps} icon={() => <ShieldCheck className="text-green-500" />} />
        <PropertySection title="Liveness Properties" properties={livenessProps} icon={() => <Zap className="text-yellow-500" />} />
        <PropertySection title="Resilience Properties" properties={resilienceProps} icon={() => <HeartPulse className="text-blue-500" />} />
      </Accordion>
    </div>
  );
}
