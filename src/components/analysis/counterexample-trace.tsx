import { ScrollArea } from '@/components/ui/scroll-area';
import { Button } from '@/components/ui/button';
import type { CounterexampleStep } from '@/lib/mock-data';
import { Table, TableBody, TableCell, TableRow } from '@/components/ui/table';

interface CounterexampleTraceProps {
  trace: CounterexampleStep[];
  currentStep: number;
  onStepSelect: (step: number) => void;
}

export default function CounterexampleTrace({ trace, currentStep, onStepSelect }: CounterexampleTraceProps) {
  return (
    <div className="space-y-4">
      <ScrollArea className="h-64">
        <div className="flex flex-col gap-1 pr-4">
          {trace.map((step, index) => (
            <Button
              key={step.step}
              variant={currentStep === index ? 'secondary' : 'ghost'}
              className="w-full justify-start text-left h-auto py-2"
              onClick={() => onStepSelect(index)}
            >
              <div className="flex flex-col">
                <span className="font-semibold text-sm">Step {step.step}</span>
                <span className="text-xs text-muted-foreground">{step.action}</span>
              </div>
            </Button>
          ))}
        </div>
      </ScrollArea>
      
      <div>
        <h4 className="font-semibold mb-2">State at Step {trace[currentStep].step}</h4>
        <ScrollArea className="h-96">
            <div className="rounded-md border">
            <Table>
                <TableBody>
                {Object.entries(trace[currentStep].state).map(([key, value]) => (
                    <TableRow key={key}>
                    <TableCell className="font-mono text-xs font-medium !py-2">{key}</TableCell>
                    <TableCell className="font-mono text-xs !py-2">{JSON.stringify(value, null, 2)}</TableCell>
                    </TableRow>
                ))}
                </TableBody>
            </Table>
            </div>
        </ScrollArea>
      </div>
    </div>
  );
}
