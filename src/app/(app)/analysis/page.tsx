'use client';

import { useState } from 'react';
import { mockCounterexample } from '@/lib/mock-data';
import CounterexampleTrace from '@/components/analysis/counterexample-trace';
import ProtocolVisualization from '@/components/analysis/protocol-visualization';
import AiExplanation from '@/components/analysis/ai-explanation';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { Alert, AlertDescription, AlertTitle } from '@/components/ui/alert';
import { AlertTriangle } from 'lucide-react';

export default function AnalysisPage() {
  const [currentStep, setCurrentStep] = useState(0);
  const counterexample = mockCounterexample;
  
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Counterexample Analysis</h1>
        <p className="text-muted-foreground">An interactive tool to analyze and debug model checking violations.</p>
      </div>

      <Alert variant="destructive" className="max-w-xl">
        <AlertTriangle className="h-4 w-4" />
        <AlertTitle>Property Violated</AlertTitle>
        <AlertDescription>{counterexample.violatedProperty}</AlertDescription>
      </Alert>

      <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
        <div className="lg:col-span-1">
          <Card className="h-full">
            <CardHeader>
              <CardTitle>State Trace</CardTitle>
              <CardDescription>Step-by-step execution leading to failure.</CardDescription>
            </CardHeader>
            <CardContent>
              <CounterexampleTrace 
                trace={counterexample.trace}
                currentStep={currentStep}
                onStepSelect={setCurrentStep}
              />
            </CardContent>
          </Card>
        </div>
        <div className="lg:col-span-2 space-y-6">
          <Card>
            <CardHeader>
              <CardTitle>Protocol Visualization</CardTitle>
              <CardDescription>Visual state of the network at step {currentStep + 1}.</CardDescription>
            </CardHeader>
            <CardContent>
              <ProtocolVisualization traceStep={counterexample.trace[currentStep]} />
            </CardContent>
          </Card>
          <AiExplanation 
            tlaSpec={counterexample.tlaSpec} 
            tlcCounterexample={JSON.stringify(counterexample.trace, null, 2)} 
          />
        </div>
      </div>
    </div>
  );
}
