'use client';

import { useState } from 'react';
import { mockCounterexample } from '@/lib/mock-data';
import CounterexampleTrace from '@/components/analysis/counterexample-trace';
import ProtocolVisualization from '@/components/analysis/protocol-visualization';
import AiExplanation from '@/components/analysis/ai-explanation';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { Alert, AlertDescription, AlertTitle } from '@/components/ui/alert';
import { AlertTriangle, ChevronsRight } from 'lucide-react';

export default function AnalysisPage() {
  const [currentStep, setCurrentStep] = useState(0);
  const counterexample = mockCounterexample;
  
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Counterexample Analysis</h1>
        <p className="text-muted-foreground">An interactive tool to analyze and debug model checking violations.</p>
      </div>

      {/* Success Alert for Fixed Issue */}
      <Alert className="border-green-200 bg-green-50 dark:border-green-800 dark:bg-green-950">
        <div className="flex items-center gap-2">
          <div className="w-2 h-2 bg-green-500 rounded-full animate-pulse"></div>
          <AlertTitle className="text-green-800 dark:text-green-200">
            ✅ Byzantine Double Voting Vulnerability Fixed
          </AlertTitle>
        </div>
        <AlertDescription className="text-green-700 dark:text-green-300 mt-2">
          The Byzantine double voting issue identified in counterexample analysis has been successfully resolved. 
          The <code className="bg-green-100 dark:bg-green-900 px-1 py-0.5 rounded text-xs">CanFinalize</code> function 
          now only counts honest stake toward finalization quorum, preventing Byzantine nodes from compromising safety.
        </AlertDescription>
      </Alert>

      <Card>
        <CardHeader>
            <Alert variant="destructive" className="w-fit opacity-60">
                <AlertTriangle className="h-4 w-4" />
                <AlertTitle className="flex items-center gap-2">
                    Property Violated (Historical) <ChevronsRight size={16} /> <span className="font-mono text-sm bg-destructive/20 px-2 py-1 rounded-md">{counterexample.violatedProperty}</span>
                </AlertTitle>
                <AlertDescription className="text-sm mt-1">
                  This counterexample shows the original vulnerability before the fix was applied.
                </AlertDescription>
            </Alert>
        </CardHeader>
        <CardContent>
            <div className="grid grid-cols-1 xl:grid-cols-5 gap-6">
                <div className="xl:col-span-2">
                <Card className="h-full bg-background/50">
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
                <div className="xl:col-span-3 space-y-6">
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
        </CardContent>
      </Card>
    </div>
  );
}
