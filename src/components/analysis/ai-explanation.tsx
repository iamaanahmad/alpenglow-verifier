'use client';

import { useState } from 'react';
import { Bot, Loader2 } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { Alert, AlertDescription, AlertTitle } from '@/components/ui/alert';
import { explainTLCounterexample } from '@/ai/flows/explain-tlc-counterexample';

interface AiExplanationProps {
  tlaSpec: string;
  tlcCounterexample: string;
}

export default function AiExplanation({ tlaSpec, tlcCounterexample }: AiExplanationProps) {
  const [explanation, setExplanation] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleExplain = async () => {
    setIsLoading(true);
    setError(null);
    setExplanation(null);
    try {
      const result = await explainTLCounterexample({ tlaSpec, tlcCounterexample });
      setExplanation(result.explanation);
    } catch (e) {
      setError('Failed to get explanation from AI. Please try again.');
      console.error(e);
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <Card>
      <CardHeader>
        <div className="flex justify-between items-start">
            <div>
                <CardTitle>AI-Powered Explanation</CardTitle>
                <CardDescription>Analyze the counterexample and get a suggested fix.</CardDescription>
            </div>
            <Button onClick={handleExplain} disabled={isLoading} size="sm">
                {isLoading ? (
                <Loader2 className="mr-2 h-4 w-4 animate-spin" />
                ) : (
                <Bot className="mr-2 h-4 w-4" />
                )}
                {isLoading ? 'Analyzing...' : 'Get Explanation'}
            </Button>
        </div>
      </CardHeader>
      <CardContent>
        <div className="flex flex-col items-start gap-4">
          {error && (
            <Alert variant="destructive">
              <AlertTitle>Error</AlertTitle>
              <AlertDescription>{error}</AlertDescription>
            </Alert>
          )}
          
          {explanation && (
            <div className="p-4 bg-muted/50 rounded-lg w-full border space-y-4">
                <h3 className="font-semibold text-foreground">AI Suggestion:</h3>
                <div className="text-sm text-muted-foreground space-y-2">
                  {explanation.split('\n').map((line, i) => <p key={i}>{line}</p>)}
                </div>
            </div>
          )}

          {!isLoading && !explanation && !error && (
             <div className="p-4 bg-muted/50 rounded-lg w-full border text-center text-sm text-muted-foreground">
                Click "Get Explanation" to see the AI analysis.
             </div>
          )}

          {isLoading && (
            <div className="p-4 bg-muted/50 rounded-lg w-full border text-center text-sm text-muted-foreground flex items-center justify-center">
                <Loader2 className="mr-2 h-4 w-4 animate-spin" />
                AI is analyzing the trace...
            </div>
          )}
        </div>
      </CardContent>
    </Card>
  );
}
