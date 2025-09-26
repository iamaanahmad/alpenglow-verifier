/**
 * @fileOverview Explains TLC counterexamples to help users debug and refine their TLA+ specifications.
 * 
 * Note: AI functionality disabled for static export compatibility
 */

export type ExplainTLCounterexampleInput = {
  tlaSpec: string;
  tlcCounterexample: string;
};

export type ExplainTLCounterexampleOutput = {
  explanation: string;
};

// Mock function for static export compatibility
export async function explainTLCounterexample(input: ExplainTLCounterexampleInput): Promise<ExplainTLCounterexampleOutput> {
  // Return a mock explanation for static deployment
  return {
    explanation: "AI analysis is not available in the static deployment version. Please use the development version for full AI capabilities."
  };
}