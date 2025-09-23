'use server';

/**
 * @fileOverview Explains TLC counterexamples to help users debug and refine their TLA+ specifications.
 *
 * - explainTLCounterexample - A function that takes a TLC counterexample and returns an explanation of how to rewrite the TLA+ spec.
 * - ExplainTLCounterexampleInput - The input type for the explainTLCounterexample function.
 * - ExplainTLCounterexampleOutput - The return type for the explainTLCounterexample function.
 */

import {ai} from '@/ai/genkit';
import {z} from 'genkit';

const ExplainTLCounterexampleInputSchema = z.object({
  tlaSpec: z.string().describe('The TLA+ specification.'),
  tlcCounterexample: z.string().describe('The TLC counterexample generated from the TLA+ specification.'),
});

export type ExplainTLCounterexampleInput = z.infer<typeof ExplainTLCounterexampleInputSchema>;

const ExplainTLCounterexampleOutputSchema = z.object({
  explanation: z.string().describe('An explanation of how to rewrite the TLA+ spec based on the TLC counterexample.'),
});

export type ExplainTLCounterexampleOutput = z.infer<typeof ExplainTLCounterexampleOutputSchema>;

export async function explainTLCounterexample(input: ExplainTLCounterexampleInput): Promise<ExplainTLCounterexampleOutput> {
  return explainTLCounterexampleFlow(input);
}

const explainTLCounterexamplePrompt = ai.definePrompt({
  name: 'explainTLCounterexamplePrompt',
  input: {
    schema: ExplainTLCounterexampleInputSchema,
  },
  output: {
    schema: ExplainTLCounterexampleOutputSchema,
  },
  prompt: `You are an expert in TLA+ and the TLC model checker. Given a TLA+ specification and a TLC counterexample, your task is to explain how to rewrite the TLA+ specification to avoid the counterexample.

  TLA+ Specification:
  {{tlaSpec}}

  TLC Counterexample:
  {{tlcCounterexample}}

  Explanation: Provide a detailed explanation of the error and how to correct the TLA+ specification. Be specific and provide code examples if possible.
  `,
});

const explainTLCounterexampleFlow = ai.defineFlow(
  {
    name: 'explainTLCounterexampleFlow',
    inputSchema: ExplainTLCounterexampleInputSchema,
    outputSchema: ExplainTLCounterexampleOutputSchema,
  },
  async input => {
    const {output} = await explainTLCounterexamplePrompt(input);
    return output!;
  }
);
