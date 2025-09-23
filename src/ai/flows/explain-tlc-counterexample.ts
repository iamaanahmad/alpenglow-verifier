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
  prompt: `You are an expert in TLA+ and the TLC model checker. Your task is to analyze a TLC-generated counterexample and provide a clear, actionable explanation for how to fix the TLA+ specification.

  Follow these steps:
  1.  **Parse the Counterexample**: Analyze the state trace to understand the sequence of actions and state changes that lead to the violation.
  2.  **Identify the Failure Pattern**: Diagnose the root cause of the error. Common patterns include, but are not limited to:
      - **Equivocation**: A node provides conflicting information to different peers.
      - **Missed Quorum**: A decision was made without sufficient votes/signatures.
      - **Split Brain**: Two or more partitions of the network make conflicting decisions.
      - **Liveness Failure**: The system fails to make progress.
      - **Incorrect State Update**: A variable was updated incorrectly.
  3.  **Suggest a Fix**: Provide a specific, code-level recommendation for how to modify the TLA+ specification to prevent this counterexample. Explain why your suggested change resolves the issue.

  Here is the TLA+ specification and the counterexample:

  **TLA+ Specification:**
  \`\`\`tlaplus
  {{tlaSpec}}
  \`\`\`

  **TLC Counterexample Trace (JSON):**
  \`\`\`json
  {{tlcCounterexample}}
  \`\`\`

  **Analysis and Suggested Fix:**
  Provide your explanation below.
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
