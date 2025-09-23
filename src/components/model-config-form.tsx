'use client';

import { zodResolver } from '@hookform/resolvers/zod';
import { useForm } from 'react-hook-form';
import * as z from 'zod';
import React from 'react';

import { Button } from '@/components/ui/button';
import {
  Form,
  FormControl,
  FormDescription,
  FormField,
  FormItem,
  FormLabel,
  FormMessage,
} from '@/components/ui/form';
import { Input } from '@/components/ui/input';
import { Slider } from '@/components/ui/slider';
import { Checkbox } from '@/components/ui/checkbox';
import { useToast } from '@/hooks/use-toast';
import { Rocket } from 'lucide-react';

const formSchema = z.object({
  modelName: z.string().min(2, {
    message: 'Model name must be at least 2 characters.',
  }),
  networkSize: z.number().min(4).max(100),
  byzantineNodes: z.number().min(0).max(50),
  scenarios: z.array(z.string()).refine((value) => value.some((item) => item), {
    message: 'You have to select at least one scenario.',
  }),
});

const scenarios = [
  { id: 'network_partition', label: 'Network Partitions' },
  { id: 'leader_failure', label: 'Leader Failure' },
  { id: 'high_latency', label: 'High Latency' },
];

export function ModelConfigForm() {
  const { toast } = useToast();
  const [networkSize, setNetworkSize] = React.useState(10);
  const [byzantineNodes, setByzantineNodes] = React.useState(1);

  const form = useForm<z.infer<typeof formSchema>>({
    resolver: zodResolver(formSchema),
    defaultValues: {
      modelName: `Alpenglow-Run-${new Date().toISOString().split('T')[0]}`,
      networkSize: 10,
      byzantineNodes: 1,
      scenarios: ['network_partition'],
    },
  });

  React.useEffect(() => {
    const subscription = form.watch((value, { name }) => {
      if (name === 'networkSize' && value.networkSize) {
        setNetworkSize(value.networkSize);
        const maxByzantine = Math.floor((value.networkSize - 1) / 3);
        if (form.getValues('byzantineNodes') > maxByzantine) {
          form.setValue('byzantineNodes', maxByzantine);
          setByzantineNodes(maxByzantine);
        }
      }
      if (name === 'byzantineNodes' && value.byzantineNodes) {
        setByzantineNodes(value.byzantineNodes);
      }
    });
    return () => subscription.unsubscribe();
  }, [form]);

  function onSubmit(values: z.infer<typeof formSchema>) {
    console.log(values);
    toast({
      title: 'Verification Started',
      description: `Model "${values.modelName}" is being verified.`,
    });
  }

  return (
    <Form {...form}>
      <form onSubmit={form.handleSubmit(onSubmit)} className="space-y-8 max-w-2xl">
        <FormField
          control={form.control}
          name="modelName"
          render={({ field }) => (
            <FormItem>
              <FormLabel>Model Name</FormLabel>
              <FormControl>
                <Input placeholder="e.g., Small_Network_Test" {...field} />
              </FormControl>
              <FormMessage />
            </FormItem>
          )}
        />
        
        <FormField
          control={form.control}
          name="networkSize"
          render={({ field: { onChange } }) => (
            <FormItem>
              <FormLabel>Network Size: {networkSize} nodes</FormLabel>
              <FormControl>
                <Slider
                  min={4}
                  max={100}
                  step={1}
                  defaultValue={[networkSize]}
                  onValueChange={(vals) => onChange(vals[0])}
                />
              </FormControl>
              <FormDescription>Total number of nodes in the network.</FormDescription>
              <FormMessage />
            </FormItem>
          )}
        />

        <FormField
          control={form.control}
          name="byzantineNodes"
          render={({ field: { onChange } }) => (
            <FormItem>
              <FormLabel>Byzantine Nodes: {byzantineNodes} nodes</FormLabel>
              <FormControl>
                <Slider
                  min={0}
                  max={Math.floor((networkSize -1) / 3) }
                  step={1}
                  value={[byzantineNodes]}
                  onValueChange={(vals) => onChange(vals[0])}
                />
              </FormControl>
              <FormDescription>Number of faulty/malicious nodes (f {'<'} n/3).</FormDescription>
              <FormMessage />
            </FormItem>
          )}
        />

        <FormField
          control={form.control}
          name="scenarios"
          render={() => (
            <FormItem>
              <div className="mb-4">
                <FormLabel className="text-base">Adversarial Scenarios</FormLabel>
                <FormDescription>
                  Select scenarios to test against.
                </FormDescription>
              </div>
              <div className="space-y-2">
                {scenarios.map((item) => (
                  <FormField
                    key={item.id}
                    control={form.control}
                    name="scenarios"
                    render={({ field }) => {
                      return (
                        <FormItem
                          key={item.id}
                          className="flex flex-row items-center space-x-3 space-y-0"
                        >
                          <FormControl>
                            <Checkbox
                              checked={field.value?.includes(item.id)}
                              onCheckedChange={(checked) => {
                                return checked
                                  ? field.onChange([...field.value, item.id])
                                  : field.onChange(
                                      field.value?.filter(
                                        (value) => value !== item.id
                                      )
                                    );
                              }}
                            />
                          </FormControl>
                          <FormLabel className="font-normal">
                            {item.label}
                          </FormLabel>
                        </FormItem>
                      );
                    }}
                  />
                ))}
              </div>
              <FormMessage />
            </FormItem>
          )}
        />
        
        <Button type="submit" size="lg">
          <Rocket className="mr-2 h-4 w-4" />
          Generate & Verify
        </Button>
      </form>
    </Form>
  );
}
