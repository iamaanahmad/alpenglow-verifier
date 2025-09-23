import { ModelConfigForm } from '@/components/model-config-form';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';

export default function DashboardPage() {
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Dashboard</h1>
        <p className="text-muted-foreground">Configure and manage your Alpenglow verification models.</p>
      </div>

      <Card>
        <CardHeader>
          <CardTitle>Create a New Verification Run</CardTitle>
          <CardDescription>
            Configure the parameters for the TLA+ model checker. Results will appear in the Verification Runs tab.
          </CardDescription>
        </CardHeader>
        <CardContent>
          <ModelConfigForm />
        </CardContent>
      </Card>
    </div>
  );
}
