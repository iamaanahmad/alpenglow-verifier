
import { ModelConfigForm } from '@/components/model-config-form';
import { Card, CardContent, CardHeader, CardTitle, CardDescription } from '@/components/ui/card';
import { Button } from '@/components/ui/button';
import Link from 'next/link';
import { PlayCircle, FileCode2, ShieldCheck, BarChart3, Activity, Zap } from 'lucide-react';

const quickLinks = [
  { href: '/specification', label: 'View Specification', icon: FileCode2 },
  { href: '/properties', label: 'Inspect Properties', icon: ShieldCheck },
  { href: '/verification', label: 'See Verification Runs', icon: PlayCircle },
  { href: '/analysis', label: 'Analyze a Failure', icon: BarChart3 },
];

export default function DashboardPage() {
  return (
    <div className="space-y-8">
      <div className="p-8 bg-card border rounded-lg shadow-lg">
        <h1 className="text-4xl font-bold tracking-tight text-primary">Alpenglow Verifier</h1>
        <p className="text-lg text-muted-foreground mt-2">A formal verification system for Solana’s Alpenglow consensus protocol.</p>
        <p className="text-muted-foreground mt-4 max-w-3xl">
          Use this dashboard to configure and run verification models against the TLA+ specification.
          You can define network conditions, introduce adversarial scenarios, and analyze the results to ensure the protocol is both safe and live.
        </p>
      </div>
      
      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <Card>
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Success Rate</CardTitle>
            <ShieldCheck className="h-4 w-4 text-green-500" />
          </CardHeader>
          <CardContent>
            <div className="text-2xl font-bold text-green-600">100%</div>
            <p className="text-xs text-muted-foreground">
              All 6 core configurations passed
            </p>
          </CardContent>
        </Card>
        <Card>
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Properties Verified</CardTitle>
            <Activity className="h-4 w-4 text-blue-500" />
          </CardHeader>
          <CardContent>
            <div className="text-2xl font-bold text-blue-600">13 / 13</div>
            <p className="text-xs text-muted-foreground">
              Safety, Liveness & Resilience
            </p>
          </CardContent>
        </Card>
        <Card>
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Byzantine Tolerance</CardTitle>
            <Zap className="h-4 w-4 text-orange-500" />
          </CardHeader>
          <CardContent>
            <div className="text-2xl font-bold text-orange-600">≤20%</div>
            <p className="text-xs text-muted-foreground">
              Proven malicious stake tolerance
            </p>
          </CardContent>
        </Card>
      </div>

      <div className="grid grid-cols-1 lg:grid-cols-3 gap-8">
        <div className="lg:col-span-2">
          <Card className="h-full">
            <CardHeader>
              <CardTitle className="text-2xl">Create a New Verification Run</CardTitle>
              <CardDescription>
                Configure the parameters for the TLA+ model checker. Results will appear in the "Verification Runs" tab.
              </CardDescription>
            </CardHeader>
            <CardContent>
              <ModelConfigForm />
            </CardContent>
          </Card>
        </div>
        <div className="space-y-6">
          <Card>
            <CardHeader>
              <CardTitle>Quick Links</CardTitle>
              <CardDescription>Jump to a section</CardDescription>
            </CardHeader>
            <CardContent className="flex flex-col gap-2">
              {quickLinks.map((link) => (
                 <Button key={link.href} variant="outline" className="w-full justify-start" asChild>
                    <Link href={link.href}>
                      <link.icon className="mr-2" />
                      {link.label}
                    </Link>
                 </Button>
              ))}
            </CardContent>
          </Card>
        </div>
      </div>
    </div>
  );
}
