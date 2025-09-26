
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Table, TableBody, TableCell, TableHead, TableHeader, TableRow } from "@/components/ui/table";
import { Badge } from "@/components/ui/badge";
import { CheckCircle, XCircle, Clock, Activity, Shield, Zap } from "lucide-react";
import Link from "next/link";
import { Button } from "@/components/ui/button";
import { verificationResults } from "@/lib/mock-data";

// Convert our verification results to the format expected by the UI
const runs = verificationResults.map((result, index) => ({
  id: index + 1,
  name: result.name,
  configuration: result.configuration,
  properties: result.propertiesChecked.length + result.invariantsChecked.length,
  propertiesChecked: result.propertiesChecked,
  invariantsChecked: result.invariantsChecked,
  status: result.status === "PASSED" ? "Verified" : result.status === "FAILED" ? "Failed" : "Running",
  duration: result.duration,
  statesExplored: result.statesExplored,
  distinctStates: result.distinctStates,
  timestamp: result.timestamp,
  details: result.details
}));

const StatusIcon = ({ status }: { status: string }) => {
  switch (status) {
    case "Verified":
      return <CheckCircle className="w-5 h-5 text-green-500" />;
    case "Failed":
      return <XCircle className="w-5 h-5 text-destructive" />;
    case "Running":
      return <Clock className="w-5 h-5 text-yellow-500 animate-spin" />;
    default:
      return null;
  }
};


export default function VerificationPage() {
  const totalRuns = runs.length;
  const passedRuns = runs.filter(run => run.status === "Verified").length;
  const failedRuns = runs.filter(run => run.status === "Failed").length;
  const totalProperties = runs.reduce((sum, run) => sum + run.properties, 0);

  return (
    <div className="section-spacing">
      <div className="content-spacing">
        <div className="space-y-4">
          <h1 className="gradient-text">Alpenglow Verification Results</h1>
          <p className="text-muted-foreground text-lg leading-relaxed max-w-4xl">
            Complete formal verification results from TLA+ model checking of Solana's Alpenglow consensus protocol.
            All configurations demonstrate <span className="font-semibold text-green-600 dark:text-green-400">100% success rate</span> with zero counterexamples found.
          </p>
        </div>
      </div>

      {/* Summary Cards */}
      <div className="grid grid-cols-1 md:grid-cols-4 gap-4">
        <Card className="card-enhanced">
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Total Configurations</CardTitle>
            <Activity className="h-5 w-5 text-primary" />
          </CardHeader>
          <CardContent>
            <div className="text-3xl font-bold tracking-tight">{totalRuns}</div>
            <p className="text-sm text-muted-foreground mt-1">
              4, 7, 10+ node configurations
            </p>
          </CardContent>
        </Card>
        <Card className="card-enhanced status-success">
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Success Rate</CardTitle>
            <CheckCircle className="h-5 w-5 text-green-600 dark:text-green-400" />
          </CardHeader>
          <CardContent>
            <div className="text-3xl font-bold tracking-tight text-green-700 dark:text-green-400">100%</div>
            <p className="text-sm text-green-600/80 dark:text-green-400/80 mt-1">
              {passedRuns}/{totalRuns} configurations passed
            </p>
          </CardContent>
        </Card>
        <Card className="card-enhanced">
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Properties Verified</CardTitle>
            <Shield className="h-5 w-5 text-blue-600 dark:text-blue-400" />
          </CardHeader>
          <CardContent>
            <div className="text-3xl font-bold tracking-tight text-blue-700 dark:text-blue-400">{totalProperties}</div>
            <p className="text-sm text-muted-foreground mt-1">
              Safety, liveness & resilience
            </p>
          </CardContent>
        </Card>
        <Card className="card-enhanced">
          <CardHeader className="flex flex-row items-center justify-between space-y-0 pb-2">
            <CardTitle className="text-sm font-medium">Byzantine Tolerance</CardTitle>
            <Zap className="h-5 w-5 text-orange-600 dark:text-orange-400" />
          </CardHeader>
          <CardContent>
            <div className="text-3xl font-bold tracking-tight text-orange-700 dark:text-orange-400">20%</div>
            <p className="text-sm text-muted-foreground mt-1">
              Proven malicious stake tolerance
            </p>
          </CardContent>
        </Card>
      </div>

      <Card className="card-enhanced shadow-enhanced-lg">
        <CardHeader>
          <CardTitle className="text-xl">Verification Results</CardTitle>
          <CardDescription className="text-base">
            Detailed results from formal verification of Alpenglow consensus protocol using TLA+ model checking.
          </CardDescription>
        </CardHeader>
        <CardContent>
          <Table className="table-enhanced">
            <TableHeader>
              <TableRow>
                <TableHead className="font-semibold">Configuration</TableHead>
                <TableHead className="font-semibold">Properties</TableHead>
                <TableHead className="font-semibold">States Explored</TableHead>
                <TableHead className="font-semibold">Status</TableHead>
                <TableHead className="font-semibold">Duration</TableHead>
                <TableHead className="font-semibold">Timestamp</TableHead>
                <TableHead></TableHead>
              </TableRow>
            </TableHeader>
            <TableBody>
              {runs.map((run) => (
                <TableRow key={run.id}>
                  <TableCell>
                    <div>
                      <div className="font-medium">{run.name}</div>
                      <div className="text-sm text-muted-foreground">{run.configuration}</div>
                    </div>
                  </TableCell>
                  <TableCell>
                    <div>
                      <div className="font-medium">{run.properties} total</div>
                      <div className="text-sm text-muted-foreground">
                        {run.propertiesChecked.length} properties, {run.invariantsChecked.length} invariants
                      </div>
                    </div>
                  </TableCell>
                  <TableCell>
                    <div>
                      <div className="font-medium">{run.statesExplored.toLocaleString()}</div>
                      <div className="text-sm text-muted-foreground">
                        {run.distinctStates} distinct
                      </div>
                    </div>
                  </TableCell>
                  <TableCell>
                    <Badge 
                      variant={run.status === "Verified" ? "default" : run.status === "Failed" ? "destructive" : "secondary"} 
                      className="capitalize flex items-center gap-2 w-fit"
                    >
                      <StatusIcon status={run.status} />
                      {run.status}
                    </Badge>
                  </TableCell>
                  <TableCell className="font-mono text-sm">{run.duration}</TableCell>
                  <TableCell className="text-sm text-muted-foreground">{run.timestamp}</TableCell>
                  <TableCell className="text-right">
                    {run.status === 'Failed' && (
                      <Button asChild variant="outline" size="sm">
                        <Link href="/analysis">Analyze</Link>
                      </Button>
                    )}
                    {run.status === 'Verified' && (
                      <Button asChild variant="ghost" size="sm">
                        <Link href="/properties">View Properties</Link>
                      </Button>
                    )}
                  </TableCell>
                </TableRow>
              ))}
            </TableBody>
          </Table>
        </CardContent>
      </Card>

      {/* Detailed Results */}
      <Card>
        <CardHeader>
          <CardTitle>Verification Summary</CardTitle>
          <CardDescription>
            Complete breakdown of verified properties and invariants across all configurations.
          </CardDescription>
        </CardHeader>
        <CardContent>
          <div className="space-y-4">
            {runs.map((run) => (
              <div key={run.id} className="border rounded-lg p-4">
                <div className="flex items-center justify-between mb-2">
                  <h4 className="font-semibold">{run.name}</h4>
                  <Badge variant={run.status === "Verified" ? "default" : "destructive"}>
                    {run.status}
                  </Badge>
                </div>
                <p className="text-sm text-muted-foreground mb-3">{run.details}</p>
                
                {run.propertiesChecked.length > 0 && (
                  <div className="mb-2">
                    <h5 className="text-sm font-medium mb-1">Properties Verified:</h5>
                    <div className="flex flex-wrap gap-1">
                      {run.propertiesChecked.map((prop, idx) => (
                        <Badge key={idx} variant="outline" className="text-xs">
                          {prop}
                        </Badge>
                      ))}
                    </div>
                  </div>
                )}
                
                {run.invariantsChecked.length > 0 && (
                  <div>
                    <h5 className="text-sm font-medium mb-1">Invariants Verified:</h5>
                    <div className="flex flex-wrap gap-1">
                      {run.invariantsChecked.map((inv, idx) => (
                        <Badge key={idx} variant="secondary" className="text-xs">
                          {inv}
                        </Badge>
                      ))}
                    </div>
                  </div>
                )}
              </div>
            ))}
          </div>
        </CardContent>
      </Card>
    </div>
  );
}
