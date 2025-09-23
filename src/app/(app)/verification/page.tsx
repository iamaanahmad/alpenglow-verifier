import { Card, CardContent, CardDescription, CardHeader, CardTitle } from "@/components/ui/card";
import { Table, TableBody, TableCell, TableHead, TableHeader, TableRow } from "@/components/ui/table";
import { Badge } from "@/components/ui/badge";
import { CheckCircle, XCircle, Clock } from "lucide-react";
import Link from "next/link";
import { Button } from "@/components/ui/button";

const runs = [
  { id: 1, name: "Small_Network_Test", properties: 3, status: "Verified", duration: "2m 15s" },
  { id: 2, name: "Network_Partition_4_Nodes", properties: 3, status: "Failed", duration: "5m 30s" },
  { id: 3, name: "Leader_Failure_10_Nodes", properties: 3, status: "Verified", duration: "12m 45s" },
  { id: 4, name: "High_Latency_Test", properties: 3, status: "Running", duration: "2m 1s" },
];

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
  return (
    <div className="space-y-6">
      <div className="space-y-2">
        <h1 className="text-3xl font-bold tracking-tight">Verification Runs</h1>
        <p className="text-muted-foreground">Results from running the TLC model checker on various configurations.</p>
      </div>
      <Card>
        <CardHeader>
          <CardTitle>Recent Runs</CardTitle>
          <CardDescription>A list of recent verification runs and their outcomes.</CardDescription>
        </CardHeader>
        <CardContent>
          <Table>
            <TableHeader>
              <TableRow>
                <TableHead>Model Name</TableHead>
                <TableHead>Properties Checked</TableHead>
                <TableHead>Status</TableHead>
                <TableHead>Duration</TableHead>
                <TableHead></TableHead>
              </TableRow>
            </TableHeader>
            <TableBody>
              {runs.map((run) => (
                <TableRow key={run.id}>
                  <TableCell className="font-medium">{run.name}</TableCell>
                  <TableCell>{run.properties}</TableCell>
                  <TableCell>
                    <Badge variant={run.status === "Verified" ? "default" : run.status === "Failed" ? "destructive" : "secondary"} className="capitalize flex items-center gap-2 w-fit">
                      <StatusIcon status={run.status} />
                      {run.status}
                    </Badge>
                  </TableCell>
                  <TableCell>{run.duration}</TableCell>
                  <TableCell className="text-right">
                    {run.status === 'Failed' && (
                        <Button asChild variant="outline" size="sm">
                            <Link href="/analysis">Analyze</Link>
                        </Button>
                    )}
                  </TableCell>
                </TableRow>
              ))}
            </TableBody>
          </Table>
        </CardContent>
      </Card>
    </div>
  );
}
