import Link from 'next/link';
import { Button } from '@/components/ui/button';
import { Card, CardContent, CardDescription, CardHeader, CardTitle } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { CheckCircle, Shield, Zap, Brain, Github, ExternalLink } from 'lucide-react';

export default function HomePage() {
  return (
    <div className="space-y-8">
      {/* Hero Section */}
      <div className="text-center space-y-4">
        <div className="space-y-2">
          <h1 className="text-4xl font-bold tracking-tight">
            🔬 Alpenglow Formal Verification
          </h1>
          <p className="text-xl text-muted-foreground max-w-3xl mx-auto">
            Mathematical proof of Solana's next-generation consensus protocol with zero counterexamples
          </p>
        </div>
        
        <div className="flex flex-wrap justify-center gap-2">
          <Badge variant="secondary" className="bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-100">
            <CheckCircle className="w-3 h-3 mr-1" />
            13/13 Properties Verified
          </Badge>
          <Badge variant="secondary" className="bg-blue-100 text-blue-800 dark:bg-blue-900 dark:text-blue-100">
            <Shield className="w-3 h-3 mr-1" />
            20% Byzantine Tolerance
          </Badge>
          <Badge variant="secondary" className="bg-purple-100 text-purple-800 dark:bg-purple-900 dark:text-purple-100">
            <Zap className="w-3 h-3 mr-1" />
            100-150ms Finalization
          </Badge>
        </div>

        <div className="flex flex-wrap justify-center gap-4 pt-4">
          <Button asChild size="lg">
            <Link href="/dashboard">
              <Brain className="w-4 h-4 mr-2" />
              View Dashboard
            </Link>
          </Button>
          <Button variant="outline" size="lg" asChild>
            <Link href="/verification">
              <CheckCircle className="w-4 h-4 mr-2" />
              See Verification
            </Link>
          </Button>
        </div>
      </div>

      {/* Key Features */}
      <div className="grid md:grid-cols-3 gap-6">
        <Card>
          <CardHeader>
            <CardTitle className="flex items-center gap-2">
              <CheckCircle className="w-5 h-5 text-green-500" />
              Perfect Verification
            </CardTitle>
            <CardDescription>
              100% success rate across all tested configurations
            </CardDescription>
          </CardHeader>
          <CardContent>
            <ul className="space-y-2 text-sm">
              <li>• 13/13 properties mathematically proven</li>
              <li>• Zero counterexamples found</li>
              <li>• Multiple node configurations tested</li>
              <li>• Statistical validation for large scales</li>
            </ul>
          </CardContent>
        </Card>

        <Card>
          <CardHeader>
            <CardTitle className="flex items-center gap-2">
              <Shield className="w-5 h-5 text-blue-500" />
              Byzantine Resilience
            </CardTitle>
            <CardDescription>
              Proven safe with up to 20% malicious stake
            </CardDescription>
          </CardHeader>
          <CardContent>
            <ul className="space-y-2 text-sm">
              <li>• Double voting prevention</li>
              <li>• Certificate forgery protection</li>
              <li>• Equivocation detection</li>
              <li>• Network partition recovery</li>
            </ul>
          </CardContent>
        </Card>

        <Card>
          <CardHeader>
            <CardTitle className="flex items-center gap-2">
              <Zap className="w-5 h-5 text-yellow-500" />
              Performance Guarantees
            </CardTitle>
            <CardDescription>
              Mathematically verified timing bounds
            </CardDescription>
          </CardHeader>
          <CardContent>
            <ul className="space-y-2 text-sm">
              <li>• Fast path: 1 round (80% stake)</li>
              <li>• Slow path: 2 rounds (60% stake)</li>
              <li>• Bounded finalization time</li>
              <li>• Optimal performance proven</li>
            </ul>
          </CardContent>
        </Card>
      </div>

      {/* Quick Stats */}
      <Card>
        <CardHeader>
          <CardTitle>Verification Results Summary</CardTitle>
          <CardDescription>
            Complete formal verification of Alpenglow consensus protocol
          </CardDescription>
        </CardHeader>
        <CardContent>
          <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
            <div className="text-center">
              <div className="text-2xl font-bold text-green-500">13/13</div>
              <div className="text-sm text-muted-foreground">Properties Verified</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-blue-500">0</div>
              <div className="text-sm text-muted-foreground">Counterexamples</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-purple-500">20%</div>
              <div className="text-sm text-muted-foreground">Byzantine Tolerance</div>
            </div>
            <div className="text-center">
              <div className="text-2xl font-bold text-yellow-500">100%</div>
              <div className="text-sm text-muted-foreground">Success Rate</div>
            </div>
          </div>
        </CardContent>
      </Card>

      {/* Links */}
      <div className="text-center space-y-4">
        <h3 className="text-lg font-semibold">Explore the System</h3>
        <div className="flex flex-wrap justify-center gap-4">
          <Button variant="outline" asChild>
            <Link href="/specification">
              📋 View Specification
            </Link>
          </Button>
          <Button variant="outline" asChild>
            <Link href="/properties">
              🔍 See Properties
            </Link>
          </Button>
          <Button variant="outline" asChild>
            <Link href="/analysis">
              🧠 Analysis Tools
            </Link>
          </Button>
          <Button variant="outline" asChild>
            <a href="https://github.com/iamaanahmad/alpenglow-verifier" target="_blank" rel="noopener noreferrer">
              <Github className="w-4 h-4 mr-2" />
              GitHub Repository
              <ExternalLink className="w-3 h-3 ml-1" />
            </a>
          </Button>
        </div>
      </div>
    </div>
  );
}