#!/usr/bin/env pwsh
# Comprehensive Alpenglow Verification Script
# Automated verification with result analysis and reporting

param(
    [string]$OutputDir = "verification_results",
    [switch]$GenerateReport = $true,
    [switch]$AnalyzeCounterexamples = $true,
    [int]$TimeoutMinutes = 30,
    [string]$LogLevel = "INFO"
)

# Configuration
$TLA_TOOLS = "tla2tools.jar"
$TIMESTAMP = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$RESULTS_DIR = "$OutputDir/$TIMESTAMP"

# Test configurations with metadata
$TEST_CONFIGS = @(
    @{
        Name = "4-Node Basic"
        ConfigFile = "MC_4Nodes.cfg"
        SpecFile = "MC_4Nodes.tla"
        Description = "Small scale exhaustive verification"
        ExpectedDuration = "5 minutes"
        Priority = "High"
        Category = "Basic"
    },
    @{
        Name = "7-Node Medium"
        ConfigFile = "MC_7Nodes.cfg" 
        SpecFile = "MC_7Nodes.tla"
        Description = "Medium scale targeted verification"
        ExpectedDuration = "15 minutes"
        Priority = "High"
        Category = "Scalability"
    },
    @{
        Name = "10-Node Large"
        ConfigFile = "MC_10Nodes.cfg"
        SpecFile = "MC_10Nodes.tla"
        Description = "Large scale statistical verification"
        ExpectedDuration = "25 minutes"
        Priority = "Medium"
        Category = "Performance"
    },
    @{
        Name = "Byzantine Test"
        ConfigFile = "MC_Byzantine_Test.cfg"
        SpecFile = "MC_Byzantine_Test.tla"
        Description = "Byzantine fault tolerance verification"
        ExpectedDuration = "10 minutes"
        Priority = "Critical"
        Category = "Security"
    },
    @{
        Name = "Certificate Test"
        ConfigFile = "MC_Certificate_Test.cfg"
        SpecFile = "MC_Certificate_Test.tla"
        Description = "Certificate aggregation verification"
        ExpectedDuration = "8 minutes"
        Priority = "High"
        Category = "Correctness"
    },
    @{
        Name = "Statistical Test"
        ConfigFile = "MC_Statistical_Test.cfg"
        SpecFile = "MC_Statistical_Test.tla"
        Description = "Statistical sampling verification"
        ExpectedDuration = "20 minutes"
        Priority = "Medium"
        Category = "Statistical"
    },
    @{
        Name = "Enhanced Statistical"
        ConfigFile = "MC_Statistical_Enhanced.cfg"
        SpecFile = "MC_Statistical_Enhanced.tla"
        Description = "Enhanced statistical sampling with Monte Carlo"
        ExpectedDuration = "25 minutes"
        Priority = "Medium"
        Category = "Statistical"
    }
)

# Property categories for analysis
$PROPERTY_CATEGORIES = @{
    "Safety" = @("NoConflictingBlocksFinalized", "CertificateUniqueness", "NoEquivocation", "ForkPrevention", "ChainConsistencyUnderByzantineFaults", "ByzantineFaultTolerance")
    "Liveness" = @("ProgressWithHonestSupermajority", "FastPathCompletion", "SlowPathCompletion", "BoundedFinalizationTimes", "ProgressWithTimeouts", "TimelyFinalizationUnderGoodConditions")
    "Resilience" = @("SafetyWithByzantineStake", "LivenessWithOfflineStake", "RecoveryFromPartition", "TwentyPlusTwentyResilienceModel")
    "Invariants" = @("SlotBounds", "ValidByzantineStake", "CertificateAggregationInvariants", "RelayGraphConsistency", "WindowManagementInvariants", "TimeoutConsistency")
}

# Initialize results tracking
$VERIFICATION_RESULTS = @()
$PROPERTY_RESULTS = @{}
$COUNTEREXAMPLES = @()
$PERFORMANCE_METRICS = @{}

function Write-Log {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    Write-Host $logMessage
    Add-Content -Path "$RESULTS_DIR/verification.log" -Value $logMessage
}

function Initialize-ResultsDirectory {
    Write-Log "Initializing results directory: $RESULTS_DIR"
    if (Test-Path $RESULTS_DIR) {
        Remove-Item -Recurse -Force $RESULTS_DIR
    }
    New-Item -ItemType Directory -Path $RESULTS_DIR -Force | Out-Null
    New-Item -ItemType Directory -Path "$RESULTS_DIR/logs" -Force | Out-Null
    New-Item -ItemType Directory -Path "$RESULTS_DIR/counterexamples" -Force | Out-Null
    New-Item -ItemType Directory -Path "$RESULTS_DIR/reports" -Force | Out-Null
}

function Test-Prerequisites {
    Write-Log "Checking prerequisites..."
    
    if (-not (Test-Path $TLA_TOOLS)) {
        Write-Log "ERROR: TLA+ tools not found at $TLA_TOOLS" "ERROR"
        return $false
    }
    
    if (-not (Get-Command java -ErrorAction SilentlyContinue)) {
        Write-Log "ERROR: Java not found in PATH" "ERROR"
        return $false
    }
    
    # Check if all config files exist
    foreach ($config in $TEST_CONFIGS) {
        if (-not (Test-Path $config.ConfigFile)) {
            Write-Log "ERROR: Configuration file not found: $($config.ConfigFile)" "ERROR"
            return $false
        }
    }
    
    Write-Log "All prerequisites satisfied"
    return $true
}

function Run-TLCVerification {
    param(
        [hashtable]$Config,
        [int]$TimeoutSeconds = 1800
    )
    
    $startTime = Get-Date
    Write-Log "Starting verification: $($Config.Name)" "INFO"
    Write-Log "Configuration: $($Config.ConfigFile), Expected duration: $($Config.ExpectedDuration)"
    
    $logFile = "$RESULTS_DIR/logs/$($Config.Name -replace ' ', '_').log"
    $errorFile = "$RESULTS_DIR/logs/$($Config.Name -replace ' ', '_')_error.log"
    
    try {
        # Run TLC with timeout
        $processArgs = @(
            "-XX:+UseParallelGC"
            "-Xmx4g"
            "-jar", $TLA_TOOLS
            "-config", $Config.ConfigFile
            $Config.SpecFile
        )
        
        Write-Log "Executing: java $($processArgs -join ' ')"
        
        $process = Start-Process -FilePath "java" -ArgumentList $processArgs -Wait -PassThru -NoNewWindow -RedirectStandardOutput $logFile -RedirectStandardError $errorFile
        
        $endTime = Get-Date
        $duration = $endTime - $startTime
        
        # Parse results
        $result = Parse-TLCOutput -LogFile $logFile -ErrorFile $errorFile -Config $Config -Duration $duration
        
        if ($process.ExitCode -eq 0) {
            Write-Log "✓ $($Config.Name) completed successfully in $($duration.ToString('mm\:ss'))" "SUCCESS"
            $result.Status = "PASSED"
        } else {
            Write-Log "✗ $($Config.Name) failed with exit code $($process.ExitCode) after $($duration.ToString('mm\:ss'))" "ERROR"
            $result.Status = "FAILED"
            
            # Analyze counterexamples if verification failed
            if ($AnalyzeCounterexamples) {
                Analyze-Counterexamples -LogFile $logFile -Config $Config
            }
        }
        
        return $result
        
    } catch {
        $endTime = Get-Date
        $duration = $endTime - $startTime
        Write-Log "Exception during verification of $($Config.Name): $($_.Exception.Message)" "ERROR"
        
        return @{
            ConfigName = $Config.Name
            Status = "ERROR"
            Duration = $duration
            ExitCode = -1
            PropertiesVerified = @()
            InvariantsChecked = @()
            StatesExplored = 0
            Error = $_.Exception.Message
        }
    }
}

function Parse-TLCOutput {
    param(
        [string]$LogFile,
        [string]$ErrorFile,
        [hashtable]$Config,
        [timespan]$Duration
    )
    
    $result = @{
        ConfigName = $Config.Name
        Category = $Config.Category
        Priority = $Config.Priority
        Duration = $Duration
        PropertiesVerified = @()
        InvariantsChecked = @()
        StatesExplored = 0
        DistinctStates = 0
        QueueSize = 0
        Error = $null
        Warnings = @()
        CounterexampleFound = $false
        CounterexampleFile = $null
    }
    
    if (Test-Path $LogFile) {
        $logContent = Get-Content $LogFile -Raw
        
        # Extract states explored
        if ($logContent -match "(\d+) states generated, (\d+) distinct states found") {
            $result.StatesExplored = [int]$matches[1]
            $result.DistinctStates = [int]$matches[2]
        }
        
        # Extract properties and invariants
        $lines = Get-Content $LogFile
        foreach ($line in $lines) {
            if ($line -match "Checking property (.+)") {
                $result.PropertiesVerified += $matches[1]
            }
            if ($line -match "Checking invariant (.+)") {
                $result.InvariantsChecked += $matches[1]
            }
            if ($line -match "Warning:") {
                $result.Warnings += $line
            }
            if ($line -match "Error:") {
                $result.Error = $line
            }
            if ($line -match "Counterexample") {
                $result.CounterexampleFound = $true
            }
        }
    }
    
    if (Test-Path $ErrorFile) {
        $errorContent = Get-Content $ErrorFile -Raw
        if ($errorContent.Trim() -ne "") {
            $result.Error = $errorContent
        }
    }
    
    return $result
}

function Analyze-Counterexamples {
    param(
        [string]$LogFile,
        [hashtable]$Config
    )
    
    Write-Log "Analyzing counterexamples for $($Config.Name)..."
    
    if (-not (Test-Path $LogFile)) {
        return
    }
    
    $logContent = Get-Content $LogFile -Raw
    
    # Look for counterexample traces
    if ($logContent -match "Error: Invariant (.+) is violated") {
        $violatedInvariant = $matches[1]
        Write-Log "Invariant violation found: $violatedInvariant" "WARNING"
        
        # Extract counterexample trace
        $counterexampleFile = "$RESULTS_DIR/counterexamples/$($Config.Name -replace ' ', '_')_$violatedInvariant.trace"
        
        # Find the trace in the log
        $lines = Get-Content $LogFile
        $inTrace = $false
        $traceLines = @()
        
        foreach ($line in $lines) {
            if ($line -match "The behavior up to this point is:") {
                $inTrace = $true
                continue
            }
            if ($inTrace) {
                if ($line -match "^$" -or $line -match "^TLC") {
                    break
                }
                $traceLines += $line
            }
        }
        
        if ($traceLines.Count -gt 0) {
            $traceContent = @"
Counterexample Analysis for $($Config.Name)
Violated Invariant: $violatedInvariant
Generated: $(Get-Date)

Trace:
$($traceLines -join "`n")

Analysis:
$(Analyze-TraceContent -TraceLines $traceLines -ViolatedProperty $violatedInvariant)
"@
            Set-Content -Path $counterexampleFile -Value $traceContent
            Write-Log "Counterexample saved to: $counterexampleFile"
            
            $COUNTEREXAMPLES += @{
                Config = $Config.Name
                Property = $violatedInvariant
                TraceFile = $counterexampleFile
                Analysis = Analyze-TraceContent -TraceLines $traceLines -ViolatedProperty $violatedInvariant
            }
        }
    }
}

function Analyze-TraceContent {
    param(
        [string[]]$TraceLines,
        [string]$ViolatedProperty
    )
    
    $analysis = @()
    
    # Basic trace analysis
    $analysis += "Trace Length: $($TraceLines.Count) steps"
    
    # Look for specific patterns based on violated property
    switch -Regex ($ViolatedProperty) {
        "NoConflictingBlocksFinalized" {
            $analysis += "Analysis: Multiple blocks may have been finalized in the same slot"
            $analysis += "Recommendation: Check certificate aggregation logic and Byzantine behavior"
        }
        "CertificateUniqueness" {
            $analysis += "Analysis: Multiple certificates generated for the same slot"
            $analysis += "Recommendation: Review certificate generation conditions and timing"
        }
        "ByzantineFaultTolerance" {
            $analysis += "Analysis: Byzantine nodes may have exceeded fault tolerance limits"
            $analysis += "Recommendation: Verify Byzantine stake calculations and constraints"
        }
        ".*Liveness.*|.*Progress.*" {
            $analysis += "Analysis: System failed to make progress within expected bounds"
            $analysis += "Recommendation: Check timeout mechanisms and responsiveness assumptions"
        }
        default {
            $analysis += "Analysis: Property violation detected - manual review required"
            $analysis += "Recommendation: Examine trace for state transitions leading to violation"
        }
    }
    
    return $analysis -join "`n"
}

function Generate-ComprehensiveReport {
    Write-Log "Generating comprehensive verification report..."
    
    $reportFile = "$RESULTS_DIR/reports/comprehensive_report.html"
    $jsonReportFile = "$RESULTS_DIR/reports/verification_results.json"
    
    # Generate JSON report for programmatic access
    $jsonReport = @{
        Timestamp = $TIMESTAMP
        Summary = Get-VerificationSummary
        Results = $VERIFICATION_RESULTS
        PropertyAnalysis = Get-PropertyAnalysis
        PerformanceMetrics = $PERFORMANCE_METRICS
        Counterexamples = $COUNTEREXAMPLES
        Recommendations = Get-Recommendations
    }
    
    $jsonReport | ConvertTo-Json -Depth 10 | Set-Content $jsonReportFile
    Write-Log "JSON report saved to: $jsonReportFile"
    
    # Generate HTML report
    $htmlReport = Generate-HTMLReport -Results $VERIFICATION_RESULTS
    Set-Content -Path $reportFile -Value $htmlReport
    Write-Log "HTML report saved to: $reportFile"
    
    # Generate summary report
    $summaryFile = "$RESULTS_DIR/reports/summary.txt"
    $summary = Generate-SummaryReport
    Set-Content -Path $summaryFile -Value $summary
    Write-Log "Summary report saved to: $summaryFile"
}

function Get-VerificationSummary {
    $total = $VERIFICATION_RESULTS.Count
    $passed = ($VERIFICATION_RESULTS | Where-Object { $_.Status -eq "PASSED" }).Count
    $failed = ($VERIFICATION_RESULTS | Where-Object { $_.Status -eq "FAILED" }).Count
    $errors = ($VERIFICATION_RESULTS | Where-Object { $_.Status -eq "ERROR" }).Count
    
    return @{
        TotalConfigurations = $total
        Passed = $passed
        Failed = $failed
        Errors = $errors
        SuccessRate = if ($total -gt 0) { [math]::Round(($passed / $total) * 100, 2) } else { 0 }
        TotalDuration = ($VERIFICATION_RESULTS | Measure-Object -Property Duration -Sum).Sum
    }
}

function Get-PropertyAnalysis {
    $propertyStats = @{}
    
    foreach ($category in $PROPERTY_CATEGORIES.Keys) {
        $categoryProperties = $PROPERTY_CATEGORIES[$category]
        $propertyStats[$category] = @{
            Properties = $categoryProperties
            VerifiedCount = 0
            FailedCount = 0
            TotalTests = 0
        }
        
        foreach ($result in $VERIFICATION_RESULTS) {
            foreach ($prop in $categoryProperties) {
                if ($result.PropertiesVerified -contains $prop -or $result.InvariantsChecked -contains $prop) {
                    $propertyStats[$category].TotalTests++
                    if ($result.Status -eq "PASSED") {
                        $propertyStats[$category].VerifiedCount++
                    } else {
                        $propertyStats[$category].FailedCount++
                    }
                }
            }
        }
    }
    
    return $propertyStats
}

function Get-Recommendations {
    $recommendations = @()
    
    # Analyze results and generate recommendations
    $failedConfigs = $VERIFICATION_RESULTS | Where-Object { $_.Status -ne "PASSED" }
    
    if ($failedConfigs.Count -eq 0) {
        $recommendations += "✓ All verification tests passed successfully!"
        $recommendations += "✓ The Alpenglow protocol implementation meets all specified safety, liveness, and resilience properties."
        $recommendations += "✓ Ready for hackathon submission with comprehensive formal verification."
    } else {
        $recommendations += "⚠ Some verification tests failed or encountered errors:"
        
        foreach ($config in $failedConfigs) {
            $recommendations += "  - $($config.ConfigName): $($config.Status)"
            if ($config.Error) {
                $recommendations += "    Error: $($config.Error)"
            }
        }
        
        $recommendations += ""
        $recommendations += "Recommended actions:"
        $recommendations += "1. Review counterexample traces in the counterexamples directory"
        $recommendations += "2. Check model constraints and optimization settings"
        $recommendations += "3. Verify TLA+ specification correctness"
        $recommendations += "4. Consider adjusting timeout values for large configurations"
    }
    
    # Performance recommendations
    $slowConfigs = $VERIFICATION_RESULTS | Where-Object { $_.Duration.TotalMinutes -gt 20 }
    if ($slowConfigs.Count -gt 0) {
        $recommendations += ""
        $recommendations += "Performance optimization suggestions:"
        foreach ($config in $slowConfigs) {
            $recommendations += "  - $($config.ConfigName) took $($config.Duration.ToString('mm\:ss')) - consider stronger state constraints"
        }
    }
    
    return $recommendations
}

function Generate-HTMLReport {
    param([array]$Results)
    
    $html = @"
<!DOCTYPE html>
<html>
<head>
    <title>Alpenglow Verification Report - $TIMESTAMP</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background: #2c3e50; color: white; padding: 20px; border-radius: 5px; }
        .summary { background: #ecf0f1; padding: 15px; margin: 20px 0; border-radius: 5px; }
        .config { border: 1px solid #bdc3c7; margin: 10px 0; padding: 15px; border-radius: 5px; }
        .passed { border-left: 5px solid #27ae60; }
        .failed { border-left: 5px solid #e74c3c; }
        .error { border-left: 5px solid #f39c12; }
        .properties { margin: 10px 0; }
        .property { display: inline-block; margin: 2px; padding: 4px 8px; border-radius: 3px; font-size: 12px; }
        .prop-verified { background: #d5f4e6; color: #27ae60; }
        .prop-failed { background: #fadbd8; color: #e74c3c; }
        table { width: 100%; border-collapse: collapse; margin: 20px 0; }
        th, td { border: 1px solid #bdc3c7; padding: 8px; text-align: left; }
        th { background: #34495e; color: white; }
        .metric { display: inline-block; margin: 10px; padding: 10px; background: #f8f9fa; border-radius: 5px; }
    </style>
</head>
<body>
    <div class="header">
        <h1>Enhanced Alpenglow Formal Verification Report</h1>
        <p>Generated: $(Get-Date)</p>
        <p>Verification Run: $TIMESTAMP</p>
    </div>
    
    <div class="summary">
        <h2>Verification Summary</h2>
        $(Generate-SummaryHTML)
    </div>
    
    <div class="results">
        <h2>Configuration Results</h2>
        $(Generate-ResultsHTML -Results $Results)
    </div>
    
    <div class="properties">
        <h2>Property Analysis</h2>
        $(Generate-PropertyHTML)
    </div>
    
    <div class="performance">
        <h2>Performance Metrics</h2>
        $(Generate-PerformanceHTML)
    </div>
    
    $(if ($COUNTEREXAMPLES.Count -gt 0) { Generate-CounterexampleHTML })
    
    <div class="recommendations">
        <h2>Recommendations</h2>
        $(Generate-RecommendationsHTML)
    </div>
</body>
</html>
"@
    
    return $html
}

function Generate-SummaryHTML {
    $summary = Get-VerificationSummary
    return @"
    <div class="metric">
        <strong>Total Configurations:</strong> $($summary.TotalConfigurations)
    </div>
    <div class="metric">
        <strong>Passed:</strong> $($summary.Passed)
    </div>
    <div class="metric">
        <strong>Failed:</strong> $($summary.Failed)
    </div>
    <div class="metric">
        <strong>Errors:</strong> $($summary.Errors)
    </div>
    <div class="metric">
        <strong>Success Rate:</strong> $($summary.SuccessRate)%
    </div>
    <div class="metric">
        <strong>Total Duration:</strong> $($summary.TotalDuration.ToString('hh\:mm\:ss'))
    </div>
"@
}

function Generate-ResultsHTML {
    param([array]$Results)
    
    $html = ""
    foreach ($result in $Results) {
        $statusClass = $result.Status.ToLower()
        $html += @"
        <div class="config $statusClass">
            <h3>$($result.ConfigName) - $($result.Status)</h3>
            <p><strong>Category:</strong> $($result.Category) | <strong>Priority:</strong> $($result.Priority)</p>
            <p><strong>Duration:</strong> $($result.Duration.ToString('mm\:ss')) | <strong>States Explored:</strong> $($result.StatesExplored)</p>
            
            $(if ($result.PropertiesVerified.Count -gt 0) {
                "<div class='properties'><strong>Properties Verified:</strong><br>" +
                ($result.PropertiesVerified | ForEach-Object { "<span class='property prop-verified'>$_</span>" }) -join "" +
                "</div>"
            })
            
            $(if ($result.InvariantsChecked.Count -gt 0) {
                "<div class='properties'><strong>Invariants Checked:</strong><br>" +
                ($result.InvariantsChecked | ForEach-Object { "<span class='property prop-verified'>$_</span>" }) -join "" +
                "</div>"
            })
            
            $(if ($result.Error) { "<p><strong>Error:</strong> $($result.Error)</p>" })
            $(if ($result.Warnings.Count -gt 0) { 
                "<p><strong>Warnings:</strong></p><ul>" +
                ($result.Warnings | ForEach-Object { "<li>$_</li>" }) -join "" +
                "</ul>"
            })
        </div>
"@
    }
    
    return $html
}

function Generate-PropertyHTML {
    $propertyAnalysis = Get-PropertyAnalysis
    $html = "<table><tr><th>Category</th><th>Properties</th><th>Verified</th><th>Failed</th><th>Success Rate</th></tr>"
    
    foreach ($category in $propertyAnalysis.Keys) {
        $stats = $propertyAnalysis[$category]
        $successRate = if ($stats.TotalTests -gt 0) { [math]::Round(($stats.VerifiedCount / $stats.TotalTests) * 100, 1) } else { 0 }
        
        $html += "<tr>"
        $html += "<td>$category</td>"
        $html += "<td>$($stats.Properties.Count)</td>"
        $html += "<td>$($stats.VerifiedCount)</td>"
        $html += "<td>$($stats.FailedCount)</td>"
        $html += "<td>$successRate%</td>"
        $html += "</tr>"
    }
    
    $html += "</table>"
    return $html
}

function Generate-PerformanceHTML {
    $html = "<table><tr><th>Configuration</th><th>Duration</th><th>States Explored</th><th>States/Second</th></tr>"
    
    foreach ($result in $VERIFICATION_RESULTS) {
        $statesPerSecond = if ($result.Duration.TotalSeconds -gt 0) { 
            [math]::Round($result.StatesExplored / $result.Duration.TotalSeconds, 0) 
        } else { 0 }
        
        $html += "<tr>"
        $html += "<td>$($result.ConfigName)</td>"
        $html += "<td>$($result.Duration.ToString('mm\:ss'))</td>"
        $html += "<td>$($result.StatesExplored)</td>"
        $html += "<td>$statesPerSecond</td>"
        $html += "</tr>"
    }
    
    $html += "</table>"
    return $html
}

function Generate-CounterexampleHTML {
    $html = "<div class='counterexamples'><h2>Counterexamples Found</h2>"
    
    foreach ($ce in $COUNTEREXAMPLES) {
        $html += @"
        <div class="config failed">
            <h3>$($ce.Config) - $($ce.Property)</h3>
            <p><strong>Trace File:</strong> $($ce.TraceFile)</p>
            <p><strong>Analysis:</strong></p>
            <pre>$($ce.Analysis)</pre>
        </div>
"@
    }
    
    $html += "</div>"
    return $html
}

function Generate-RecommendationsHTML {
    $recommendations = Get-Recommendations
    $html = "<ul>"
    foreach ($rec in $recommendations) {
        $html += "<li>$rec</li>"
    }
    $html += "</ul>"
    return $html
}

function Generate-SummaryReport {
    $summary = Get-VerificationSummary
    $propertyAnalysis = Get-PropertyAnalysis
    $recommendations = Get-Recommendations
    
    return @"
Enhanced Alpenglow Formal Verification Summary
Generated: $(Get-Date)
Verification Run: $TIMESTAMP

OVERALL RESULTS:
================
Total Configurations: $($summary.TotalConfigurations)
Passed: $($summary.Passed)
Failed: $($summary.Failed)
Errors: $($summary.Errors)
Success Rate: $($summary.SuccessRate)%
Total Duration: $($summary.TotalDuration.ToString('hh\:mm\:ss'))

PROPERTY VERIFICATION:
=====================
$($propertyAnalysis.Keys | ForEach-Object {
    $stats = $propertyAnalysis[$_]
    "$_`: $($stats.VerifiedCount)/$($stats.TotalTests) verified ($([math]::Round(($stats.VerifiedCount / [math]::Max($stats.TotalTests, 1)) * 100, 1))%)"
} | Out-String)

CONFIGURATION DETAILS:
=====================
$($VERIFICATION_RESULTS | ForEach-Object {
    "$($_.ConfigName): $($_.Status) - $($_.Duration.ToString('mm\:ss')) - $($_.StatesExplored) states"
} | Out-String)

RECOMMENDATIONS:
===============
$($recommendations -join "`n")

HACKATHON READINESS:
===================
$(if ($summary.SuccessRate -eq 100) {
    "✓ READY FOR SUBMISSION: All verification tests passed successfully!"
} else {
    "⚠ NEEDS ATTENTION: Some tests failed - review counterexamples and fix issues"
})
"@
}

# Main execution
function Main {
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Enhanced Alpenglow Comprehensive Verification" -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    
    Initialize-ResultsDirectory
    
    if (-not (Test-Prerequisites)) {
        Write-Log "Prerequisites check failed. Exiting." "ERROR"
        exit 1
    }
    
    Write-Log "Starting comprehensive verification of $($TEST_CONFIGS.Count) configurations..."
    
    # Run all verifications
    foreach ($config in $TEST_CONFIGS) {
        $result = Run-TLCVerification -Config $config -TimeoutSeconds ($TimeoutMinutes * 60)
        $VERIFICATION_RESULTS += $result
        
        # Update performance metrics
        $PERFORMANCE_METRICS[$config.Name] = @{
            Duration = $result.Duration
            StatesExplored = $result.StatesExplored
            StatesPerSecond = if ($result.Duration.TotalSeconds -gt 0) { $result.StatesExplored / $result.Duration.TotalSeconds } else { 0 }
        }
    }
    
    # Generate comprehensive report
    if ($GenerateReport) {
        Generate-ComprehensiveReport
    }
    
    # Final summary
    $summary = Get-VerificationSummary
    Write-Host ""
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Verification Complete!" -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Results: $($summary.Passed)/$($summary.TotalConfigurations) passed ($($summary.SuccessRate)%)" -ForegroundColor $(if ($summary.SuccessRate -eq 100) { "Green" } else { "Yellow" })
    Write-Host "Duration: $($summary.TotalDuration.ToString('hh\:mm\:ss'))"
    Write-Host "Reports saved to: $RESULTS_DIR"
    
    if ($summary.SuccessRate -eq 100) {
        Write-Host "🎉 All tests passed! Ready for hackathon submission!" -ForegroundColor Green
    } else {
        Write-Host "⚠ Some tests failed. Check reports for details." -ForegroundColor Yellow
    }
}

# Execute main function
Main