#!/usr/bin/env pwsh
# Complete Alpenglow Verification Suite
# Runs comprehensive verification and generates detailed reports

param(
    [int]$TimeoutMinutes = 60,
    [switch]$SkipCounterexampleAnalysis = $false,
    [switch]$SkipReportGeneration = $false,
    [string]$OutputDir = "verification_suite_results"
)

function Write-SuiteLog {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    Write-Host $logMessage
}

function Main {
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Complete Alpenglow Verification Suite" -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host ""
    
    $startTime = Get-Date
    $overallSuccess = $true
    
    # Step 1: Run comprehensive verification
    Write-SuiteLog "Step 1/3: Running comprehensive verification..."
    Write-Host "[1/3] Running comprehensive verification..." -ForegroundColor Yellow
    
    try {
        $verifyResult = & .\verify_comprehensive.ps1 -TimeoutMinutes $TimeoutMinutes -GenerateReport $true -AnalyzeCounterexamples $true
        if ($LASTEXITCODE -eq 0) {
            Write-SuiteLog "Comprehensive verification completed successfully" "SUCCESS"
        } else {
            Write-SuiteLog "Comprehensive verification completed with issues" "WARNING"
            $overallSuccess = $false
        }
    } catch {
        Write-SuiteLog "Comprehensive verification failed: $($_.Exception.Message)" "ERROR"
        $overallSuccess = $false
    }
    
    Write-Host ""
    
    # Step 2: Analyze counterexamples
    if (-not $SkipCounterexampleAnalysis) {
        Write-SuiteLog "Step 2/3: Analyzing counterexamples..."
        Write-Host "[2/3] Analyzing counterexamples..." -ForegroundColor Yellow
        
        try {
            $ceResult = & .\analyze_counterexamples.ps1 -DetailedAnalysis -OutputDir "counterexample_analysis"
            if ($LASTEXITCODE -eq 0) {
                Write-SuiteLog "Counterexample analysis completed" "SUCCESS"
            } else {
                Write-SuiteLog "Counterexample analysis completed with warnings" "WARNING"
            }
        } catch {
            Write-SuiteLog "Counterexample analysis failed: $($_.Exception.Message)" "WARNING"
        }
    } else {
        Write-SuiteLog "Step 2/3: Skipping counterexample analysis (as requested)"
    }
    
    Write-Host ""
    
    # Step 3: Generate comprehensive report
    if (-not $SkipReportGeneration) {
        Write-SuiteLog "Step 3/3: Generating comprehensive report..."
        Write-Host "[3/3] Generating comprehensive report..." -ForegroundColor Yellow
        
        try {
            $reportResult = & .\generate_verification_report.ps1 -IncludeProofStatus -IncludePerformanceMetrics -GenerateJSON
            if ($LASTEXITCODE -eq 0) {
                Write-SuiteLog "Report generation completed successfully" "SUCCESS"
            } else {
                Write-SuiteLog "Report generation completed with warnings" "WARNING"
            }
        } catch {
            Write-SuiteLog "Report generation failed: $($_.Exception.Message)" "WARNING"
        }
    } else {
        Write-SuiteLog "Step 3/3: Skipping report generation (as requested)"
    }
    
    # Final summary
    $endTime = Get-Date
    $totalDuration = $endTime - $startTime
    
    Write-Host ""
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Verification Suite Complete!" -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host "Total Duration: $($totalDuration.ToString('hh\:mm\:ss'))" -ForegroundColor White
    Write-Host "Overall Status: $(if ($overallSuccess) { "✅ SUCCESS" } else { "⚠️ COMPLETED WITH ISSUES" })" -ForegroundColor $(if ($overallSuccess) { "Green" } else { "Yellow" })
    Write-Host ""
    
    Write-Host "Generated Outputs:" -ForegroundColor White
    
    # Check for verification results
    $verificationDirs = Get-ChildItem -Path "verification_results" -Directory -ErrorAction SilentlyContinue | Sort-Object Name -Descending
    if ($verificationDirs.Count -gt 0) {
        $latestVerification = $verificationDirs[0].FullName
        Write-Host "📁 Verification Results: $latestVerification" -ForegroundColor Cyan
        
        # List key files
        $summaryFile = Join-Path $latestVerification "reports/summary.txt"
        if (Test-Path $summaryFile) {
            Write-Host "📄 Summary Report: $summaryFile" -ForegroundColor Cyan
        }
        
        $logDir = Join-Path $latestVerification "logs"
        if (Test-Path $logDir) {
            $logCount = (Get-ChildItem $logDir -File).Count
            Write-Host "📋 Log Files: $logCount files in $logDir" -ForegroundColor Cyan
        }
        
        $ceDir = Join-Path $latestVerification "counterexamples"
        if (Test-Path $ceDir) {
            $ceCount = (Get-ChildItem $ceDir -File).Count
            if ($ceCount -gt 0) {
                Write-Host "⚠️ Counterexamples: $ceCount files in $ceDir" -ForegroundColor Yellow
            } else {
                Write-Host "✅ Counterexamples: None found (all tests passed!)" -ForegroundColor Green
            }
        }
    }
    
    # Check for counterexample analysis
    if (Test-Path "counterexample_analysis") {
        Write-Host "🔍 Counterexample Analysis: counterexample_analysis/" -ForegroundColor Cyan
    }
    
    # Check for comprehensive report
    if (Test-Path "comprehensive_verification_report.html") {
        Write-Host "📊 Comprehensive Report: comprehensive_verification_report.html" -ForegroundColor Cyan
        Write-Host "   (Should open automatically in your browser)" -ForegroundColor Gray
    }
    
    if (Test-Path "comprehensive_verification_report.json") {
        Write-Host "📋 JSON Report: comprehensive_verification_report.json" -ForegroundColor Cyan
    }
    
    Write-Host ""
    
    # Hackathon readiness assessment
    Write-Host "🎯 Hackathon Readiness Assessment:" -ForegroundColor Magenta
    
    $hasCounterexamples = $false
    if (Test-Path "verification_results") {
        $latestResults = Get-ChildItem -Path "verification_results" -Directory | Sort-Object Name -Descending | Select-Object -First 1
        if ($latestResults) {
            $ceDir = Join-Path $latestResults.FullName "counterexamples"
            if (Test-Path $ceDir) {
                $ceCount = (Get-ChildItem $ceDir -File).Count
                $hasCounterexamples = $ceCount -gt 0
            }
        }
    }
    
    if (-not $hasCounterexamples -and $overallSuccess) {
        Write-Host "🎉 READY FOR SUBMISSION!" -ForegroundColor Green
        Write-Host "   ✅ All verification tests passed" -ForegroundColor Green
        Write-Host "   ✅ No counterexamples found" -ForegroundColor Green
        Write-Host "   ✅ Comprehensive formal verification complete" -ForegroundColor Green
        Write-Host "   ✅ All safety, liveness, and resilience properties verified" -ForegroundColor Green
    } elseif (-not $hasCounterexamples) {
        Write-Host "⚠️ MOSTLY READY" -ForegroundColor Yellow
        Write-Host "   ✅ No counterexamples found" -ForegroundColor Green
        Write-Host "   ⚠️ Some verification steps had issues" -ForegroundColor Yellow
        Write-Host "   📋 Review the reports for details" -ForegroundColor Yellow
    } else {
        Write-Host "🔧 NEEDS WORK" -ForegroundColor Red
        Write-Host "   ❌ Counterexamples found" -ForegroundColor Red
        Write-Host "   🔍 Review counterexample analysis" -ForegroundColor Red
        Write-Host "   🛠️ Fix issues before submission" -ForegroundColor Red
    }
    
    Write-Host ""
    Write-Host "Next Steps:" -ForegroundColor White
    if (-not $hasCounterexamples -and $overallSuccess) {
        Write-Host "1. Review the comprehensive report" -ForegroundColor White
        Write-Host "2. Document the successful verification" -ForegroundColor White
        Write-Host "3. Prepare hackathon submission materials" -ForegroundColor White
        Write-Host "4. Highlight the formal correctness guarantees" -ForegroundColor White
    } else {
        Write-Host "1. Open comprehensive_verification_report.html" -ForegroundColor White
        Write-Host "2. Review any counterexamples in detail" -ForegroundColor White
        Write-Host "3. Fix identified issues in the specification" -ForegroundColor White
        Write-Host "4. Re-run verification after fixes" -ForegroundColor White
    }
    
    Write-Host ""
    Write-Host "Press any key to continue..." -ForegroundColor Gray
    $null = $Host.UI.RawUI.ReadKey("NoEcho,IncludeKeyDown")
}

# Execute main function
Main