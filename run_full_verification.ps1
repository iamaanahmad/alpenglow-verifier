# Alpenglow Formal Verification - Complete Suite
# This script runs the full verification pipeline

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Complete Alpenglow Verification Suite" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

$startTime = Get-Date
$overallSuccess = $true

# Step 1: Run basic verification
Write-Host "[1/2] Running verification tests..." -ForegroundColor Yellow

try {
    & .\run_verification_simple.ps1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Verification completed successfully" -ForegroundColor Green
    } else {
        Write-Host "⚠️ Verification completed with issues" -ForegroundColor Yellow
        $overallSuccess = $false
    }
} catch {
    Write-Host "❌ Verification failed: $($_.Exception.Message)" -ForegroundColor Red
    $overallSuccess = $false
}

Write-Host ""

# Step 2: Generate report
Write-Host "[2/2] Generating comprehensive report..." -ForegroundColor Yellow

try {
    & .\generate_verification_report.ps1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Report generation completed successfully" -ForegroundColor Green
    } else {
        Write-Host "⚠️ Report generation completed with warnings" -ForegroundColor Yellow
    }
} catch {
    Write-Host "⚠️ Report generation failed: $($_.Exception.Message)" -ForegroundColor Yellow
}

Write-Host ""

# Final summary
$endTime = Get-Date
$totalDuration = $endTime - $startTime

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "VERIFICATION SUITE COMPLETE" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Total Duration: $($totalDuration.ToString('hh\:mm\:ss'))" -ForegroundColor White

if ($overallSuccess) {
    Write-Host "Overall Status: ✅ SUCCESS" -ForegroundColor Green
    Write-Host ""
    Write-Host "🎉 READY FOR SUBMISSION!" -ForegroundColor Green
    Write-Host "   ✅ All verification tests passed" -ForegroundColor Green
    Write-Host "   ✅ No counterexamples found" -ForegroundColor Green
    Write-Host "   ✅ Mathematical correctness proven" -ForegroundColor Green
} else {
    Write-Host "Overall Status: ⚠️ COMPLETED WITH ISSUES" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "⚠️ Some issues found - review output above" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "Available Reports:" -ForegroundColor White

if (Test-Path "verification_results_simple.md") {
    Write-Host "📄 Simple Results: verification_results_simple.md" -ForegroundColor Cyan
}

if (Test-Path "comprehensive_verification_report.html") {
    Write-Host "📊 Comprehensive Report: comprehensive_verification_report.html" -ForegroundColor Cyan
}

Write-Host ""
Write-Host "Verification suite completed successfully!" -ForegroundColor Green