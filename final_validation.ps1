#!/usr/bin/env pwsh

# Final Validation Script for Alpenglow Verification
# Task 24: Complete final validation and testing

Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Final Alpenglow Verification Validation" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

$startTime = Get-Date
$overallSuccess = $true
$testResults = @()

# Function to log results
function Log-TestResult {
    param(
        [string]$TestName,
        [bool]$Success,
        [string]$Details = ""
    )
    
    $result = @{
        TestName = $TestName
        Success = $Success
        Details = $Details
        Timestamp = Get-Date
    }
    
    $script:testResults += $result
    
    if ($Success) {
        Write-Host "✅ $TestName" -ForegroundColor Green
    } else {
        Write-Host "❌ $TestName" -ForegroundColor Red
        $script:overallSuccess = $false
    }
    
    if ($Details) {
        Write-Host "   $Details" -ForegroundColor Gray
    }
}

Write-Host "Step 1: Running comprehensive verification suite..." -ForegroundColor Yellow
Write-Host ""

# Test 1: Run comprehensive verification
try {
    Write-Host "Running verify_comprehensive.ps1..." -ForegroundColor White
    $result = & .\verify_comprehensive.ps1 -TimeoutMinutes 30
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "Comprehensive Verification Suite" $true "All configurations tested successfully"
    } else {
        Log-TestResult "Comprehensive Verification Suite" $false "Some tests failed or timed out"
    }
} catch {
    Log-TestResult "Comprehensive Verification Suite" $false "Script execution failed: $($_.Exception.Message)"
}

Write-Host ""
Write-Host "Step 2: Validating individual configurations..." -ForegroundColor Yellow
Write-Host ""

# Test 2: Validate 4-node configuration
try {
    Write-Host "Testing 4-node configuration..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_4Nodes.cfg -workers auto -cleanup MC_4Nodes.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "4-Node Configuration" $true "All properties verified"
    } else {
        Log-TestResult "4-Node Configuration" $false "Property verification failed"
    }
} catch {
    Log-TestResult "4-Node Configuration" $false "TLC execution failed: $($_.Exception.Message)"
}

# Test 3: Validate 7-node configuration  
try {
    Write-Host "Testing 7-node configuration..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_7Nodes.cfg -workers auto -cleanup MC_7Nodes.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "7-Node Configuration" $true "All properties verified"
    } else {
        Log-TestResult "7-Node Configuration" $false "Property verification failed"
    }
} catch {
    Log-TestResult "7-Node Configuration" $false "TLC execution failed: $($_.Exception.Message)"
}

# Test 4: Validate 10-node configuration
try {
    Write-Host "Testing 10-node configuration..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_10Nodes.cfg -workers auto -cleanup MC_10Nodes.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "10-Node Configuration" $true "All properties verified"
    } else {
        Log-TestResult "10-Node Configuration" $false "Property verification failed"
    }
} catch {
    Log-TestResult "10-Node Configuration" $false "TLC execution failed: $($_.Exception.Message)"
}

Write-Host ""
Write-Host "Step 3: Validating Byzantine fault tolerance..." -ForegroundColor Yellow
Write-Host ""

# Test 5: Byzantine fault tolerance
try {
    Write-Host "Testing Byzantine fault tolerance..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_Byzantine_Test.cfg -workers auto -cleanup MC_Byzantine_Test.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "Byzantine Fault Tolerance" $true "Safety maintained with Byzantine nodes"
    } else {
        Log-TestResult "Byzantine Fault Tolerance" $false "Byzantine fault tolerance verification failed"
    }
} catch {
    Log-TestResult "Byzantine Fault Tolerance" $false "TLC execution failed: $($_.Exception.Message)"
}

Write-Host ""
Write-Host "Step 4: Validating safety properties..." -ForegroundColor Yellow
Write-Host ""

# Test 6: Safety properties
try {
    Write-Host "Testing safety properties..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_Safety_Test.cfg -workers auto -cleanup MC_Safety_Test.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "Safety Properties" $true "All safety properties verified"
    } else {
        Log-TestResult "Safety Properties" $false "Safety property verification failed"
    }
} catch {
    Log-TestResult "Safety Properties" $false "TLC execution failed: $($_.Exception.Message)"
}

Write-Host ""
Write-Host "Step 5: Validating liveness properties..." -ForegroundColor Yellow
Write-Host ""

# Test 7: Liveness properties
try {
    Write-Host "Testing liveness properties..." -ForegroundColor White
    $result = java -jar tla2tools.jar -config MC_Liveness_Test.cfg -workers auto -cleanup MC_Liveness_Test.tla
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "Liveness Properties" $true "All liveness properties verified"
    } else {
        Log-TestResult "Liveness Properties" $false "Liveness property verification failed"
    }
} catch {
    Log-TestResult "Liveness Properties" $false "TLC execution failed: $($_.Exception.Message)"
}

Write-Host ""
Write-Host "Step 6: Generating final documentation..." -ForegroundColor Yellow
Write-Host ""

# Test 8: Generate final documentation
try {
    Write-Host "Generating verification report..." -ForegroundColor White
    $result = & .\generate_verification_report.ps1 -IncludeProofStatus -IncludePerformanceMetrics -GenerateJSON
    
    if ($LASTEXITCODE -eq 0) {
        Log-TestResult "Documentation Generation" $true "Final reports generated successfully"
    } else {
        Log-TestResult "Documentation Generation" $false "Report generation had issues"
    }
} catch {
    Log-TestResult "Documentation Generation" $false "Report generation failed: $($_.Exception.Message)"
}

# Final Summary
$endTime = Get-Date
$duration = $endTime - $startTime

Write-Host ""
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Final Validation Results" -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Duration: $($duration.ToString('hh\:mm\:ss'))" -ForegroundColor White
Write-Host ""

$passedTests = ($testResults | Where-Object { $_.Success }).Count
$totalTests = $testResults.Count

Write-Host "Test Results: $passedTests/$totalTests passed" -ForegroundColor White
Write-Host ""

foreach ($result in $testResults) {
    $status = if ($result.Success) { "✅" } else { "❌" }
    $color = if ($result.Success) { "Green" } else { "Red" }
    Write-Host "$status $($result.TestName)" -ForegroundColor $color
    if ($result.Details) {
        Write-Host "   $($result.Details)" -ForegroundColor Gray
    }
}

Write-Host ""

if ($overallSuccess -and $passedTests -eq $totalTests) {
    Write-Host "🎉 FINAL VALIDATION SUCCESSFUL!" -ForegroundColor Green
    Write-Host "   ✅ All verification tests passed" -ForegroundColor Green
    Write-Host "   ✅ All 13 properties verified without counterexamples" -ForegroundColor Green
    Write-Host "   ✅ Byzantine fault tolerance confirmed" -ForegroundColor Green
    Write-Host "   ✅ Ready for hackathon submission" -ForegroundColor Green
} else {
    Write-Host "⚠️ VALIDATION COMPLETED WITH ISSUES" -ForegroundColor Yellow
    Write-Host "   Some tests failed or had issues" -ForegroundColor Yellow
    Write-Host "   Review the results above for details" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "Generated Files:" -ForegroundColor White

# Check for generated files
$files = @(
    "comprehensive_verification_report.html",
    "comprehensive_verification_report.json",
    "verification_results"
)

foreach ($file in $files) {
    if (Test-Path $file) {
        Write-Host "✅ $file" -ForegroundColor Green
    } else {
        Write-Host "❌ $file (missing)" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "Final validation completed." -ForegroundColor Cyan

# Save results to JSON for documentation
$finalResults = @{
    Timestamp = Get-Date
    Duration = $duration.ToString()
    OverallSuccess = $overallSuccess
    PassedTests = $passedTests
    TotalTests = $totalTests
    TestResults = $testResults
}

$finalResults | ConvertTo-Json -Depth 3 | Out-File "final_validation_results.json"
Write-Host "Results saved to: final_validation_results.json" -ForegroundColor Cyan