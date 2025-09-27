#!/usr/bin/env pwsh
# Simple Verification Script - Fixed Encoding
# Runs core TLA+ verification tests

Write-Host "=== Alpenglow Formal Verification System ===" -ForegroundColor Green
Write-Host "Starting verification tests..." -ForegroundColor Yellow

# Test configurations
$configs = @(
    @{Name="4-Node Basic"; Config="MC_4Nodes.cfg"; Spec="MC_4Nodes.tla"},
    @{Name="7-Node Medium"; Config="MC_7Nodes.cfg"; Spec="MC_7Nodes.tla"},
    @{Name="Byzantine Test"; Config="MC_Byzantine_Test.cfg"; Spec="MC_Byzantine_Test.tla"}
)

$results = @()
$totalTests = $configs.Count
$passedTests = 0

foreach ($test in $configs) {
    Write-Host "`nRunning: $($test.Name)" -ForegroundColor Cyan
    Write-Host "Command: java -jar tla2tools.jar -config $($test.Config) $($test.Spec)" -ForegroundColor Gray
    
    try {
        $output = & java -jar tla2tools.jar -config $test.Config $test.Spec 2>&1
        
        if ($LASTEXITCODE -eq 0 -and $output -match "Model checking completed. No error has been found") {
            Write-Host "PASSED: $($test.Name)" -ForegroundColor Green
            $status = "PASSED"
            $passedTests++
        } else {
            Write-Host "FAILED: $($test.Name)" -ForegroundColor Red
            $status = "FAILED"
        }
        
        $results += @{
            Name = $test.Name
            Status = $status
            Output = $output -join "`n"
        }
    }
    catch {
        Write-Host "ERROR: $($test.Name) - $($_.Exception.Message)" -ForegroundColor Red
        $results += @{
            Name = $test.Name
            Status = "ERROR"
            Output = $_.Exception.Message
        }
    }
}

# Summary
Write-Host "`n=== VERIFICATION SUMMARY ===" -ForegroundColor Green
Write-Host "Total Tests: $totalTests" -ForegroundColor White
Write-Host "Passed: $passedTests" -ForegroundColor Green
Write-Host "Failed: $($totalTests - $passedTests)" -ForegroundColor Red
Write-Host "Success Rate: $([math]::Round(($passedTests / $totalTests) * 100, 1))%" -ForegroundColor Yellow

if ($passedTests -eq $totalTests) {
    Write-Host "`nALL TESTS PASSED! Ready for hackathon submission!" -ForegroundColor Green
} else {
    Write-Host "`nSome tests failed. Check output above." -ForegroundColor Red
}

# Generate simple report
$reportContent = @"
# Alpenglow Verification Results
Generated: $(Get-Date)

## Summary
- Total Tests: $totalTests
- Passed: $passedTests  
- Failed: $($totalTests - $passedTests)
- Success Rate: $([math]::Round(($passedTests / $totalTests) * 100, 1))%

## Test Results
"@

foreach ($result in $results) {
    $reportContent += "`n### $($result.Name): $($result.Status)`n"
}

$reportContent | Out-File -FilePath "verification_results_simple.md" -Encoding UTF8
Write-Host "`nReport saved to: verification_results_simple.md" -ForegroundColor Cyan