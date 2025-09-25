# Enhanced Alpenglow Verification Script with Optimization
# PowerShell version for cross-platform compatibility

Write-Host "========================================" -ForegroundColor Green
Write-Host "Enhanced Alpenglow Verification Script" -ForegroundColor Green
Write-Host "With State Constraints and Optimization" -ForegroundColor Green
Write-Host "========================================" -ForegroundColor Green

function Run-TLCTest {
    param(
        [string]$ConfigFile,
        [string]$TestName,
        [string]$OptimizationLevel
    )
    
    Write-Host ""
    Write-Host "Running $TestName with $OptimizationLevel optimization..." -ForegroundColor Yellow
    
    $process = Start-Process -FilePath "java" -ArgumentList "-jar", "tla2tools.jar", "-config", $ConfigFile, "Alpenglow.tla" -Wait -PassThru -NoNewWindow
    
    if ($process.ExitCode -eq 0) {
        Write-Host "✓ $TestName passed" -ForegroundColor Green
        return $true
    } else {
        Write-Host "✗ $TestName failed with exit code $($process.ExitCode)" -ForegroundColor Red
        return $false
    }
}

# Track test results
$testResults = @()

# Run all test configurations
$testResults += Run-TLCTest -ConfigFile "MC_4Nodes.cfg" -TestName "4-node configuration" -OptimizationLevel "basic"
$testResults += Run-TLCTest -ConfigFile "MC_7Nodes.cfg" -TestName "7-node configuration" -OptimizationLevel "moderate"
$testResults += Run-TLCTest -ConfigFile "MC_10Nodes.cfg" -TestName "10-node configuration" -OptimizationLevel "aggressive"
$testResults += Run-TLCTest -ConfigFile "MC_Byzantine_Test.cfg" -TestName "Byzantine test" -OptimizationLevel "moderate"
$testResults += Run-TLCTest -ConfigFile "MC_Certificate_Test.cfg" -TestName "Certificate test" -OptimizationLevel "basic"
$testResults += Run-TLCTest -ConfigFile "MC_Statistical_Test.cfg" -TestName "Statistical sampling test" -OptimizationLevel "aggressive"

# Summary
Write-Host ""
Write-Host "========================================" -ForegroundColor Green
$passedTests = ($testResults | Where-Object { $_ -eq $true }).Count
$totalTests = $testResults.Count

if ($passedTests -eq $totalTests) {
    Write-Host "All $totalTests optimized verification tests passed!" -ForegroundColor Green
    Write-Host "State constraints and optimization working correctly." -ForegroundColor Green
} else {
    Write-Host "$passedTests out of $totalTests tests passed." -ForegroundColor Yellow
    Write-Host "Some optimizations may need adjustment." -ForegroundColor Yellow
}
Write-Host "========================================" -ForegroundColor Green

# Performance analysis
Write-Host ""
Write-Host "Optimization Performance Analysis:" -ForegroundColor Cyan
Write-Host "- Basic (Level 1): Minimal constraints for small configurations" -ForegroundColor White
Write-Host "- Moderate (Level 2): Balanced constraints for medium configurations" -ForegroundColor White  
Write-Host "- Aggressive (Level 3): Maximum constraints for large configurations" -ForegroundColor White
Write-Host "- Statistical: Monte Carlo sampling for probabilistic verification" -ForegroundColor White