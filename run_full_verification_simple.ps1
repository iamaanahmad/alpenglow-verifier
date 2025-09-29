# Simple Full Verification Script
Write-Host "Running Full Alpenglow Verification..." -ForegroundColor Cyan

# Run basic verification
Write-Host "Step 1: Basic Verification" -ForegroundColor Yellow
& .\run_verification_simple.ps1

# Generate report
Write-Host "Step 2: Generate Report" -ForegroundColor Yellow
& .\generate_verification_report.ps1

Write-Host "Full verification completed!" -ForegroundColor Green