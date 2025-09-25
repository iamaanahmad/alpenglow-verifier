# Test script to validate property verification fixes
# Tests various Byzantine node configurations and edge cases

Write-Host "Testing Property Verification Fixes" -ForegroundColor Green
Write-Host "====================================" -ForegroundColor Green

$testResults = @()

# Test 1: Empty Byzantine node set (edge case)
Write-Host "`nTest 1: Empty Byzantine node set" -ForegroundColor Yellow
java -jar tla2tools.jar -config MC_Simple_Test.cfg Properties.tla -deadlock > $null 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ PASSED: Empty Byzantine set handled correctly" -ForegroundColor Green
    $testResults += "Empty Byzantine set: PASSED"
} else {
    Write-Host "✗ FAILED: Empty Byzantine set test failed" -ForegroundColor Red
    $testResults += "Empty Byzantine set: FAILED"
}

# Test 2: Byzantine node configuration
Write-Host "`nTest 2: Byzantine node configuration" -ForegroundColor Yellow
java -jar tla2tools.jar -config MC_Byzantine_Test.cfg Properties.tla -deadlock > $null 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ PASSED: Byzantine configuration handled correctly" -ForegroundColor Green
    $testResults += "Byzantine configuration: PASSED"
} else {
    Write-Host "✗ FAILED: Byzantine configuration test failed" -ForegroundColor Red
    $testResults += "Byzantine configuration: FAILED"
}

# Test 3: Timeout and skip certificate handling
Write-Host "`nTest 3: Timeout and skip certificate handling" -ForegroundColor Yellow
java -jar tla2tools.jar -config MC_Timeout_Test.cfg Properties.tla -deadlock > $null 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ PASSED: Timeout handling works correctly" -ForegroundColor Green
    $testResults += "Timeout handling: PASSED"
} else {
    Write-Host "✗ FAILED: Timeout handling test failed" -ForegroundColor Red
    $testResults += "Timeout handling: FAILED"
}

# Test 4: Certificate validation
Write-Host "`nTest 4: Certificate validation" -ForegroundColor Yellow
java -jar tla2tools.jar -config MC_Certificate_Test.cfg Properties.tla -deadlock > $null 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ PASSED: Certificate validation works correctly" -ForegroundColor Green
    $testResults += "Certificate validation: PASSED"
} else {
    Write-Host "✗ FAILED: Certificate validation test failed" -ForegroundColor Red
    $testResults += "Certificate validation: FAILED"
}

# Test 5: Safety properties
Write-Host "`nTest 5: Safety properties" -ForegroundColor Yellow
java -jar tla2tools.jar -config MC_Safety_Test.cfg Properties.tla -deadlock > $null 2>&1
if ($LASTEXITCODE -eq 0) {
    Write-Host "✓ PASSED: Safety properties work correctly" -ForegroundColor Green
    $testResults += "Safety properties: PASSED"
} else {
    Write-Host "✗ FAILED: Safety properties test failed" -ForegroundColor Red
    $testResults += "Safety properties: FAILED"
}

# Summary
Write-Host "`n" -ForegroundColor White
Write-Host "Test Results Summary" -ForegroundColor Green
Write-Host "===================" -ForegroundColor Green
foreach ($result in $testResults) {
    if ($result -like "*PASSED*") {
        Write-Host "✓ $result" -ForegroundColor Green
    } elseif ($result -like "*FAILED*") {
        Write-Host "✗ $result" -ForegroundColor Red
    } else {
        Write-Host "⚠ $result" -ForegroundColor Yellow
    }
}

$passedCount = ($testResults | Where-Object { $_ -like "*PASSED*" }).Count
$totalCount = $testResults.Count

Write-Host "`nOverall: $passedCount/$totalCount tests passed" -ForegroundColor $(if ($passedCount -eq $totalCount) { "Green" } else { "Yellow" })

if ($passedCount -eq $totalCount) {
    Write-Host "`n🎉 All property verification fixes are working correctly!" -ForegroundColor Green
    exit 0
} else {
    Write-Host "`n⚠️  Some tests failed. Please review the output above." -ForegroundColor Yellow
    exit 1
}