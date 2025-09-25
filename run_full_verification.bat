@echo off
REM Complete Alpenglow Verification Suite
REM Runs comprehensive verification and generates detailed reports

echo ========================================
echo Complete Alpenglow Verification Suite
echo ========================================
echo.

REM Step 1: Run comprehensive verification
echo [1/3] Running comprehensive verification...
call verify_comprehensive.bat
if %errorlevel% neq 0 (
    echo ERROR: Comprehensive verification failed
    pause
    exit /b 1
)

echo.
echo [2/3] Analyzing counterexamples...
powershell -ExecutionPolicy Bypass -File analyze_counterexamples.ps1
if %errorlevel% neq 0 (
    echo WARNING: Counterexample analysis had issues
)

echo.
echo [3/3] Generating comprehensive report...
powershell -ExecutionPolicy Bypass -File generate_verification_report.ps1
if %errorlevel% neq 0 (
    echo WARNING: Report generation had issues
)

echo.
echo ========================================
echo Verification Suite Complete!
echo ========================================
echo.
echo Check the following outputs:
echo - verification_results\[timestamp]\ - Detailed verification logs
echo - counterexample_analysis\ - Counterexample analysis (if any)
echo - comprehensive_verification_report.html - Final report
echo.
echo The HTML report should open automatically in your browser.
echo.
pause