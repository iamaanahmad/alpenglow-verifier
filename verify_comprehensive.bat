@echo off
setlocal enabledelayedexpansion

REM Comprehensive Alpenglow Verification Script (Batch version)
REM Automated verification with result analysis and reporting

echo ========================================
echo Enhanced Alpenglow Comprehensive Verification
echo ========================================

REM Configuration
set TLA_TOOLS=tla2tools.jar
set TIMESTAMP=%date:~-4,4%-%date:~-10,2%-%date:~-7,2%_%time:~0,2%-%time:~3,2%-%time:~6,2%
set TIMESTAMP=%TIMESTAMP: =0%
set RESULTS_DIR=verification_results\%TIMESTAMP%

REM Create results directory
echo Initializing results directory: %RESULTS_DIR%
if exist "%RESULTS_DIR%" rmdir /s /q "%RESULTS_DIR%"
mkdir "%RESULTS_DIR%"
mkdir "%RESULTS_DIR%\logs"
mkdir "%RESULTS_DIR%\counterexamples"
mkdir "%RESULTS_DIR%\reports"

REM Initialize log file
echo [%date% %time%] [INFO] Starting comprehensive verification > "%RESULTS_DIR%\verification.log"

REM Check prerequisites
echo Checking prerequisites...
if not exist "%TLA_TOOLS%" (
    echo ERROR: TLA+ tools not found at %TLA_TOOLS%
    echo [%date% %time%] [ERROR] TLA+ tools not found >> "%RESULTS_DIR%\verification.log"
    pause
    exit /b 1
)

java -version >nul 2>&1
if %errorlevel% neq 0 (
    echo ERROR: Java not found in PATH
    echo [%date% %time%] [ERROR] Java not found in PATH >> "%RESULTS_DIR%\verification.log"
    pause
    exit /b 1
)

echo Prerequisites satisfied
echo [%date% %time%] [INFO] Prerequisites satisfied >> "%RESULTS_DIR%\verification.log"

REM Initialize counters
set TOTAL_TESTS=0
set PASSED_TESTS=0
set FAILED_TESTS=0
set ERROR_TESTS=0

REM Test configurations
echo.
echo Starting verification of all configurations...
echo [%date% %time%] [INFO] Starting verification of all configurations >> "%RESULTS_DIR%\verification.log"

REM 4-Node Basic Test
call :RunTest "4-Node Basic" "MC_4Nodes.cfg" "MC_4Nodes.tla" "Basic" "High" "Small scale exhaustive verification"

REM 7-Node Medium Test  
call :RunTest "7-Node Medium" "MC_7Nodes.cfg" "MC_7Nodes.tla" "Scalability" "High" "Medium scale targeted verification"

REM 10-Node Large Test
call :RunTest "10-Node Large" "MC_10Nodes.cfg" "MC_10Nodes.tla" "Performance" "Medium" "Large scale statistical verification"

REM Byzantine Test
call :RunTest "Byzantine Test" "MC_Byzantine_Test.cfg" "MC_Byzantine_Test.tla" "Security" "Critical" "Byzantine fault tolerance verification"

REM Certificate Test
call :RunTest "Certificate Test" "MC_Certificate_Test.cfg" "MC_Certificate_Test.tla" "Correctness" "High" "Certificate aggregation verification"

REM Statistical Test
call :RunTest "Statistical Test" "MC_Statistical_Test.cfg" "MC_Statistical_Test.tla" "Statistical" "Medium" "Statistical sampling verification"

REM Enhanced Statistical Test
if exist "MC_Statistical_Enhanced.cfg" (
    call :RunTest "Enhanced Statistical" "MC_Statistical_Enhanced.cfg" "MC_Statistical_Enhanced.tla" "Statistical" "Medium" "Enhanced statistical sampling with Monte Carlo"
)

REM Generate summary report
call :GenerateSummaryReport

REM Final results
echo.
echo ========================================
echo Verification Complete!
echo ========================================
set /a SUCCESS_RATE=(%PASSED_TESTS% * 100) / %TOTAL_TESTS%
echo Results: %PASSED_TESTS%/%TOTAL_TESTS% passed (%SUCCESS_RATE%%%)
echo Reports saved to: %RESULTS_DIR%

if %SUCCESS_RATE% equ 100 (
    echo 🎉 All tests passed! Ready for hackathon submission!
) else (
    echo ⚠ Some tests failed. Check reports for details.
)

echo.
echo Press any key to view the summary report...
pause >nul
type "%RESULTS_DIR%\reports\summary.txt"
pause
exit /b 0

REM Function to run individual test
:RunTest
set TEST_NAME=%~1
set CONFIG_FILE=%~2
set SPEC_FILE=%~3
set CATEGORY=%~4
set PRIORITY=%~5
set DESCRIPTION=%~6

set /a TOTAL_TESTS+=1
echo.
echo [%TOTAL_TESTS%] Running %TEST_NAME%...
echo Category: %CATEGORY% ^| Priority: %PRIORITY%
echo Description: %DESCRIPTION%
echo [%date% %time%] [INFO] Starting %TEST_NAME% >> "%RESULTS_DIR%\verification.log"

REM Check if config file exists
if not exist "%CONFIG_FILE%" (
    echo ERROR: Configuration file not found: %CONFIG_FILE%
    echo [%date% %time%] [ERROR] Configuration file not found: %CONFIG_FILE% >> "%RESULTS_DIR%\verification.log"
    set /a ERROR_TESTS+=1
    goto :eof
)

REM Set log files
set LOG_FILE=%RESULTS_DIR%\logs\%TEST_NAME: =_%_output.log
set ERROR_FILE=%RESULTS_DIR%\logs\%TEST_NAME: =_%_error.log

REM Record start time
set START_TIME=%time%

REM Run TLC verification
echo Executing: java -XX:+UseParallelGC -Xmx4g -jar %TLA_TOOLS% -config %CONFIG_FILE% %SPEC_FILE%
java -XX:+UseParallelGC -Xmx4g -jar %TLA_TOOLS% -config %CONFIG_FILE% %SPEC_FILE% > "%LOG_FILE%" 2> "%ERROR_FILE%"

REM Record end time and calculate duration
set END_TIME=%time%

REM Check result
if %errorlevel% equ 0 (
    echo ✓ %TEST_NAME% completed successfully
    echo [%date% %time%] [SUCCESS] %TEST_NAME% completed successfully >> "%RESULTS_DIR%\verification.log"
    set /a PASSED_TESTS+=1
    call :AnalyzeSuccess "%LOG_FILE%" "%TEST_NAME%"
) else (
    echo ✗ %TEST_NAME% failed with exit code %errorlevel%
    echo [%date% %time%] [ERROR] %TEST_NAME% failed with exit code %errorlevel% >> "%RESULTS_DIR%\verification.log"
    set /a FAILED_TESTS+=1
    call :AnalyzeFailure "%LOG_FILE%" "%ERROR_FILE%" "%TEST_NAME%"
)

goto :eof

REM Function to analyze successful test
:AnalyzeSuccess
set LOG_FILE=%~1
set TEST_NAME=%~2

echo Analyzing results for %TEST_NAME%...

REM Extract key metrics from log file
if exist "%LOG_FILE%" (
    findstr /C:"states generated" "%LOG_FILE%" > temp_states.txt
    if exist temp_states.txt (
        for /f "tokens=1" %%a in (temp_states.txt) do set STATES_EXPLORED=%%a
        del temp_states.txt
    ) else (
        set STATES_EXPLORED=Unknown
    )
    
    REM Count properties and invariants
    findstr /C:"Checking property" "%LOG_FILE%" > temp_props.txt 2>nul
    if exist temp_props.txt (
        for /f %%a in ('type temp_props.txt ^| find /c /v ""') do set PROPERTIES_COUNT=%%a
        del temp_props.txt
    ) else (
        set PROPERTIES_COUNT=0
    )
    
    findstr /C:"Checking invariant" "%LOG_FILE%" > temp_invs.txt 2>nul
    if exist temp_invs.txt (
        for /f %%a in ('type temp_invs.txt ^| find /c /v ""') do set INVARIANTS_COUNT=%%a
        del temp_invs.txt
    ) else (
        set INVARIANTS_COUNT=0
    )
    
    echo   States Explored: !STATES_EXPLORED!
    echo   Properties Verified: !PROPERTIES_COUNT!
    echo   Invariants Checked: !INVARIANTS_COUNT!
    
    REM Log detailed results
    echo [%date% %time%] [INFO] %TEST_NAME% - States: !STATES_EXPLORED!, Properties: !PROPERTIES_COUNT!, Invariants: !INVARIANTS_COUNT! >> "%RESULTS_DIR%\verification.log"
)

goto :eof

REM Function to analyze failed test
:AnalyzeFailure
set LOG_FILE=%~1
set ERROR_FILE=%~2
set TEST_NAME=%~3

echo Analyzing failure for %TEST_NAME%...

REM Check for counterexamples
if exist "%LOG_FILE%" (
    findstr /C:"Error: Invariant" "%LOG_FILE%" > temp_error.txt 2>nul
    if exist temp_error.txt (
        echo   Invariant violation detected
        for /f "tokens=3" %%a in (temp_error.txt) do (
            echo   Violated invariant: %%a
            call :ExtractCounterexample "%LOG_FILE%" "%TEST_NAME%" "%%a"
        )
        del temp_error.txt
    )
    
    findstr /C:"Error: Temporal property" "%LOG_FILE%" > temp_temporal.txt 2>nul
    if exist temp_temporal.txt (
        echo   Temporal property violation detected
        del temp_temporal.txt
    )
    
    findstr /C:"Warning:" "%LOG_FILE%" > temp_warnings.txt 2>nul
    if exist temp_warnings.txt (
        echo   Warnings found - check log file
        del temp_warnings.txt
    )
)

REM Check error file
if exist "%ERROR_FILE%" (
    for %%a in ("%ERROR_FILE%") do if %%~za gtr 0 (
        echo   Error output detected - check error file
        echo [%date% %time%] [ERROR] %TEST_NAME% - Error output in %ERROR_FILE% >> "%RESULTS_DIR%\verification.log"
    )
)

goto :eof

REM Function to extract counterexample
:ExtractCounterexample
set LOG_FILE=%~1
set TEST_NAME=%~2
set VIOLATED_PROPERTY=%~3

set COUNTEREXAMPLE_FILE=%RESULTS_DIR%\counterexamples\%TEST_NAME: =_%_%VIOLATED_PROPERTY%.trace

echo Extracting counterexample for %VIOLATED_PROPERTY%...
echo Counterexample Analysis for %TEST_NAME% > "%COUNTEREXAMPLE_FILE%"
echo Violated Property: %VIOLATED_PROPERTY% >> "%COUNTEREXAMPLE_FILE%"
echo Generated: %date% %time% >> "%COUNTEREXAMPLE_FILE%"
echo. >> "%COUNTEREXAMPLE_FILE%"
echo Trace: >> "%COUNTEREXAMPLE_FILE%"

REM Extract trace from log file (simplified extraction)
findstr /A:"The behavior up to this point is:" "%LOG_FILE%" >> "%COUNTEREXAMPLE_FILE%" 2>nul

echo. >> "%COUNTEREXAMPLE_FILE%"
echo Analysis: >> "%COUNTEREXAMPLE_FILE%"
call :AnalyzeViolation "%VIOLATED_PROPERTY%" >> "%COUNTEREXAMPLE_FILE%"

echo   Counterexample saved to: %COUNTEREXAMPLE_FILE%

goto :eof

REM Function to analyze property violation
:AnalyzeViolation
set PROPERTY=%~1

echo Analysis for %PROPERTY%:
if "%PROPERTY%"=="NoConflictingBlocksFinalized" (
    echo - Multiple blocks may have been finalized in the same slot
    echo - Recommendation: Check certificate aggregation logic and Byzantine behavior
) else if "%PROPERTY%"=="CertificateUniqueness" (
    echo - Multiple certificates generated for the same slot  
    echo - Recommendation: Review certificate generation conditions and timing
) else if "%PROPERTY%"=="ByzantineFaultTolerance" (
    echo - Byzantine nodes may have exceeded fault tolerance limits
    echo - Recommendation: Verify Byzantine stake calculations and constraints
) else (
    echo - Property violation detected - manual review required
    echo - Recommendation: Examine trace for state transitions leading to violation
)

goto :eof

REM Function to generate summary report
:GenerateSummaryReport
echo Generating comprehensive summary report...

set SUMMARY_FILE=%RESULTS_DIR%\reports\summary.txt
set /a SUCCESS_RATE=(%PASSED_TESTS% * 100) / %TOTAL_TESTS%

echo Enhanced Alpenglow Formal Verification Summary > "%SUMMARY_FILE%"
echo Generated: %date% %time% >> "%SUMMARY_FILE%"
echo Verification Run: %TIMESTAMP% >> "%SUMMARY_FILE%"
echo. >> "%SUMMARY_FILE%"
echo OVERALL RESULTS: >> "%SUMMARY_FILE%"
echo ================ >> "%SUMMARY_FILE%"
echo Total Configurations: %TOTAL_TESTS% >> "%SUMMARY_FILE%"
echo Passed: %PASSED_TESTS% >> "%SUMMARY_FILE%"
echo Failed: %FAILED_TESTS% >> "%SUMMARY_FILE%"
echo Errors: %ERROR_TESTS% >> "%SUMMARY_FILE%"
echo Success Rate: %SUCCESS_RATE%%% >> "%SUMMARY_FILE%"
echo. >> "%SUMMARY_FILE%"

echo CONFIGURATION DETAILS: >> "%SUMMARY_FILE%"
echo ===================== >> "%SUMMARY_FILE%"

REM Add individual test results
for %%f in ("%RESULTS_DIR%\logs\*_output.log") do (
    set LOG_NAME=%%~nf
    set TEST_NAME=!LOG_NAME:_output=!
    set TEST_NAME=!TEST_NAME:_= !
    
    if exist "%%f" (
        findstr /C:"states generated" "%%f" > temp_result.txt 2>nul
        if exist temp_result.txt (
            for /f "tokens=1" %%s in (temp_result.txt) do (
                echo !TEST_NAME!: PASSED - %%s states >> "%SUMMARY_FILE%"
            )
            del temp_result.txt
        ) else (
            echo !TEST_NAME!: PASSED - Analysis pending >> "%SUMMARY_FILE%"
        )
    )
)

REM Add failed tests
if %FAILED_TESTS% gtr 0 (
    echo. >> "%SUMMARY_FILE%"
    echo FAILED CONFIGURATIONS: >> "%SUMMARY_FILE%"
    echo ====================== >> "%SUMMARY_FILE%"
    for %%f in ("%RESULTS_DIR%\logs\*_error.log") do (
        for %%a in ("%%f") do if %%~za gtr 0 (
            set ERROR_NAME=%%~nf
            set TEST_NAME=!ERROR_NAME:_error=!
            set TEST_NAME=!TEST_NAME:_= !
            echo !TEST_NAME!: FAILED - Check counterexamples directory >> "%SUMMARY_FILE%"
        )
    )
)

echo. >> "%SUMMARY_FILE%"
echo HACKATHON READINESS: >> "%SUMMARY_FILE%"
echo =================== >> "%SUMMARY_FILE%"
if %SUCCESS_RATE% equ 100 (
    echo ✓ READY FOR SUBMISSION: All verification tests passed successfully! >> "%SUMMARY_FILE%"
) else (
    echo ⚠ NEEDS ATTENTION: Some tests failed - review counterexamples and fix issues >> "%SUMMARY_FILE%"
)

echo. >> "%SUMMARY_FILE%"
echo RECOMMENDATIONS: >> "%SUMMARY_FILE%"
echo =============== >> "%SUMMARY_FILE%"
if %SUCCESS_RATE% equ 100 (
    echo ✓ All verification tests passed successfully! >> "%SUMMARY_FILE%"
    echo ✓ The Alpenglow protocol implementation meets all specified properties. >> "%SUMMARY_FILE%"
    echo ✓ Ready for hackathon submission with comprehensive formal verification. >> "%SUMMARY_FILE%"
) else (
    echo ⚠ Some verification tests failed or encountered errors. >> "%SUMMARY_FILE%"
    echo 1. Review counterexample traces in the counterexamples directory >> "%SUMMARY_FILE%"
    echo 2. Check model constraints and optimization settings >> "%SUMMARY_FILE%"
    echo 3. Verify TLA+ specification correctness >> "%SUMMARY_FILE%"
    echo 4. Consider adjusting timeout values for large configurations >> "%SUMMARY_FILE%"
)

echo Summary report generated: %SUMMARY_FILE%
echo [%date% %time%] [INFO] Summary report generated >> "%RESULTS_DIR%\verification.log"

goto :eof