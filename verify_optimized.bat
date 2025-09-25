@echo off
echo ========================================
echo Enhanced Alpenglow Verification Script
echo With State Constraints and Optimization
echo ========================================

echo.
echo Running 4-node configuration with basic optimization...
java -jar tla2tools.jar -config MC_4Nodes.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: 4-node verification failed
    pause
    exit /b 1
)

echo.
echo Running 7-node configuration with moderate optimization...
java -jar tla2tools.jar -config MC_7Nodes.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: 7-node verification failed
    pause
    exit /b 1
)

echo.
echo Running 10-node configuration with aggressive optimization...
java -jar tla2tools.jar -config MC_10Nodes.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: 10-node verification failed
    pause
    exit /b 1
)

echo.
echo Running Byzantine test with optimization...
java -jar tla2tools.jar -config MC_Byzantine_Test.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: Byzantine test failed
    pause
    exit /b 1
)

echo.
echo Running Certificate test with optimization...
java -jar tla2tools.jar -config MC_Certificate_Test.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: Certificate test failed
    pause
    exit /b 1
)

echo.
echo Running Statistical sampling test...
java -jar tla2tools.jar -config MC_Statistical_Test.cfg Alpenglow.tla
if %errorlevel% neq 0 (
    echo ERROR: Statistical test failed
    pause
    exit /b 1
)

echo.
echo ========================================
echo All optimized verification tests passed!
echo ========================================
pause