@echo off
echo === Alpenglow Formal Verification System ===
echo Starting verification tests...

echo.
echo Running 4-Node Basic Configuration...
java -jar tla2tools.jar -config MC_4Nodes.cfg MC_4Nodes.tla
if %ERRORLEVEL% EQU 0 (
    echo PASSED: 4-Node Basic
) else (
    echo FAILED: 4-Node Basic
)

echo.
echo Running Byzantine Test Configuration...
java -jar tla2tools.jar -config MC_Byzantine_Test.cfg MC_Byzantine_Test.tla
if %ERRORLEVEL% EQU 0 (
    echo PASSED: Byzantine Test
) else (
    echo FAILED: Byzantine Test
)

echo.
echo === VERIFICATION COMPLETE ===
echo Check output above for results.
pause