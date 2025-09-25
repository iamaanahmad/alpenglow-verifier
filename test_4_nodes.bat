@echo off
echo Testing 4-node configuration...
echo.
echo Running basic syntax and invariant check (depth 2):
java -jar tla2tools.jar -config MC_4Nodes.cfg MC_4Nodes.tla -workers 1 -depth 2
echo.
echo Test completed. Check output above for results.
pause