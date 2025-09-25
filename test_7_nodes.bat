@echo off
echo Testing 7-node Alpenglow configuration...
echo.

echo Running TLC model checker on 7-node configuration...
java -jar tla2tools.jar -config MC_7Nodes.cfg MC_7Nodes.tla

echo.
echo 7-node test completed.
echo Check the output above for any property violations or errors.
echo.
pause