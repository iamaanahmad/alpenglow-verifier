@echo off
echo Testing 10-node Alpenglow configuration for stress testing and performance boundaries...
echo.

echo Running TLC model checker on 10-node configuration with statistical sampling...
echo This may take longer due to the larger state space and stress testing scenarios.
echo.

echo Starting statistical model checking...
java -jar tla2tools.jar -config MC_10Nodes.cfg MC_10Nodes.tla -workers auto -maxSetSize 1000000

echo.
echo 10-node stress test completed.
echo Check the output above for any property violations or performance boundary issues.
echo This configuration tests:
echo - Maximum Byzantine ratios (up to 20%% stake)
echo - High network delays and timeout scenarios  
echo - Combined fault scenarios (Byzantine + offline nodes)
echo - Statistical verification of probabilistic properties
echo.
pause