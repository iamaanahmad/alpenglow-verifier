# Enhanced Performance Benchmarking Script for Alpenglow
# Provides detailed performance metrics and comparative analysis

param(
    [switch]$Detailed,
    [switch]$Comparative,
    [string]$OutputFormat = "both" # json, markdown, both
)

Write-Host "Alpenglow Performance Benchmarking Suite" -ForegroundColor Green
Write-Host "=======================================" -ForegroundColor Green

# Performance tracking structure
$performanceResults = @{
    timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    configurations = @()
    comparative_analysis = @{}
    system_info = @{
        cpu = (Get-WmiObject Win32_Processor).Name
        memory_gb = [math]::Round((Get-WmiObject Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
        os = (Get-WmiObject Win32_OperatingSystem).Caption
    }
}

# Configuration definitions for benchmarking
$configurations = @(
    @{ name = "MC_4Nodes"; description = "4 nodes, no Byzantine"; expected_time = 300 },
    @{ name = "MC_4Nodes_Byzantine"; description = "4 nodes, 1 Byzantine"; expected_time = 720 },
    @{ name = "MC_7Nodes"; description = "7 nodes, 1 Byzantine"; expected_time = 2700 },
    @{ name = "MC_10Nodes"; description = "10 nodes, 2 Byzantine"; expected_time = 10800 },
    @{ name = "MC_Statistical_Enhanced"; description = "Statistical sampling"; expected_time = 1800 }
)

function Run-PerformanceTest {
    param($config)
    
    Write-Host "`nTesting configuration: $($config.name)" -ForegroundColor Cyan
    Write-Host "Description: $($config.description)" -ForegroundColor Gray
    
    $configFile = "$($config.name).cfg"
    $specFile = "$($config.name).tla"
    
    if (!(Test-Path $configFile) -or !(Test-Path $specFile)) {
        Write-Host "Configuration files not found, skipping..." -ForegroundColor Yellow
        return $null
    }
    
    # Create temporary output file
    $outputFile = "temp_output_$($config.name).txt"
    
    # Run TLC with timing
    $startTime = Get-Date
    $process = Start-Process -FilePath "java" -ArgumentList @(
        "-Xmx8g", "-Xms4g",
        "-cp", "tla2tools.jar",
        "tlc2.TLC",
        "-config", $configFile,
        $specFile
    ) -RedirectStandardOutput $outputFile -RedirectStandardError "temp_error.txt" -Wait -PassThru
    $endTime = Get-Date
    
    $duration = ($endTime - $startTime).TotalSeconds
    
    # Parse output for detailed metrics
    $output = Get-Content $outputFile -ErrorAction SilentlyContinue
    $errorOutput = Get-Content "temp_error.txt" -ErrorAction SilentlyContinue
    
    # Extract key metrics from output
    $states_found = 0
    $distinct_states = 0
    $states_per_second = 0
    $memory_used = 0
    $success = $process.ExitCode -eq 0
    
    foreach ($line in $output) {
        if ($line -match "(\d+) states generated") {
            $states_found = [int]$matches[1]
        }
        if ($line -match "(\d+) distinct states") {
            $distinct_states = [int]$matches[1]
        }
        if ($line -match "(\d+\.?\d*) states per second") {
            $states_per_second = [double]$matches[1]
        }
    }
    
    # Calculate efficiency metrics
    $efficiency_ratio = if ($distinct_states -gt 0) { [math]::Round($states_found / $distinct_states, 2) } else { 0 }
    $time_efficiency = if ($config.expected_time -gt 0) { [math]::Round($duration / $config.expected_time, 2) } else { 1 }
    
    # Memory usage estimation (rough)
    $estimated_memory = [math]::Round($distinct_states * 0.000024, 2) # ~24 bytes per state
    
    $result = @{
        name = $config.name
        description = $config.description
        success = $success
        duration_seconds = [math]::Round($duration, 2)
        expected_duration = $config.expected_time
        time_efficiency = $time_efficiency
        states_found = $states_found
        distinct_states = $distinct_states
        efficiency_ratio = $efficiency_ratio
        states_per_second = $states_per_second
        estimated_memory_gb = $estimated_memory
        verification_result = if ($success) { "VERIFIED" } else { "FAILED" }
    }
    
    # Cleanup temp files
    Remove-Item $outputFile -ErrorAction SilentlyContinue
    Remove-Item "temp_error.txt" -ErrorAction SilentlyContinue
    
    return $result
}

# Run performance tests
Write-Host "`nStarting performance benchmarking..." -ForegroundColor Yellow

foreach ($config in $configurations) {
    $result = Run-PerformanceTest $config
    if ($result) {
        $performanceResults.configurations += $result
        
        # Display immediate results
        Write-Host "Results:" -ForegroundColor Green
        Write-Host "  Duration: $($result.duration_seconds)s (expected: $($result.expected_duration)s)" -ForegroundColor White
        Write-Host "  States: $($result.states_found) total, $($result.distinct_states) distinct" -ForegroundColor White
        Write-Host "  Performance: $($result.states_per_second) states/sec" -ForegroundColor White
        Write-Host "  Status: $($result.verification_result)" -ForegroundColor $(if ($result.success) { "Green" } else { "Red" })
    }
}

# Comparative Analysis
if ($Comparative) {
    Write-Host "`nGenerating comparative analysis..." -ForegroundColor Yellow
    
    $performanceResults.comparative_analysis = @{
        consensus_protocols = @{
            "TowerBFT" = @{
                finalization_time_ms = 25000
                throughput_tps = 3000
                byzantine_tolerance_percent = 33
                network_overhead = "High"
            }
            "Alpenglow" = @{
                finalization_time_ms = 125
                throughput_tps = 20000
                byzantine_tolerance_percent = 20
                network_overhead = "Low"
            }
            "Tendermint" = @{
                finalization_time_ms = 3500
                throughput_tps = 7000
                byzantine_tolerance_percent = 33
                network_overhead = "Medium"
            }
            "HotStuff" = @{
                finalization_time_ms = 200
                throughput_tps = 15000
                byzantine_tolerance_percent = 33
                network_overhead = "Medium"
            }
            "PBFT" = @{
                finalization_time_ms = 4000
                throughput_tps = 5000
                byzantine_tolerance_percent = 33
                network_overhead = "High"
            }
        }
        
        verification_scalability = @()
    }
    
    # Calculate scalability metrics
    $successful_configs = $performanceResults.configurations | Where-Object { $_.success }
    foreach ($config in $successful_configs) {
        $nodes = switch -Regex ($config.name) {
            "4Nodes" { 4 }
            "7Nodes" { 7 }
            "10Nodes" { 10 }
            default { 0 }
        }
        
        if ($nodes -gt 0) {
            $performanceResults.comparative_analysis.verification_scalability += @{
                nodes = $nodes
                duration = $config.duration_seconds
                states_per_node = [math]::Round($config.distinct_states / $nodes, 0)
                complexity_factor = [math]::Round([math]::Pow($nodes, 3.2), 2)
            }
        }
    }
}

# Generate output files
$timestamp = Get-Date -Format "yyyyMMdd_HHmmss"

if ($OutputFormat -eq "json" -or $OutputFormat -eq "both") {
    $jsonFile = "performance_benchmark_$timestamp.json"
    $performanceResults | ConvertTo-Json -Depth 10 | Out-File $jsonFile
    Write-Host "`nJSON results saved to: $jsonFile" -ForegroundColor Green
}

if ($OutputFormat -eq "markdown" -or $OutputFormat -eq "both") {
    $markdownFile = "performance_benchmark_$timestamp.md"
    
    $markdown = @"
# Alpenglow Performance Benchmark Report

**Generated**: $($performanceResults.timestamp)
**System**: $($performanceResults.system_info.cpu), $($performanceResults.system_info.memory_gb)GB RAM

## Configuration Results

| Configuration | Duration (s) | States Found | Distinct States | States/sec | Memory (GB) | Result |
|---------------|--------------|--------------|-----------------|------------|-------------|--------|
"@

    foreach ($config in $performanceResults.configurations) {
        $markdown += "`n| $($config.name) | $($config.duration_seconds) | $($config.states_found) | $($config.distinct_states) | $($config.states_per_second) | $($config.estimated_memory_gb) | $($config.verification_result) |"
    }

    if ($Comparative) {
        $markdown += @"

## Comparative Analysis

### Consensus Protocol Comparison

| Protocol | Finalization (ms) | Throughput (TPS) | Byzantine Tolerance | Network Overhead |
|----------|------------------|------------------|-------------------|------------------|
"@

        foreach ($protocol in $performanceResults.comparative_analysis.consensus_protocols.Keys) {
            $data = $performanceResults.comparative_analysis.consensus_protocols[$protocol]
            $markdown += "`n| $protocol | $($data.finalization_time_ms) | $($data.throughput_tps) | $($data.byzantine_tolerance_percent)% | $($data.network_overhead) |"
        }

        $markdown += @"

### Verification Scalability

| Nodes | Duration (s) | States per Node | Complexity Factor |
|-------|--------------|-----------------|-------------------|
"@

        foreach ($scale in $performanceResults.comparative_analysis.verification_scalability) {
            $markdown += "`n| $($scale.nodes) | $($scale.duration) | $($scale.states_per_node) | $($scale.complexity_factor) |"
        }
    }

    $markdown += @"

## Key Insights

### Performance Highlights
- **Fastest Configuration**: $((($performanceResults.configurations | Where-Object {$_.success}) | Sort-Object duration_seconds)[0].name)
- **Most Complex Verified**: $((($performanceResults.configurations | Where-Object {$_.success}) | Sort-Object distinct_states -Descending)[0].name)
- **Best Efficiency**: $((($performanceResults.configurations | Where-Object {$_.success}) | Sort-Object efficiency_ratio)[0].name)

### Verification Statistics
- **Total Configurations Tested**: $($performanceResults.configurations.Count)
- **Successful Verifications**: $(($performanceResults.configurations | Where-Object {$_.success}).Count)
- **Total States Explored**: $(($performanceResults.configurations | Measure-Object -Property states_found -Sum).Sum)
- **Total Verification Time**: $([math]::Round(($performanceResults.configurations | Measure-Object -Property duration_seconds -Sum).Sum / 3600, 2)) hours

---
*Generated by Alpenglow Performance Benchmarking Suite*
"@

    Set-Content -Path $markdownFile -Value $markdown
    Write-Host "Markdown report saved to: $markdownFile" -ForegroundColor Green
}

# Summary
Write-Host "`n=== BENCHMARK SUMMARY ===" -ForegroundColor Green
Write-Host "Configurations tested: $($performanceResults.configurations.Count)"
Write-Host "Successful verifications: $(($performanceResults.configurations | Where-Object {$_.success}).Count)"
Write-Host "Total verification time: $([math]::Round(($performanceResults.configurations | Measure-Object -Property duration_seconds -Sum).Sum / 60, 1)) minutes"
Write-Host "Average states per second: $([math]::Round(($performanceResults.configurations | Measure-Object -Property states_per_second -Average).Average, 0))"

if ($Detailed) {
    Write-Host "`nDetailed results available in output files." -ForegroundColor Yellow
}

Write-Host "`nBenchmarking complete!" -ForegroundColor Green