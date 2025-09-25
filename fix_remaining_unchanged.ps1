#!/usr/bin/env pwsh

# Script to fix remaining UNCHANGED clauses in Alpenglow.tla

$filePath = "Alpenglow.tla"
$content = Get-Content $filePath -Raw

# Find all remaining UNCHANGED clauses that don't include statistical sampling variables
$patterns = @(
    "UNCHANGED <<([^>]*)current_window>>[^,]",
    "UNCHANGED <<([^>]*)window_bounds>>[^,]",
    "UNCHANGED <<([^>]*)finalization_times>>[^,]"
)

foreach ($pattern in $patterns) {
    $matches = [regex]::Matches($content, $pattern)
    foreach ($match in $matches) {
        $oldClause = $match.Value
        if (-not $oldClause.Contains("monte_carlo_samples")) {
            $newClause = $oldClause -replace ">>[^,]", ", monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"
            $content = $content -replace [regex]::Escape($oldClause), $newClause
            Write-Host "Fixed: $oldClause"
        }
    }
}

# Write back to file
Set-Content $filePath $content -NoNewline

Write-Host "Fixed remaining UNCHANGED clauses in $filePath"