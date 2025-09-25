#!/usr/bin/env pwsh

# Script to fix all UNCHANGED clauses in Alpenglow.tla to include statistical sampling variables

$filePath = "Alpenglow.tla"
$content = Get-Content $filePath -Raw

# Define the old and new UNCHANGED clause patterns
$oldPattern1 = "UNCHANGED <<stake, votes, finalized, block_proposals, certs, leader, slot, byzantine_behaviors, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window>>"
$newPattern1 = "UNCHANGED <<stake, votes, finalized, block_proposals, certs, leader, slot, byzantine_behaviors, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"

$oldPattern2 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window>>"
$newPattern2 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"

$oldPattern3 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window>>"
$newPattern3 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"

$oldPattern4 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window>>"
$newPattern4 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, finalization_times, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"

$oldPattern5 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, windows, window_bounds, current_window>>"
$newPattern5 = "UNCHANGED <<stake, votes, finalized, block_proposals, received_blocks, certs, leader, slot, byzantine_behaviors, relay_graph, network_topology, timeouts, skip_certs, slot_start_time, current_time, round_start_time, node_responsiveness, network_delays, partial_sync_violations, windows, window_bounds, current_window, monte_carlo_samples, confidence_intervals, sampling_history, property_verification_stats>>"

# Apply replacements
$content = $content -replace [regex]::Escape($oldPattern1), $newPattern1
$content = $content -replace [regex]::Escape($oldPattern2), $newPattern2
$content = $content -replace [regex]::Escape($oldPattern3), $newPattern3
$content = $content -replace [regex]::Escape($oldPattern4), $newPattern4
$content = $content -replace [regex]::Escape($oldPattern5), $newPattern5

# Write back to file
Set-Content $filePath $content -NoNewline

Write-Host "Fixed UNCHANGED clauses in $filePath"