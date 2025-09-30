# Documentation Cleanup and Organization Script
# Run this to consolidate redundant documentation files

Write-Host "Alpenglow Project - Documentation Cleanup" -ForegroundColor Green
Write-Host "=========================================" -ForegroundColor Green

# Create organized directory structure
$dirs = @("docs/technical", "docs/verification", "docs/performance", "docs/archived")
foreach ($dir in $dirs) {
    if (!(Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force
        Write-Host "Created directory: $dir" -ForegroundColor Yellow
    }
}

# Map of redundant files to consolidate
$redundantFiles = @{
    "FINAL_SUBMISSION_CHECKLIST.md" = "docs/archived/"
    "FINAL_SUBMISSION_STATUS.md" = "docs/archived/"  
    "FINAL_SUBMISSION_SUMMARY.md" = "docs/archived/"
    "hackathon_submission_summary.md" = "docs/archived/"
    "HACKATHON_READINESS_FINAL.md" = "docs/archived/"
    "SUBMISSION_CHECKLIST.md" = "docs/archived/"
    
    "BYZANTINE_DOUBLE_VOTING_FIXES.md" = "docs/technical/"
    "CERTIFICATE_ENHANCEMENT.md" = "docs/technical/"
    "ENHANCED_SAFETY_PROPERTIES.md" = "docs/technical/"
    "LIVENESS_PROPERTIES_IMPLEMENTATION.md" = "docs/technical/"
    "STAKE_WEIGHTED_RELAY_IMPLEMENTATION.md" = "docs/technical/"
    "TIMEOUT_SKIP_CERTIFICATE_IMPLEMENTATION.md" = "docs/technical/"
    "STATISTICAL_SAMPLING_IMPLEMENTATION.md" = "docs/technical/"
    "ENHANCED_OPTIMIZATION_GUIDE.md" = "docs/technical/"
    
    "TECHNICAL_REPORT_FINAL.md" = "docs/verification/"
    "final_validation_report.md" = "docs/verification/"
    "verification_results_simple.md" = "docs/verification/"
    
    "COMPETITIVE_ANALYSIS.md" = "docs/performance/"
}

# Move redundant files to organized locations
foreach ($file in $redundantFiles.Keys) {
    if (Test-Path $file) {
        $destination = $redundantFiles[$file] + $file
        Move-Item $file $destination -Force
        Write-Host "Moved $file to $destination" -ForegroundColor Cyan
    }
}

# Create a consolidated index file
$indexContent = @"
# Alpenglow Verification Project - Documentation Index

This document provides a comprehensive index of all documentation in this project.

## Primary Documents (Root Level)
- **README.md** - Main project overview and setup instructions
- **COMPREHENSIVE_FINAL_REPORT.md** - Complete technical report consolidating all results
- **LICENSE** - Apache 2.0 license
- **CODE_OF_CONDUCT.md** - Project code of conduct
- **CONTRIBUTING.md** - Contribution guidelines
- **SECURITY.md** - Security policy

## Technical Documentation (docs/technical/)
- **BYZANTINE_DOUBLE_VOTING_FIXES.md** - Byzantine behavior modeling and fixes
- **CERTIFICATE_ENHANCEMENT.md** - Certificate system improvements
- **ENHANCED_SAFETY_PROPERTIES.md** - Advanced safety property implementations
- **LIVENESS_PROPERTIES_IMPLEMENTATION.md** - Liveness property verification details
- **STAKE_WEIGHTED_RELAY_IMPLEMENTATION.md** - Erasure coding and relay mechanisms
- **TIMEOUT_SKIP_CERTIFICATE_IMPLEMENTATION.md** - Timeout handling and skip certificates
- **STATISTICAL_SAMPLING_IMPLEMENTATION.md** - Large-scale verification techniques
- **ENHANCED_OPTIMIZATION_GUIDE.md** - Performance optimization strategies

## Verification Results (docs/verification/)
- **TECHNICAL_REPORT_FINAL.md** - Detailed verification results
- **final_validation_report.md** - Final validation summary
- **verification_results_simple.md** - Simplified results overview

## Performance Analysis (docs/performance/)
- **COMPETITIVE_ANALYSIS.md** - Comparison with other consensus protocols

## Archived Documents (docs/archived/)
- Various submission checklists and status files (consolidated into main report)

## Model Configurations
- **MC_*.tla/cfg** - TLA+ model configurations for different test scenarios
- **Properties.tla** - Core property definitions
- **Alpenglow.tla** - Main protocol specification

## Automation Scripts
- **run_full_verification.ps1** - Complete verification suite
- **run_verification_simple.ps1** - Quick verification tests
- **generate_verification_report.ps1** - Report generation

## Results Data
- **performance_results/** - Detailed performance metrics
- **states/** - Model checker state data
- **final_validation_results.json** - Machine-readable results summary

---
Last Updated: September 30, 2025
"@

Set-Content -Path "DOCUMENTATION_INDEX.md" -Value $indexContent
Write-Host "Created DOCUMENTATION_INDEX.md" -ForegroundColor Green

Write-Host "`nCleanup complete! Project is now better organized." -ForegroundColor Green
Write-Host "Primary documents are consolidated in COMPREHENSIVE_FINAL_REPORT.md" -ForegroundColor Yellow