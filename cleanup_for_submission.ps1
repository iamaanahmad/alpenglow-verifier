# Final Cleanup Script for Bounty Submission
Write-Host " Starting Final Cleanup..." -ForegroundColor Cyan
Write-Host ""

$removedCount = 0

# Files to remove
$filesToRemove = @(
    "6_DAY_PERFECTION_PLAN.md",
    "A_PLUS_FINAL_STATUS.md",
    "CLEANUP_ANALYSIS.md",
    "cleanup_project.ps1",
    "cleanup_project_enhanced.ps1",
    "DAY_1_PROGRESS_REPORT.md",
    "DAY_2_PROGRESS_REPORT.md",
    "DAY_3_COMPLETE_REPORT.md",
    "DAY_3_PROGRESS_REPORT.md",
    "DECISION_GUIDE.md",
    "ENHANCED_COMPARATIVE_ANALYSIS.md",
    "FINAL_CLEANUP_PLAN.md",
    "FINAL_PRESENTATION.md",
    "FINAL_TEST_RESULTS.txt",
    "NEXT_STEPS_DAY_4.md",
    "PROPERTY_EXPANSION_PLAN.md",
    "QUICK_VIDEO_GUIDE.md",
    "TIMING_BOUNDS_STRATEGY.md",
    "VIDEO_RECORDING_CHECKLIST.md",
    "bountydetails.txt",
    ".env",
    ".env.local"
)

Write-Host "Removing unnecessary files..." -ForegroundColor Yellow
foreach ($file in $filesToRemove) {
    if (Test-Path $file) {
        Remove-Item $file -Force
        Write-Host "   Removed: $file" -ForegroundColor Green
        $removedCount++
    }
}

# Remove folders
$foldersToRemove = @("docs\archived", "docs\technical", "docs\performance", "docs\verification", ".next", "out")
foreach ($folder in $foldersToRemove) {
    if (Test-Path $folder) {
        Write-Host "Removing $folder..." -ForegroundColor Yellow
        Remove-Item $folder -Recurse -Force
        Write-Host "   Removed: $folder" -ForegroundColor Green
        $removedCount++
    }
}

Write-Host ""
Write-Host "Cleanup Complete! Removed $removedCount items" -ForegroundColor Green
Write-Host ""
Write-Host "Next steps:" -ForegroundColor Cyan
Write-Host "  1. git status" -ForegroundColor White
Write-Host "  2. git add -A" -ForegroundColor White
Write-Host "  3. git commit -m 'Clean project for submission'" -ForegroundColor White
Write-Host "  4. git push" -ForegroundColor White
Write-Host "  5. Record video using VIDEO_SCRIPT.md" -ForegroundColor White
Write-Host ""
