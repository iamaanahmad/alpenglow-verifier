Write-Host "Fixing Local Cache Issues" -ForegroundColor Green
Write-Host "=========================" -ForegroundColor Green

Write-Host "`n1. Clearing Next.js cache..." -ForegroundColor Blue
if (Test-Path ".next") {
    Remove-Item -Recurse -Force ".next"
    Write-Host "✓ Removed .next directory" -ForegroundColor Green
} else {
    Write-Host "• .next directory not found" -ForegroundColor Yellow
}

if (Test-Path "out") {
    Remove-Item -Recurse -Force "out"
    Write-Host "✓ Removed out directory" -ForegroundColor Green
}

Write-Host "`n2. Clearing browser cache instructions:" -ForegroundColor Blue
Write-Host "• Chrome/Edge: Ctrl+Shift+R or F12 > Network tab > Disable cache" -ForegroundColor Cyan
Write-Host "• Firefox: Ctrl+Shift+R or F12 > Network tab > Settings > Disable cache" -ForegroundColor Cyan
Write-Host "• Safari: Cmd+Option+R or Develop > Empty Caches" -ForegroundColor Cyan

Write-Host "`n3. For development (with hot reload):" -ForegroundColor Blue
Write-Host "Run: npm run dev" -ForegroundColor Cyan
Write-Host "Server will be at: http://localhost:9002" -ForegroundColor Cyan

Write-Host "`n4. For production testing:" -ForegroundColor Blue
Write-Host "Run: npm run build && npx serve out" -ForegroundColor Cyan

Write-Host "`n✓ Cache cleared! Ready to start development." -ForegroundColor Green