Write-Host "Deployment Readiness Check" -ForegroundColor Green
Write-Host "=========================" -ForegroundColor Green

Write-Host "`n1. Testing build..." -ForegroundColor Blue
npm run build

Write-Host "`n2. Checking key files..." -ForegroundColor Blue
if (Test-Path "package.json") { Write-Host "✓ package.json" -ForegroundColor Green }
if (Test-Path "next.config.ts") { Write-Host "✓ next.config.ts" -ForegroundColor Green }
if (Test-Path "src/app/layout.tsx") { Write-Host "✓ src/app/layout.tsx" -ForegroundColor Green }
if (Test-Path "src/app/page.tsx") { Write-Host "✓ src/app/page.tsx" -ForegroundColor Green }

Write-Host "`n3. Deployment tips:" -ForegroundColor Blue
Write-Host "• Clear browser cache: Ctrl+Shift+R" -ForegroundColor Cyan
Write-Host "• Make sure deployment platform supports Next.js 15" -ForegroundColor Cyan
Write-Host "• Use Node.js 18+ on deployment platform" -ForegroundColor Cyan

Write-Host "`n✓ Check complete!" -ForegroundColor Green