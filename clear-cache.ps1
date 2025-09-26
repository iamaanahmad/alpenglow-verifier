#!/usr/bin/env pwsh

Write-Host "Clearing Next.js cache and rebuilding..." -ForegroundColor Green

# Remove Next.js cache and build directories
if (Test-Path ".next") {
    Remove-Item -Recurse -Force ".next"
    Write-Host "Removed .next directory" -ForegroundColor Yellow
}

if (Test-Path "node_modules/.cache") {
    Remove-Item -Recurse -Force "node_modules/.cache"
    Write-Host "Removed node_modules/.cache directory" -ForegroundColor Yellow
}

# Clear npm cache
npm cache clean --force
Write-Host "Cleared npm cache" -ForegroundColor Yellow

# Reinstall dependencies
Write-Host "Reinstalling dependencies..." -ForegroundColor Blue
npm install

# Build the project
Write-Host "Building project..." -ForegroundColor Blue
npm run build

Write-Host "Cache cleared and project rebuilt successfully!" -ForegroundColor Green
Write-Host "You can now run 'npm run dev' to start the development server" -ForegroundColor Cyan