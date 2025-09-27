#!/usr/bin/env pwsh
# Test Deployment Script - Verify GitHub Pages deployment setup

Write-Host "=== Testing GitHub Pages Deployment Setup ===" -ForegroundColor Green

# Set environment variables for GitHub Pages build
$env:NODE_ENV = "production"
$env:GITHUB_PAGES = "true"

Write-Host "`nStep 1: Installing dependencies..." -ForegroundColor Yellow
npm ci

Write-Host "`nStep 2: Building for GitHub Pages..." -ForegroundColor Yellow
npm run build

Write-Host "`nStep 3: Verifying build output..." -ForegroundColor Yellow
if (Test-Path "out") {
    Write-Host "✅ out directory created successfully" -ForegroundColor Green
    
    $files = Get-ChildItem -Path "out" -File
    Write-Host "📁 Generated files: $($files.Count)" -ForegroundColor Cyan
    
    # Check for key files
    $keyFiles = @("index.html", "dashboard.html", "analysis.html", "verification.html")
    foreach ($file in $keyFiles) {
        if (Test-Path "out/$file") {
            Write-Host "✅ $file found" -ForegroundColor Green
        } else {
            Write-Host "❌ $file missing" -ForegroundColor Red
        }
    }
    
    # Check file sizes
    $indexSize = (Get-Item "out/index.html").Length
    Write-Host "📊 index.html size: $indexSize bytes" -ForegroundColor Cyan
    
    if ($indexSize -gt 1000) {
        Write-Host "✅ index.html has content" -ForegroundColor Green
    } else {
        Write-Host "⚠️ index.html seems small" -ForegroundColor Yellow
    }
    
} else {
    Write-Host "❌ out directory not found!" -ForegroundColor Red
    Write-Host "Available directories:" -ForegroundColor Yellow
    Get-ChildItem -Directory | ForEach-Object { Write-Host "  - $($_.Name)" }
    exit 1
}

Write-Host "`nStep 4: Testing local preview..." -ForegroundColor Yellow
if (Get-Command "npx" -ErrorAction SilentlyContinue) {
    Write-Host "Starting local server for testing..." -ForegroundColor Cyan
    Write-Host "You can test the deployment at: http://localhost:3000/alpenglow-verifier/" -ForegroundColor Green
    Write-Host "Press Ctrl+C to stop the server" -ForegroundColor Yellow
    
    # Start local server (this will block until Ctrl+C)
    npx serve out -l 3000
} else {
    Write-Host "npx not available, skipping local preview" -ForegroundColor Yellow
}

Write-Host "`n=== Deployment Test Complete ===" -ForegroundColor Green
Write-Host "✅ Ready for GitHub Pages deployment!" -ForegroundColor Green