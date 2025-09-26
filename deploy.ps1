param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("appwrite", "vercel")]
    [string]$Platform
)

Write-Host "Alpenglow Verifier Deployment Script" -ForegroundColor Green
Write-Host "====================================" -ForegroundColor Green

Write-Host "`nPlatform: $Platform" -ForegroundColor Cyan

# Clean and build
Write-Host "`n1. Cleaning previous builds..." -ForegroundColor Blue
if (Test-Path ".next") { Remove-Item -Recurse -Force ".next" }
if (Test-Path "out") { Remove-Item -Recurse -Force "out" }

Write-Host "`n2. Building for static export..." -ForegroundColor Blue
npm run build

if ($LASTEXITCODE -ne 0) {
    Write-Host "✗ Build failed!" -ForegroundColor Red
    exit 1
}

Write-Host "✓ Build successful!" -ForegroundColor Green

# Deploy based on platform
switch ($Platform) {
    "appwrite" {
        Write-Host "`n3. Deploying to Appwrite..." -ForegroundColor Blue
        appwrite sites create-deployment --site-id 68d57dcb001d0230a9a4 --code "." --activate --build-command "npm run build" --install-command "npm install" --output-directory "out"
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✓ Appwrite deployment initiated!" -ForegroundColor Green
            Write-Host "Check your Appwrite console for deployment status." -ForegroundColor Cyan
        } else {
            Write-Host "✗ Appwrite deployment failed!" -ForegroundColor Red
        }
    }
    "vercel" {
        Write-Host "`n3. Deploying to Vercel..." -ForegroundColor Blue
        Write-Host "Make sure you have Vercel CLI installed: npm i -g vercel" -ForegroundColor Yellow
        
        # Check if vercel CLI is available
        try {
            vercel --version | Out-Null
            vercel --prod
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Vercel deployment successful!" -ForegroundColor Green
            } else {
                Write-Host "✗ Vercel deployment failed!" -ForegroundColor Red
            }
        } catch {
            Write-Host "✗ Vercel CLI not found. Install with: npm i -g vercel" -ForegroundColor Red
        }
    }
}

Write-Host "`n4. Post-deployment checklist:" -ForegroundColor Blue
Write-Host "• Clear browser cache (Ctrl+Shift+R)" -ForegroundColor Cyan
Write-Host "• Test all navigation links" -ForegroundColor Cyan
Write-Host "• Verify responsive design" -ForegroundColor Cyan
Write-Host "• Check console for any errors" -ForegroundColor Cyan

Write-Host "`n✓ Deployment process complete!" -ForegroundColor Green