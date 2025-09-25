import type {Metadata} from 'next';
import './globals.css';
import { Toaster } from '@/components/ui/toaster';
import { cn } from '@/lib/utils';
import Header from '@/components/layout/header';
import MainNav from '@/components/layout/main-nav';
import { Sidebar, SidebarContent, SidebarHeader, SidebarInset, SidebarProvider } from '@/components/ui/sidebar';
import { Mountain } from 'lucide-react';
import Link from 'next/link';

export const metadata: Metadata = {
  title: 'Alpenglow Verifier',
  description: 'Formal Verification System for Solana Alpenglow',
};

// Force cache busting
const cacheVersion = Date.now();

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en" className="dark" suppressHydrationWarning>
      <head>
        <link rel="preconnect" href="https://fonts.googleapis.com" />
        <link rel="preconnect" href="https://fonts.gstatic.com" crossOrigin="anonymous" />
        <meta name="cache-version" content={cacheVersion.toString()} />
      </head>
      <body className={cn('antialiased min-h-screen')}>
        <SidebarProvider>
          <Sidebar>
            <SidebarHeader>
              <Link href="/dashboard" className="flex items-center gap-2 p-2">
                <Mountain className="w-8 h-8 text-primary" />
                <h1 className="text-xl font-semibold text-primary">Alpenglow Verifier</h1>
              </Link>
            </SidebarHeader>
            <SidebarContent>
              <MainNav />
            </SidebarContent>
          </Sidebar>
          <SidebarInset>
            <Header />
            <main className="p-4 lg:p-6 bg-background">
              {children}
            </main>
          </SidebarInset>
        </SidebarProvider>
        <Toaster />
      </body>
    </html>
  );
}
