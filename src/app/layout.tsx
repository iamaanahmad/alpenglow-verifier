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
  title: 'Alpenglow Verifier - Formal Verification System',
  description: 'World\'s first complete formal verification of Solana\'s Alpenglow consensus protocol with mathematical guarantees',
  icons: {
    icon: [
      { url: '/alpenglow-verifier/favicon.svg', type: 'image/svg+xml' },
      { url: '/alpenglow-verifier/favicon.ico', sizes: '32x32' }
    ]
  },
  manifest: '/alpenglow-verifier/site.webmanifest',
  keywords: ['Alpenglow', 'Solana', 'Formal Verification', 'TLA+', 'Consensus Protocol', 'Blockchain Security'],
  authors: [{ name: 'Aman Ahmad' }],
  creator: 'Aman Ahmad',
  openGraph: {
    title: 'Alpenglow Verifier - Mathematical Proof of Consensus Security',
    description: 'World\'s first complete formal verification of Solana\'s Alpenglow consensus protocol',
    type: 'website',
    locale: 'en_US',
  },
  twitter: {
    card: 'summary_large_image',
    title: 'Alpenglow Verifier - Formal Verification System',
    description: 'Mathematical proof that Alpenglow consensus protocol works correctly under all conditions',
  },
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
        <link rel="icon" href="/alpenglow-verifier/favicon.svg" type="image/svg+xml" />
        <link rel="icon" href="/alpenglow-verifier/favicon.ico" sizes="32x32" />
        <link rel="manifest" href="/alpenglow-verifier/site.webmanifest" />
        <meta name="cache-version" content={cacheVersion.toString()} />
        <meta name="theme-color" content="#0f172a" />
        <meta name="msapplication-TileColor" content="#0f172a" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
      </head>
      <body className={cn('antialiased min-h-screen')}>
        <SidebarProvider>
          <Sidebar>
            <SidebarHeader>
              <Link href="/" className="flex items-center gap-2 p-2">
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
