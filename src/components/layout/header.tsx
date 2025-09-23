'use client';

import { SidebarTrigger } from '@/components/ui/sidebar';

export default function Header() {
  return (
    <header className="sticky top-0 z-10 flex h-14 items-center gap-4 border-b bg-background/95 px-4 backdrop-blur supports-[backdrop-filter]:bg-background/60 md:hidden">
      <SidebarTrigger />
      <h1 className="text-lg font-semibold">Alpenglow Verifier</h1>
    </header>
  );
}
