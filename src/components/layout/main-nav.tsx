'use client';

import { usePathname } from 'next/navigation';
import { SidebarMenu, SidebarMenuItem, SidebarMenuButton } from '@/components/ui/sidebar';
import { LayoutDashboard, FileCode2, ShieldCheck, PlayCircle, BarChart3 } from 'lucide-react';
import Link from 'next/link';

const navItems = [
  { href: '/', label: 'Dashboard', icon: LayoutDashboard },
  { href: '/specification', label: 'Specification', icon: FileCode2 },
  { href: '/properties', label: 'Properties', icon: ShieldCheck },
  { href: '/verification', label: 'Verification Runs', icon: PlayCircle },
  { href: '/analysis', label: 'Analysis', icon: BarChart3 },
];

export default function MainNav() {
  const pathname = usePathname();

  return (
    <SidebarMenu>
      {navItems.map((item) => (
        <SidebarMenuItem key={item.href}>
          <Link href={item.href} legacyBehavior passHref>
            <SidebarMenuButton
              isActive={pathname === item.href}
              tooltip={item.label}
            >
              <item.icon />
              <span>{item.label}</span>
            </SidebarMenuButton>
          </Link>
        </SidebarMenuItem>
      ))}
    </SidebarMenu>
  );
}
