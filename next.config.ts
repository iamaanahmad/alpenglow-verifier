import type {NextConfig} from 'next';

const nextConfig: NextConfig = {
  /* config options here */
  typescript: {
    ignoreBuildErrors: true,
  },
  eslint: {
    ignoreDuringBuilds: true,
  },
  // Dynamic configuration based on environment
  ...(process.env.NODE_ENV === 'production' && (process.env.GITHUB_PAGES === 'true' || process.env.CI) ? {
    output: 'export',
    trailingSlash: false,
    distDir: 'out',
    basePath: '/alpenglow-verifier',
    assetPrefix: '/alpenglow-verifier/',
  } : {}),
  images: {
    unoptimized: true,
    remotePatterns: [
      {
        protocol: 'https',
        hostname: 'placehold.co',
        port: '',
        pathname: '/**',
      },
      {
        protocol: 'https',
        hostname: 'images.unsplash.com',
        port: '',
        pathname: '/**',
      },
      {
        protocol: 'https',
        hostname: 'picsum.photos',
        port: '',
        pathname: '/**',
      },
    ],
  },
};

export default nextConfig;
