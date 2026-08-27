/// <reference types="vite/client" />

interface Window {
  readonly __ORCHARD_WDIO__?: {
    setRenderMode(mode: 'game' | 'raw'): void
  }
}
