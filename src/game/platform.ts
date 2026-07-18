export interface CursebreakerPlatform {
  loadSave(): Promise<unknown | null>
  writeSave(document: unknown): Promise<void>
  setFullscreen(fullscreen: boolean): Promise<boolean>
  requestExit(document: unknown): Promise<void>
  onExitRequested(callback: () => void): () => void
}

declare global {
  interface Window {
    cursebreakerPlatform: CursebreakerPlatform
  }
}

export function cursebreakerPlatform(): CursebreakerPlatform {
  return window.cursebreakerPlatform
}
