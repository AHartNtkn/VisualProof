export interface CursebreakerPlatform {
  loadSave(): Promise<unknown | null>
  writeSave(document: unknown): Promise<void>
  replaceInvalidSave(document: unknown): Promise<void>
  rendererReady(): Promise<void>
  reportStartupFailure(message: string): Promise<void>
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
