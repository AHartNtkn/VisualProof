import { mountCursebreaker, type CursebreakerDebugState } from '../src/game'
import type { Vec2 } from '../src/view/vec'

declare global {
  interface Window {
    __cursebreakerDebug?: {
      state(): CursebreakerDebugState
      canvasToClient(worldPoint: Vec2): Vec2
      dispose(): void
    }
  }
}

const host = document.getElementById('cursebreaker')
if (!(host instanceof HTMLElement)) throw new Error("missing <main id='cursebreaker'>")

const mounted = mountCursebreaker({ host })
if (new URLSearchParams(window.location.search).has('debug')) {
  window.__cursebreakerDebug = {
    state: () => mounted.debug(),
    canvasToClient: (worldPoint) => mounted.canvasToClient(worldPoint),
    dispose: () => mounted.dispose(),
  }
}
