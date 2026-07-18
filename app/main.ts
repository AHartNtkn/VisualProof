import {
  cursebreakerPlatform,
  mountCursebreaker,
  type CursebreakerDebugState,
} from '../src/game'
import type { GameAction } from '../src/game/controller'
import type { Vec2 } from '../src/view/vec'

declare global {
  interface Window {
    __cursebreakerDebug?: {
      state(): CursebreakerDebugState
      dispatch(action: GameAction): void
      settled(): Promise<void>
      canvasToClient(worldPoint: Vec2): Vec2
      dispose(): void
    }
  }
}

async function boot(): Promise<void> {
  const host = document.getElementById('cursebreaker')
  if (!(host instanceof HTMLElement)) throw new Error("missing <main id='cursebreaker'>")

  const platform = cursebreakerPlatform()
  const mounted = await mountCursebreaker({ host, platform })
  if (new URLSearchParams(window.location.search).has('debug')) {
    window.__cursebreakerDebug = {
      state: () => mounted.debug(),
      dispatch: (action) => mounted.dispatch(action),
      settled: () => mounted.settled(),
      canvasToClient: (worldPoint) => mounted.canvasToClient(worldPoint),
      dispose: () => mounted.dispose(),
    }
  }
  await platform.rendererReady()
}

async function reportLaunchFailure(error: unknown): Promise<void> {
  console.error('Failed to start Cursebreaker', error)
  const message = error instanceof Error ? `${error.name}: ${error.message}` : String(error)
  await cursebreakerPlatform().reportStartupFailure(message)
}

void boot().catch(reportLaunchFailure).catch((error: unknown) => {
  console.error('Failed to report Cursebreaker startup failure', error)
})
