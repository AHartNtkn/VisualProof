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

  const mounted = await mountCursebreaker({ host, platform: cursebreakerPlatform() })
  if (new URLSearchParams(window.location.search).has('debug')) {
    window.__cursebreakerDebug = {
      state: () => mounted.debug(),
      dispatch: (action) => mounted.dispatch(action),
      settled: () => mounted.settled(),
      canvasToClient: (worldPoint) => mounted.canvasToClient(worldPoint),
      dispose: () => mounted.dispose(),
    }
  }
}

function showLaunchFailure(error: unknown): void {
  console.error('Failed to start Cursebreaker', error)

  const host = document.getElementById('cursebreaker')
  if (!(host instanceof HTMLElement)) return

  const failure = document.createElement('section')
  failure.className = 'curse-launch-failure'
  failure.setAttribute('role', 'alert')

  const heading = document.createElement('h1')
  heading.textContent = 'Cursebreaker could not start'

  const message = document.createElement('p')
  message.textContent = 'Close this window and try again.'

  failure.append(heading, message)
  host.dataset.launchState = 'failed'
  host.replaceChildren(failure)
}

void boot().catch(showLaunchFailure)
