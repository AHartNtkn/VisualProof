import { ConstructionLoupe, type ConstructionLoupeHost } from '../../src/game/interface/construction-loupe'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import { seedProject } from '../../src/view/relax'
import { comprehensionFixture } from '../app/comprehension-fixture'

const fixture = comprehensionFixture()
const mount = document.querySelector<HTMLElement>('#host')!
const canvas = document.querySelector<HTMLCanvasElement>('#proof')!
const engine = mkEngine(fixture.diagram, [])
seedProject(engine)
let loupe: ConstructionLoupe | null = null

const state = {
  closed: 0,
  commits: 0,
  lastRule: null as string | null,
  reopen: (): void => {
    loupe?.dispose()
    loupe = new ConstructionLoupe(host, fixture.bubble, { x: 360, y: 180 })
  },
  setReducedMotion: (enabled: boolean): void => { loupe?.setReducedMotion(enabled) },
  centerMapping: (): { readonly screen: { readonly x: number; readonly y: number }; readonly canvas: { readonly width: number; readonly height: number } } => {
    const draftCanvas = mount.querySelector<HTMLCanvasElement>('.cursebreaker-construction-loupe__canvas')!
    const rect = draftCanvas.getBoundingClientRect()
    return {
      screen: loupe!.clientMapping({ x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }).screen,
      canvas: { width: draftCanvas.width, height: draftCanvas.height },
    }
  },
  history: (): { readonly cursor: number; readonly length: number } => {
    const debug = loupe!.debugState()
    return { cursor: debug.cursor, length: debug.historyLength }
  },
}

const host: ConstructionLoupeHost = {
  mount,
  canvas,
  diagram: () => fixture.diagram,
  boundary: () => [],
  engine: () => engine,
  view: () => ({ scale: 1, offsetX: 0, offsetY: 0 }),
  context: () => ({ theorems: new Map(), relations: new Map() }),
  theme: () => DARK,
  apply: (step) => { state.commits++; state.lastRule = step.rule },
  refuse: () => {},
  changed: () => {},
  openChanged: (open) => { if (!open) state.closed++ },
  reducedMotion: () => false,
}

declare global {
  interface Window {
    __constructionLoupeFixture: typeof state
  }
}

window.__constructionLoupeFixture = state
state.reopen()

const frame = (now: number): void => {
  loupe?.frame(now)
  requestAnimationFrame(frame)
}
requestAnimationFrame(frame)
