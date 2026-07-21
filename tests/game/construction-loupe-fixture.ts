import { ConstructionLoupe, type ConstructionLoupeHost } from '../../src/game/interface/construction-loupe'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import { seedProject } from '../../src/view/relax'
import { InteractiveViewport } from '../../src/game/interface/loupe/interact/viewport'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { comprehensionFixture } from '../app/comprehension-fixture'

const fixture = comprehensionFixture()
const mainMount = document.querySelector<HTMLElement>('#host')!
const mainCanvas = document.querySelector<HTMLCanvasElement>('#proof')!
let activeMount = mainMount
let activeCanvas = mainCanvas
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
  mountInIframe: async (): Promise<void> => {
    loupe?.dispose()
    document.querySelector('#loupe-frame')?.remove()
    const frame = document.createElement('iframe')
    frame.id = 'loupe-frame'
    frame.style.cssText = 'position:fixed;left:0;top:0;z-index:100;width:700px;height:600px;border:0'
    frame.srcdoc = '<!doctype html><html><head></head><body style="margin:0;overflow:hidden;background:#061019"><main id="host" style="position:fixed;inset:0"><canvas id="proof" tabindex="0" style="position:fixed;inset:0;width:100%;height:100%"></canvas></main></body></html>'
    document.body.append(frame)
    await new Promise<void>((resolve) => frame.addEventListener('load', () => resolve(), { once: true }))
    const frameDocument = frame.contentDocument!
    for (const style of document.querySelectorAll('style')) frameDocument.head.append(style.cloneNode(true))
    activeMount = frameDocument.querySelector<HTMLElement>('#host')!
    activeCanvas = frameDocument.querySelector<HTMLCanvasElement>('#proof')!
    loupe = new ConstructionLoupe(host, fixture.bubble, { x: 160, y: 120 })
  },
  setReducedMotion: (enabled: boolean): void => { loupe?.setReducedMotion(enabled) },
  centerMapping: (): { readonly screen: { readonly x: number; readonly y: number }; readonly canvas: { readonly width: number; readonly height: number } } => {
    const draftCanvas = activeMount.querySelector<HTMLCanvasElement>('.cursebreaker-construction-loupe__canvas')!
    const rect = draftCanvas.getBoundingClientRect()
    return {
      screen: loupe!.clientMapping({ x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }).screen,
      canvas: { width: draftCanvas.width, height: draftCanvas.height },
    }
  },
  mapClient: (client: { readonly x: number; readonly y: number }) => loupe!.clientMapping(client),
  lastContextMenuMapping: () => loupe!.debugState().lastContextMenuMapping,
  history: (): { readonly cursor: number; readonly length: number } => {
    const debug = loupe!.debugState()
    return { cursor: debug.cursor, length: debug.historyLength }
  },
  probeInjectedMapper: (): { readonly screen: { readonly x: number; readonly y: number }; readonly world: { readonly x: number; readonly y: number } } | null => {
    const realm = activeMount.ownerDocument.defaultView!
    const probeCanvas = activeMount.ownerDocument.createElement('canvas')
    probeCanvas.width = 640
    probeCanvas.height = 480
    probeCanvas.style.cssText = 'position:fixed;left:20px;top:30px;width:320px;height:240px'
    activeMount.append(probeCanvas)
    let observed: { readonly screen: { readonly x: number; readonly y: number }; readonly world: { readonly x: number; readonly y: number } } | null = null
    const probe = new InteractiveViewport({
      canvas: probeCanvas,
      view: { scale: 1, offsetX: 0, offsetY: 0 },
      engine: () => engine,
      diagram: () => fixture.diagram,
      selectionEnabled: () => false,
      claim: () => null,
      doubleClick: () => false,
      contextMenu: (sample) => { observed = { screen: sample.screen, world: sample.world } },
      pointerChanged: () => {},
      keyDown: () => false,
      selectionChanged: () => {},
      selectionCommitted: () => {},
      mapClient: () => ({ screen: { x: 111, y: 222 }, world: { x: 333, y: 444 } }),
    })
    probeCanvas.dispatchEvent(new realm.MouseEvent('contextmenu', {
      bubbles: true, cancelable: true, clientX: 137, clientY: 83, button: 2,
    }))
    probe.dispose()
    probeCanvas.remove()
    return observed
  },
}

const host: ConstructionLoupeHost = {
  get mount() { return activeMount },
  get canvas() { return activeCanvas },
  diagram: () => fixture.diagram,
  boundary: () => [],
  engine: () => engine,
  view: () => ({ scale: 1, offsetX: 0, offsetY: 0 }),
  context: () => EMPTY_PROOF_CONTEXT,
  orientation: () => 'forward',
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
