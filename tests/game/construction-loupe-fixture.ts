import { ConstructionLoupe, type ConstructionLoupeHost } from '../../src/game/interface/construction-loupe'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import { seedProject } from '../../src/view/relax'
import { existentialStubs } from '../../src/view/wires'
import { InteractiveViewport } from '../../src/interaction/controllers/viewport'
import type { PointerSample } from '../../src/interaction/controllers/viewport'
import type { Hit } from '../../src/interaction/hittest'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram } from '../../src/kernel/diagram/diagram'

const fixture = (() => {
  const builder = new DiagramBuilder()
  const binder = builder.bubble(builder.root, 0)
  const hostAtom = builder.atom(binder, binder)
  const guard = builder.cut(binder)
  const bubble = builder.bubble(guard, 2)
  for (let copy = 0; copy < 2; copy++) {
    const atom = builder.atom(bubble, bubble)
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    builder.wire(bubble, [{ node: atom, port: { kind: 'arg', index: 1 } }])
  }
  const context = builder.ref(builder.root, 'context', 1)
  const parameter = builder.wire(builder.root, [{ node: context, port: { kind: 'arg', index: 0 } }])
  const inaccessible = builder.bubble(builder.root, 0)
  const inaccessibleAtom = builder.atom(inaccessible, inaccessible)
  return {
    diagram: builder.build(), binder, hostAtom, guard, bubble, parameter,
    inaccessible, inaccessibleAtom,
  }
})()
const mainMount = document.querySelector<HTMLElement>('#host')!
const mainCanvas = document.querySelector<HTMLCanvasElement>('#proof')!
let activeMount = mainMount
let activeCanvas = mainCanvas
const engine = mkEngine(fixture.diagram, [])
seedProject(engine)
let loupe: ConstructionLoupe | null = null
let liveDiagram: Diagram = fixture.diagram
let hostSelection: readonly Hit[] = []

const state = {
  closed: 0,
  commits: 0,
  lastRule: null as string | null,
  reopen: (): void => {
    loupe?.dispose()
    liveDiagram = fixture.diagram
    hostSelection = []
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
  regions: () => loupe!.debugState().draftRegions,
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
  probeSharedLifecycle: (): { readonly cancellations: number; readonly modifiers: readonly boolean[] } => {
    const realm = activeMount.ownerDocument.defaultView!
    const probeCanvas = activeMount.ownerDocument.createElement('canvas')
    probeCanvas.style.cssText = 'position:fixed;left:0;top:0;width:100px;height:100px'
    activeMount.append(probeCanvas)
    let cancellations = 0
    const modifiers: boolean[] = []
    const probe = new InteractiveViewport({
      canvas: probeCanvas,
      view: { scale: 1, offsetX: 0, offsetY: 0 },
      engine: () => engine,
      diagram: () => fixture.diagram,
      selectionEnabled: () => false,
      claim: () => ({
        still: 'claim', blocksPassiveRelaxation: false,
        move: () => {}, release: () => {}, cancel: () => { cancellations++ },
      }),
      doubleClick: () => false,
      contextMenu: () => {},
      pointerChanged: () => {},
      modifiersChanged: (held) => { modifiers.push(held) },
      keyDown: () => false,
      selectionChanged: () => {},
      selectionCommitted: () => {},
      keyScope: 'window',
    })
    probeCanvas.dispatchEvent(new realm.PointerEvent('pointerdown', {
      bubbles: true, cancelable: true, pointerId: 41, button: 0, clientX: 5, clientY: 5,
    }))
    realm.dispatchEvent(new realm.Event('blur'))
    probeCanvas.dispatchEvent(new realm.PointerEvent('pointerdown', {
      bubbles: true, cancelable: true, pointerId: 42, button: 0, clientX: 5, clientY: 5,
    }))
    Object.defineProperty(activeMount.ownerDocument, 'visibilityState', {
      value: 'hidden', configurable: true,
    })
    activeMount.ownerDocument.dispatchEvent(new realm.Event('visibilitychange'))
    Reflect.deleteProperty(activeMount.ownerDocument, 'visibilityState')
    realm.dispatchEvent(new realm.KeyboardEvent('keydown', { key: 'Control', ctrlKey: true }))
    realm.dispatchEvent(new realm.KeyboardEvent('keyup', { key: 'Control', ctrlKey: false }))
    probe.dispose()
    probeCanvas.remove()
    return { cancellations, modifiers }
  },
  probeHostPatternClaims: (): {
    readonly wireClaimWins: boolean
    readonly nullarySelectedClaimed: boolean
    readonly unselectedClaimed: boolean
    readonly inaccessibleClaimed: boolean
    readonly importedSnapshots: number
    readonly importedExactTarget: boolean
    readonly cancelledSnapshots: number
    readonly staleSnapshots: number
  } => {
    const nodeSample = (node: string): PointerSample => {
      const world = engine.bodies.get(node)?.pos
      if (world === undefined) throw new Error(`missing fixture body '${node}'`)
      return {
        pointerId: 71,
        button: 0,
        client: { x: 40, y: 40 },
        screen: { x: 40, y: 40 },
        world: { ...world },
        hit: { kind: 'node', id: node },
        shiftKey: false,
        ctrlKey: false,
        altKey: false,
        metaKey: false,
      }
    }
    const destinationSample = (): PointerSample => {
      const canvas = activeMount.querySelector<HTMLCanvasElement>('.cursebreaker-construction-loupe__canvas')!
      const rect = canvas.getBoundingClientRect()
      const client = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
      const mapped = loupe!.clientMapping(client)
      return {
        pointerId: 71,
        button: 0,
        client,
        screen: mapped.screen,
        world: mapped.world,
        hit: null,
        shiftKey: false,
        ctrlKey: false,
        altKey: false,
        metaKey: false,
      }
    }

    state.reopen()
    hostSelection = [{ kind: 'node', id: fixture.hostAtom }]
    const selectedSample = nodeSample(fixture.hostAtom)
    const parameterPoint = existentialStubs(engine).find((stub) => stub.wid === fixture.parameter)?.from
    if (parameterPoint === undefined) throw new Error('missing fixture parameter marker')
    const wireClaim = loupe!.hostClaim({ ...selectedSample, world: parameterPoint })
    const wireClaimWins = wireClaim?.blocksPassiveRelaxation === true
    wireClaim?.cancel()

    const selectedClaim = loupe!.hostClaim(selectedSample)
    const nullarySelectedClaimed = selectedClaim?.blocksPassiveRelaxation === false
    selectedClaim?.cancel()

    hostSelection = []
    const unselectedClaimed = loupe!.hostClaim(selectedSample) !== null
    hostSelection = [{ kind: 'node', id: fixture.inaccessibleAtom }]
    const inaccessibleClaimed = loupe!.hostClaim(nodeSample(fixture.inaccessibleAtom)) !== null

    state.reopen()
    hostSelection = [{ kind: 'node', id: fixture.hostAtom }]
    const importedBefore = loupe!.debugState().historyLength
    const importClaim = loupe!.hostClaim(nodeSample(fixture.hostAtom))
    const importDestination = destinationSample()
    importClaim?.move(importDestination)
    importClaim?.release(importDestination, true)
    const imported = loupe!.debugState()

    state.reopen()
    hostSelection = [{ kind: 'node', id: fixture.hostAtom }]
    const cancelledBefore = loupe!.debugState().historyLength
    const cancelClaim = loupe!.hostClaim(nodeSample(fixture.hostAtom))
    cancelClaim?.move(destinationSample())
    cancelClaim?.cancel()
    const cancelledAfter = loupe!.debugState().historyLength

    state.reopen()
    hostSelection = [{ kind: 'node', id: fixture.hostAtom }]
    const staleBefore = loupe!.debugState().historyLength
    const staleClaim = loupe!.hostClaim(nodeSample(fixture.hostAtom))
    const staleDestination = destinationSample()
    staleClaim?.move(staleDestination)
    liveDiagram = mkDiagram({
      root: fixture.diagram.root,
      regions: { ...fixture.diagram.regions },
      nodes: { ...fixture.diagram.nodes },
      wires: { ...fixture.diagram.wires },
    })
    staleClaim?.release(staleDestination, true)
    const staleAfter = loupe!.debugState().historyLength
    liveDiagram = fixture.diagram

    return {
      wireClaimWins,
      nullarySelectedClaimed,
      unselectedClaimed,
      inaccessibleClaimed,
      importedSnapshots: imported.historyLength - importedBefore,
      importedExactTarget: imported.binders.some(([, target]) => target === fixture.binder),
      cancelledSnapshots: cancelledAfter - cancelledBefore,
      staleSnapshots: staleAfter - staleBefore,
    }
  },
}

const host: ConstructionLoupeHost = {
  get mount() { return activeMount },
  get canvas() { return activeCanvas },
  diagram: () => liveDiagram,
  boundary: () => [],
  engine: () => engine,
  selection: () => hostSelection,
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
