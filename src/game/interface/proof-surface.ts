import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import type { ProofStep } from '../../kernel/proof/step'
import { singleStepAction, type ProofAction } from '../../kernel/proof/action'
import type { ProofContext } from '../../kernel/proof/context'
import type { Engine } from '../../view/engine'
import { carryOver, mkEngine } from '../../view/engine'
import { seedProject } from '../../view/relax'
import type { Shape, Theme } from '../../view/paint'
import { highlightGroup, paint } from '../../view/paint'
import { drawShapes } from '../../view/canvas'
import { existentialStubs, legPaths } from '../../view/wires'
import type { Vec2 } from '../../view/vec'
import type { PuzzleDefinition } from '../types'
import type { ArtifactAction } from '../artifact'
import type { GameSessionAction } from '../session'
import { planArtifactDrop, type ArtifactDropPlan, type ArtifactDropTarget } from './artifact-drop'
import { ConstructionLoupe, type ConstructionLoupeDebug } from './construction-loupe'
import { hitTest, type Hit } from '../../interaction/hittest'
import { isHitSelected } from '../../interaction/controllers/brush'
import {
  InteractiveViewport,
  type MutableView,
  type PointerClaim,
  type PointerSample,
} from '../../interaction/controllers/viewport'
import { GameProofMoveController } from './proof-moves'
import {
  GameProofMotion,
  type ProofMotionDebug,
  type ProofMotionPreferences,
} from './proof-motion'
import './proof-surface.css'

export type ProofCanvasRect = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
}

export function mapProofClient(
  client: Vec2,
  rect: ProofCanvasRect,
  canvas: { readonly width: number; readonly height: number },
  view: Readonly<MutableView>,
): { readonly screen: Vec2; readonly world: Vec2 } {
  const scaleX = rect.width > 0 ? canvas.width / rect.width : 1
  const scaleY = rect.height > 0 ? canvas.height / rect.height : 1
  const screen = {
    x: (client.x - rect.left) * scaleX,
    y: (client.y - rect.top) * scaleY,
  }
  return {
    screen,
    world: {
      x: (screen.x - view.offsetX) / view.scale,
      y: (screen.y - view.offsetY) / view.scale,
    },
  }
}

export const proofSurfaceInputAllowed = (
  constructionOpen: boolean,
  motionPlaying: boolean,
  hostAllowed: boolean,
): boolean => !constructionOpen && !motionPlaying && hostAllowed

export const proofSurfaceViewportAllowed = (
  motionPlaying: boolean,
  hostAllowed: boolean,
): boolean => !motionPlaying && hostAllowed

export function routeGameProofClaim(
  construction: Pick<ConstructionLoupe, 'hostClaim'> | null,
  moves: Pick<GameProofMoveController, 'claim'>,
  sample: PointerSample,
): PointerClaim | null {
  return construction === null ? moves.claim(sample) : construction.hostClaim(sample)
}

export type GameProofViewportModel = {
  readonly host: HTMLElement
  readonly overlayHost?: HTMLElement
  diagram(): Diagram
  boundary(): readonly WireId[]
  context(): ProofContext
  artifactAvailable(id: PuzzleDefinition['id']): boolean
  orientation(): 'forward' | 'backward'
  theme(): Theme
  fuel(): number
  prepare(action: GameSessionAction): () => void
  motionPreferences(): ProofMotionPreferences
  inputAllowed(): boolean
  refuse(text: string, pointer: Vec2): void
  changed(): void
  constructionChanged?(open: boolean): void
}

export type GameProofViewportDebug = {
  readonly rebuilds: number
  readonly construction: ConstructionLoupeDebug | null
  readonly view: Readonly<MutableView>
  readonly selection: readonly Hit[]
  readonly pins: readonly string[]
  readonly motion: ProofMotionDebug
}

const containingRegionAt = (engine: Engine, diagram: Diagram, point: Vec2): RegionId => {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

const hoverBinder = (diagram: Diagram, hit: Hit): RegionId | null => {
  if (hit.kind === 'node') {
    const node = diagram.nodes[hit.id]
    return node?.kind === 'atom' ? node.binder : null
  }
  if (hit.kind === 'region') return diagram.regions[hit.id]?.kind === 'bubble' ? hit.id : null
  return null
}

/** One active-puzzle proof surface. Runtime/controller orchestration stays outside. */
export class GameProofViewport {
  readonly canvas: HTMLCanvasElement
  readonly view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
  readonly interaction: InteractiveViewport
  readonly motion: GameProofMotion
  readonly #model: GameProofViewportModel
  readonly #window: Window & typeof globalThis
  readonly #context: CanvasRenderingContext2D
  readonly #moves: GameProofMoveController
  #engine: Engine
  #construction: ConstructionLoupe | null = null
  #disposed = false
  #rebuilds = 1

  constructor(model: GameProofViewportModel) {
    this.#model = model
    const document = model.host.ownerDocument
    const viewportWindow = document.defaultView
    if (viewportWindow === null) throw new Error('the game proof surface must belong to a live window')
    this.#window = viewportWindow
    this.canvas = document.createElement('canvas')
    this.canvas.className = 'curse-game-proof-canvas'
    this.canvas.setAttribute('aria-label', 'Seal under examination')
    model.host.append(this.canvas)
    const context = this.canvas.getContext('2d')
    if (context === null) throw new Error('the game proof canvas has no 2d context')
    this.#context = context
    this.#engine = mkEngine(model.diagram(), model.boundary())
    seedProject(this.#engine)
    this.motion = new GameProofMotion({
      preferences: model.motionPreferences,
      diagram: model.diagram,
      engine: () => this.#engine,
      theme: model.theme,
    })
    this.#moves = new GameProofMoveController({
      host: model.overlayHost ?? document.body,
      active: () => this.#inputAllowed(),
      diagram: model.diagram,
      engine: () => this.#engine,
      viewScale: () => this.view.scale,
      selection: () => this.interaction.selection,
      setSelection: (selection) => this.interaction.setSelection(selection),
      context: model.context,
      apply: (action) => this.#applyAction(action),
      refuse: model.refuse,
      theme: model.theme,
      fuel: model.fuel,
      openConstruction: (bubble, pointer) => this.openConstruction(bubble, pointer),
    })
    this.interaction = new InteractiveViewport({
      canvas: this.canvas,
      view: this.view,
      engine: () => this.#engine,
      diagram: model.diagram,
      selectionEnabled: () => true,
      brushMode: (sample) => sample.shiftKey ? 'deselect' : 'select',
      claim: (sample) => routeGameProofClaim(this.#construction, this.#moves, sample),
      doubleClick: (sample) => this.#construction === null && this.#moves.doubleClick(sample),
      contextMenu: (sample) => { if (this.#construction === null) this.#moves.contextMenu(sample) },
      pointerChanged: (client) => this.#construction?.hostPointerChanged(client),
      keyDown: (sample) => {
        if (this.#construction !== null) return true
        if (sample.key === 'Home') {
          this.interaction.resetZoom()
          model.changed()
          return true
        }
        return this.#moves.keyDown(sample)
      },
      selectionChanged: () => {
        this.#moves.cancel()
        model.changed()
      },
      selectionCommitted: model.changed,
      mapClient: (client) => this.mapClient(client),
      inputAllowed: () => proofSurfaceViewportAllowed(this.motion.playing, model.inputAllowed()),
      physicsEnabled: () => this.#construction === null,
      zoomEnabled: () => this.#construction === null,
      keyScope: 'focused',
    })
  }

  get engine(): Engine { return this.#engine }
  get playing(): boolean { return this.motion.playing }
  get editing(): boolean { return this.#construction !== null }

  mapClient(client: Vec2): { readonly screen: Vec2; readonly world: Vec2 } {
    const rect = this.canvas.getBoundingClientRect()
    return mapProofClient(client, {
      left: rect.left,
      top: rect.top,
      width: rect.width,
      height: rect.height,
    }, this.canvas, this.view)
  }

  artifactTargetAt(client: Vec2): ArtifactDropTarget {
    const rect = this.canvas.getBoundingClientRect()
    if (
      client.x < rect.left
      || client.x >= rect.right
      || client.y < rect.top
      || client.y >= rect.bottom
    ) return { hit: null, containingRegion: null }
    const mapped = this.mapClient(client)
    return {
      hit: hitTest(this.#engine, mapped.world, { scale: this.view.scale }),
      containingRegion: containingRegionAt(this.#engine, this.#model.diagram(), mapped.world),
    }
  }

  dropArtifact(artifact: PuzzleDefinition, client: Vec2): ArtifactDropPlan {
    if (this.#disposed) return {
      ok: false,
      code: 'invalid-drop-target',
      reason: 'the proof surface is closed',
    }
    if (!this.#inputAllowed()) {
      const result: ArtifactDropPlan = {
        ok: false,
        code: 'no-legal-artifact-operation',
        reason: 'finish the current seal interaction before using an artifact',
      }
      this.#model.refuse(result.reason, client)
      return result
    }
    const result = planArtifactDrop({
      artifact,
      available: this.#model.artifactAvailable(artifact.id),
      diagram: this.#model.diagram(),
      target: this.artifactTargetAt(client),
      fuel: this.#model.fuel(),
    })
    if (!result.ok) {
      this.#model.refuse(result.reason, client)
      return result
    }
    this.#applyArtifactAction(result.action)
    return result
  }

  openConstruction(bubble: RegionId, invocation: Vec2): boolean {
    if (this.#disposed || this.#construction !== null || !this.#inputAllowed()) return false
    let construction: ConstructionLoupe
    construction = new ConstructionLoupe({
      mount: this.#model.overlayHost ?? this.#model.host.ownerDocument.body,
      canvas: this.canvas,
      diagram: this.#model.diagram,
      boundary: this.#model.boundary,
      engine: () => this.#engine,
      selection: () => this.interaction.selection,
      view: () => this.view,
      context: this.#model.context,
      orientation: this.#model.orientation,
      theme: this.#model.theme,
      apply: (step) => this.#apply(step),
      refuse: this.#model.refuse,
      changed: this.#model.changed,
      openChanged: (open) => {
        if (!open && this.#construction === construction) this.#construction = null
        this.#model.constructionChanged?.(open)
        this.#model.changed()
      },
      reducedMotion: () => this.#model.motionPreferences().hoverEaseMs === 0,
    }, bubble, invocation)
    this.#construction = construction
    this.#moves.cancel()
    this.#model.changed()
    return true
  }

  closeConstruction(): boolean {
    const construction = this.#construction
    if (construction === null) return false
    construction.dispose()
    return true
  }

  setReducedMotion(enabled: boolean): void {
    if (this.#disposed) return
    this.#construction?.setReducedMotion(enabled)
  }

  reconcileDiagram(): void {
    if (this.#disposed) return
    const next = mkEngine(this.#model.diagram(), this.#model.boundary())
    carryOver(this.#engine, next)
    seedProject(next)
    this.motion.observeSwap(this.#engine, next, this.#window.performance.now())
    this.#engine = next
    this.#rebuilds++
    this.interaction.reconcileDiagram(true)
    this.#model.changed()
  }

  cancelActiveGesture(): void {
    if (this.#disposed) return
    this.interaction.cancelActiveGesture()
    this.#moves.cancel()
  }

  resize(width: number, height: number): void {
    if (this.#disposed) return
    const nextWidth = Math.max(1, Math.round(width))
    const nextHeight = Math.max(1, Math.round(height))
    if (this.canvas.width === nextWidth && this.canvas.height === nextHeight) return
    this.canvas.width = nextWidth
    this.canvas.height = nextHeight
    this.interaction.fit()
  }

  frame(now = this.#window.performance.now()): void {
    if (this.#disposed) return
    this.motion.frame(now)
    if (!this.motion.playing) this.interaction.advance(this.#construction === null)
    const theme = this.#model.theme()
    const shapes: Shape[] = paint(this.#engine, theme).filter((shape) => shape.kind !== 'frame')
    for (const id of this.interaction.pins) {
      const body = this.#engine.bodies.get(id)
      if (body === undefined) continue
      shapes.push({ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale + 1.2, fill: null, stroke: theme.interaction.pin, width: 1.5, insetColor: null, glow: null })
      const marker = this.#markerAt(id)
      if (marker !== null) shapes.push({ kind: 'dot', center: marker, rPx: 5.5, fill: theme.interaction.pin })
    }
    const preview = this.interaction.pinPreviewId
    const previewAt = preview === null ? null : this.#markerAt(preview)
    if (previewAt !== null) shapes.push({ kind: 'dot', center: previewAt, rPx: 8, fill: theme.interaction.pin })
    for (const hit of this.interaction.selection) shapes.push(...this.#itemShapes(hit, theme.interaction.selection))
    const hover = this.interaction.hover
    this.motion.setHover(hover === null ? null : `${hover.kind}:${hover.id}`, now)
    const hoverShapes: Shape[] = []
    if (hover !== null) {
      const binder = hoverBinder(this.#model.diagram(), hover)
      if (binder !== null) hoverShapes.push(...highlightGroup(this.#engine, theme, binder))
      else hoverShapes.push(...this.#itemShapes(
        hover,
        isHitSelected(this.interaction.selection, hover)
          ? theme.interaction.selectedHover
          : theme.interaction.hover,
      ))
    }
    shapes.push(...this.#moves.overlay())
    if (this.#construction !== null) shapes.push(...this.#construction.hostOverlays())
    this.#context.clearRect(0, 0, this.canvas.width, this.canvas.height)
    drawShapes(this.#context, shapes, this.view)
    this.#context.save()
    this.#context.globalAlpha = this.motion.hoverFraction(now)
    drawShapes(this.#context, hoverShapes, this.view)
    this.#context.restore()
    drawShapes(this.#context, this.motion.overlays(now), this.view)
    this.#construction?.frame(now)
  }

  debug(): GameProofViewportDebug {
    return {
      rebuilds: this.#rebuilds,
      construction: this.#construction?.debugState() ?? null,
      view: { ...this.view },
      selection: [...this.interaction.selection],
      pins: [...this.interaction.pins],
      motion: this.motion.debug(this.#window.performance.now()),
    }
  }

  dispose(): void {
    if (this.#disposed) return
    this.#disposed = true
    this.#moves.dispose()
    this.#construction?.dispose()
    this.#construction = null
    this.motion.dispose()
    this.interaction.dispose()
    this.canvas.remove()
  }

  #inputAllowed(): boolean {
    return proofSurfaceInputAllowed(this.#construction !== null, this.motion.playing, this.#model.inputAllowed())
  }

  #apply(step: ProofStep): void {
    this.#applyAction(singleStepAction(step.rule, step))
  }

  #applyAction(action: ProofAction): void {
    const commit = this.#model.prepare(action)
    const first = action.steps[0]
    if (first === undefined) throw new Error('proof action must contain at least one step')
    this.motion.run(first, () => {
      commit()
      this.reconcileDiagram()
    }, this.#window.performance.now())
  }

  #applyArtifactAction(action: ArtifactAction): void {
    const commit = this.#model.prepare(action)
    commit()
    this.reconcileDiagram()
  }

  #markerAt(id: string): Vec2 | null {
    const body = this.#engine.bodies.get(id)
    if (body === undefined) return null
    const radius = body.discR * this.#engine.scale
    return { x: body.pos.x + radius * 0.72, y: body.pos.y - radius * 0.72 }
  }

  #itemShapes(hit: Hit, stroke: string): Shape[] {
    if (hit.kind === 'node') {
      const body = this.#engine.bodies.get(hit.id)
      return body === undefined ? [] : [{ kind: 'circle', center: body.pos, r: body.discR * this.#engine.scale, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    if (hit.kind === 'region') {
      const region = this.#engine.regions.get(hit.id)
      return region === undefined ? [] : [{ kind: 'circle', center: region.center, r: region.radius, fill: null, stroke, width: 2, insetColor: null, glow: null }]
    }
    const shapes: Shape[] = []
    for (const leg of legPaths(this.#engine)) if (leg.wid === hit.id) shapes.push({ kind: 'polyline', pts: leg.pts, stroke, width: 3, glow: null })
    for (const stub of existentialStubs(this.#engine)) if (stub.wid === hit.id) shapes.push({ kind: 'segment', from: stub.from, to: stub.to, stroke, width: 3, glow: null })
    return shapes
  }
}
