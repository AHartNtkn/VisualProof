import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import type { ProofContext, ProofStep } from '../kernel/proof/step'
import type { Engine } from '../view/engine'
import type { Theme } from '../view/paint'
import type { Vec2 } from '../view/vec'
import type { MutableView } from './interact/viewport'
import {
  planComprehensionConnection,
  type ComprehensionConnectionEndpoint,
  type ComprehensionDraft,
  type ExternalWireBinding,
} from './comprehension-draft'

export const EDITOR_PREFERRED_WIDTH = 660
export const EDITOR_PREFERRED_HEIGHT = 560
export const EDITOR_MIN_WIDTH = 420
export const EDITOR_MIN_HEIGHT = 340

const HORIZONTAL_MARGIN = 12
const TOP_MARGIN = 44
const BOTTOM_MARGIN = 34
const INVOCATION_GAP = 16

export type EditorRect = {
  readonly left: number
  readonly top: number
  readonly width: number
  readonly height: number
}

type ViewportSize = { readonly width: number; readonly height: number }

const clamp = (value: number, min: number, max: number): number =>
  Math.max(min, Math.min(Math.max(min, max), value))

export function placeComprehensionEditor(invocation: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - HORIZONTAL_MARGIN * 2)
  const availableHeight = Math.max(0, viewport.height - TOP_MARGIN - BOTTOM_MARGIN)
  const width = Math.min(EDITOR_PREFERRED_WIDTH, availableWidth)
  const height = Math.min(EDITOR_PREFERRED_HEIGHT, availableHeight)
  const right = invocation.x + INVOCATION_GAP
  const preferredLeft = right + width <= viewport.width - HORIZONTAL_MARGIN
    ? right
    : invocation.x - width - INVOCATION_GAP
  return {
    left: clamp(preferredLeft, HORIZONTAL_MARGIN, viewport.width - width - HORIZONTAL_MARGIN),
    top: clamp(invocation.y - 18, TOP_MARGIN, viewport.height - height - BOTTOM_MARGIN),
    width,
    height,
  }
}

export function moveComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  return {
    ...rect,
    left: clamp(rect.left + delta.x, 0, viewport.width - rect.width),
    top: clamp(rect.top + delta.y, 0, viewport.height - rect.height),
  }
}

export function resizeComprehensionEditor(rect: EditorRect, delta: Vec2, viewport: ViewportSize): EditorRect {
  const availableWidth = Math.max(0, viewport.width - rect.left)
  const availableHeight = Math.max(0, viewport.height - rect.top)
  const minWidth = Math.min(EDITOR_MIN_WIDTH, availableWidth)
  const minHeight = Math.min(EDITOR_MIN_HEIGHT, availableHeight)
  return {
    ...rect,
    width: clamp(rect.width + delta.x, minWidth, availableWidth),
    height: clamp(rect.height + delta.y, minHeight, availableHeight),
  }
}

export function connectionTargets(
  draft: ComprehensionDraft,
  source: ComprehensionConnectionEndpoint,
): { readonly draft: ReadonlySet<WireId>; readonly host: ReadonlySet<WireId> } {
  const draftTargets = new Set<WireId>()
  const hostTargets = new Set<WireId>()
  const current = draft.history[draft.cursor]!
  for (const wire of Object.keys(current.relation.diagram.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'draft', wire }).ok) draftTargets.add(wire)
  }
  for (const wire of Object.keys(draft.host.wires)) {
    if (planComprehensionConnection(draft, source, { kind: 'host', wire }).ok) hostTargets.add(wire)
  }
  return { draft: draftTargets, host: hostTargets }
}

export function formalBoundaryMarks(boundary: readonly WireId[]): readonly {
  readonly wire: WireId
  readonly position: number
  readonly orientation: boolean
}[] {
  return boundary.map((wire, position) => ({ wire, position, orientation: position === 0 }))
}

export type ComprehensionEditorHost = {
  readonly mount: HTMLElement
  readonly canvas: HTMLCanvasElement
  diagram(): Diagram
  boundary(): readonly WireId[]
  engine(): Engine
  view(): MutableView
  context(): ProofContext
  theme(): Theme
  fuel(): number
  apply(step: ProofStep): void
  refuse(text: string, pointer: Vec2): void
  changed(): void
  openChanged(open: boolean): void
}

export type ComprehensionEditorDebug = {
  readonly bubble: RegionId
  readonly cursor: number
  readonly historyLength: number
  readonly formalBoundary: readonly WireId[]
  readonly materializedBoundary: readonly WireId[]
  readonly externalWires: readonly ExternalWireBinding[]
  readonly rect: EditorRect
  readonly connection: null | {
    readonly source: ComprehensionConnectionEndpoint
    readonly draftTargets: readonly WireId[]
    readonly hostTargets: readonly WireId[]
  }
}
