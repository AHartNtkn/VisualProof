import type { Hit } from '../hittest'

export type BrushMode = 'select' | 'deselect'

export type BrushStroke = {
  readonly mode: BrushMode
  readonly fromVoid: boolean
  /** True once the stroke has encountered a semantic hit. */
  readonly painted: boolean
}
export type BrushState = {
  readonly selected: readonly Hit[]
  readonly stroke: BrushStroke | null
}

export type BrushEvent =
  | { readonly kind: 'begin'; readonly hit: Hit | null; readonly mode: BrushMode }
  | { readonly kind: 'move'; readonly hit: Hit | null }
  | { readonly kind: 'end' }

export type PointerPhase = 'selection' | 'physics' | 'claimed'

export type PointerModifiers = {
  readonly shiftKey: boolean
  readonly ctrlKey: boolean
}

function sameHit(a: Hit, b: Hit): boolean {
  return a.kind === b.kind && a.id === b.id
}

function uniqueHits(hits: readonly Hit[]): readonly Hit[] {
  const unique: Hit[] = []
  for (const hit of hits) {
    if (!unique.some((candidate) => sameHit(candidate, hit))) unique.push(hit)
  }
  return unique
}

export function isHitSelected(selected: readonly Hit[], hit: Hit | null): boolean {
  return hit !== null && selected.some((candidate) => sameHit(candidate, hit))
}

export function createBrushState(selected: readonly Hit[] = []): BrushState {
  return { selected: uniqueHits(selected), stroke: null }
}

function applyBrush(
  selected: readonly Hit[],
  hit: Hit | null,
  mode: BrushMode,
): readonly Hit[] {
  if (hit === null) return selected
  const present = isHitSelected(selected, hit)
  if (mode === 'deselect') {
    return present ? selected.filter((candidate) => !sameHit(candidate, hit)) : selected
  }
  return present ? selected : [...selected, hit]
}

/** Pure selection lifecycle. A press carries an explicit selection mode for
    the whole stroke; a void-start stroke clears only if it encounters no hit. */
export function reduceBrush(state: BrushState, event: BrushEvent): BrushState {
  if (event.kind === 'begin') {
    const selected = uniqueHits(state.selected)
    return {
      selected: applyBrush(selected, event.hit, event.mode),
      stroke: { mode: event.mode, fromVoid: event.hit === null, painted: event.hit !== null },
    }
  }

  if (event.kind === 'move') {
    if (state.stroke === null) return state
    const selected = applyBrush(state.selected, event.hit, state.stroke.mode)
    const painted = state.stroke.painted || event.hit !== null
    if (selected === state.selected && painted === state.stroke.painted) return state
    return { selected, stroke: { ...state.stroke, painted } }
  }

  if (state.stroke === null) return state
  return {
    selected: state.stroke.fromVoid && !state.stroke.painted ? [] : state.selected,
    stroke: null,
  }
}

/** Modifier precedence is global: Shift reserves the gesture for selection;
    otherwise Ctrl is physics-only, then a domain gesture may claim it. */
export function choosePointerPhase(modifiers: PointerModifiers, claim: boolean): PointerPhase {
  if (modifiers.shiftKey) return 'selection'
  if (modifiers.ctrlKey) return 'physics'
  return claim ? 'claimed' : 'selection'
}
