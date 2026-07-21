import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { ProofStep } from '../../src/kernel/proof/step'
import { applyAction } from '../../src/kernel/proof/action'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory } from '../../src/kernel/proof/store'
import { EMPTY_PROOF_CONTEXT, type ProofContext } from '../../src/kernel/proof/context'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import { computeLegs, recomputeRegions } from '../../src/view/index'
import { LIGHT } from '../../src/view/paint'
import {
  contextualDeleteStep,
  discoverProofActions,
  foldedComprehension,
  instantiationChoices,
  proofConnectionStep,
  ProofMoveController,
} from '../../src/app/interact/moves'
import type { ConnectionEnd } from '../../src/app/interact/connection'
import type { Hit } from '../../src/app/hittest'
import type { KeySample, PointerSample } from '../../src/app/interact/viewport'

const p = (source: string) => parseTerm(source)
const ctx = () => verifyTheory(buildFregeTheory())

const pointer = (hit: Hit): PointerSample => ({
  pointerId: 1,
  button: 0,
  client: { x: 12, y: 18 },
  screen: { x: 12, y: 18 },
  world: { x: 0, y: 0 },
  hit,
  shiftKey: false,
  ctrlKey: false,
  altKey: false,
  metaKey: false,
})

const contextPointer = (hit: Hit | null, world = { x: 0, y: 0 }): PointerSample => ({
  ...pointer(hit ?? { kind: 'region', id: 'unused' }),
  button: 2,
  world,
  hit,
})

const key = (value: string): KeySample => ({
  key: value,
  shiftKey: value === value.toUpperCase() && value !== value.toLowerCase(),
  ctrlKey: false,
  altKey: false,
  metaKey: false,
  repeat: false,
})

function fusionController(
  initialSelection: 'none' | 'wire' | 'node' | 'mixed' = 'none',
  initialContext: ProofContext = ctx(),
) {
  const b = new DiagramBuilder()
  const producer = b.termNode(b.root, p('\\x. x'))
  const consumer = b.termNode(b.root, p('q y'))
  const wire = b.wire(b.root, [
    { node: producer, port: { kind: 'output' } },
    { node: consumer, port: { kind: 'freeVar', name: 'q' } },
  ])
  let diagram = b.build()
  let selection: Hit[] = initialSelection === 'wire'
    ? [{ kind: 'wire', id: wire }]
    : initialSelection === 'node'
      ? [{ kind: 'node', id: producer }]
      : initialSelection === 'mixed'
        ? [{ kind: 'wire', id: wire }, { kind: 'node', id: producer }]
        : []
  const applied: ProofStep[] = []
  const abstractions: Array<{ sel: import('../../src/kernel/diagram/subgraph/selection').SubgraphSelection; pointer: { x: number; y: number } }> = []
  let proof = initialContext
  const controller = new ProofMoveController({
    host: { ownerDocument: {} } as HTMLElement,
    active: () => true,
    diagram: () => diagram,
    engine: () => mkEngine(diagram, []),
    viewScale: () => 1,
    selection: () => selection,
    setSelection: (next) => { selection = [...next] },
    context: () => proof,
    orientation: () => 'forward',
    apply: (action) => {
      applied.push(...action.steps)
      diagram = applyAction(diagram, action, proof)
    },
    commitFission: () => {},
    refuse: (text) => { throw new Error(text) },
    theme: () => LIGHT,
    fuel: () => 64,
    openComprehension: () => {},
    openAbstraction: (sel, at) => { abstractions.push({ sel, pointer: at }) },
    openSpawn: () => {},
  })
  return {
    controller, producer, consumer, wire, applied, abstractions, diagram: () => diagram,
    setContext: (next: ProofContext) => { proof = next },
  }
}

function inconsistentCut(
  firstSource = '\\x. x',
  secondSource = '\\x. \\y. x',
  enclosingCut = false,
) {
  const b = new DiagramBuilder()
  const parent = enclosingCut ? b.cut(b.root) : b.root
  const cut = b.cut(parent)
  const first = b.termNode(cut, p(firstSource))
  const second = b.termNode(cut, p(secondSource))
  const wire = b.wire(cut, [first, second]
    .map((node) => ({ node, port: { kind: 'output' as const } })))
  return { diagram: b.build(), parent, cut, first, second, wire }
}

class MenuElement {
  textContent = ''
  className = ''
  style = { cssText: '' }
  readonly children: MenuElement[] = []
  readonly #listeners: Array<() => void> = []

  get childElementCount(): number { return this.children.length }
  setAttribute(): void {}
  addEventListener(type: string, listener: () => void): void {
    if (type === 'click') this.#listeners.push(listener)
  }
  append(...children: MenuElement[]): void { this.children.push(...children) }
  remove(): void {}
  click(): void { for (const listener of this.#listeners) listener() }
}

function menuHost(): { readonly host: HTMLElement; readonly appended: MenuElement[] } {
  const appended: MenuElement[] = []
  const document = { createElement: () => new MenuElement() }
  const host = {
    ownerDocument: document,
    append: (element: MenuElement) => { appended.push(element) },
  }
  return { host: host as unknown as HTMLElement, appended }
}

function inconsistentController(
  orientation: 'forward' | 'backward',
  fuel = 64,
  host: HTMLElement = { ownerDocument: {} } as HTMLElement,
  firstSource?: string,
  secondSource?: string,
) {
  const fixture = inconsistentCut(firstSource, secondSource)
  const steps: ProofStep[] = []
  const refusals: string[] = []
  let selection: Hit[] = [{ kind: 'region', id: fixture.cut }]
  const controller = new ProofMoveController({
    host,
    active: () => true,
    diagram: () => fixture.diagram,
    engine: () => mkEngine(fixture.diagram, []),
    viewScale: () => 1,
    selection: () => selection,
    setSelection: (next) => { selection = [...next] },
    context: () => EMPTY_PROOF_CONTEXT,
    orientation: () => orientation,
    apply: (action) => { steps.push(...action.steps) },
    commitFission: () => {},
    refuse: (text) => { refusals.push(text) },
    theme: () => LIGHT,
    fuel: () => fuel,
    openComprehension: () => {},
    openAbstraction: () => {},
    openSpawn: () => {},
  })
  return { ...fixture, controller, steps, refusals }
}

describe('ProofMoveController context authority', () => {
  it('authenticates construction and every later context callback before branching', () => {
    const forged = { theorems: new Map(), relations: new Map() } as unknown as ProofContext
    expect(() => fusionController('none', forged)).toThrowError('invalid proof context')
    const fixture = fusionController()
    fixture.setContext(forged)
    expect(() => fixture.controller.claim({ ...pointer({ kind: 'region', id: 'missing' }), button: 1 }))
      .toThrowError('invalid proof context')
  })
})

describe('shared proof move discovery', () => {
  it('absorb-normalizes a selected inconsistent cut plus all its contents to the same action and step', () => {
    const { diagram, cut, first, second, wire } = inconsistentCut()
    const cutOnly = discoverProofActions(diagram, [{ kind: 'region', id: cut }], ctx(), 'forward')!
    const withContents = discoverProofActions(diagram, [
      { kind: 'region', id: cut },
      { kind: 'node', id: first },
      { kind: 'node', id: second },
      { kind: 'wire', id: wire },
    ], ctx(), 'forward')!

    expect(withContents.sel).toEqual(cutOnly.sel)
    expect(withContents.actions.map((action) => action.kind)).toContain('inconsistentCutElim')
    expect(contextualDeleteStep(diagram, withContents, 64))
      .toEqual(contextualDeleteStep(diagram, cutOnly, 64))
  })

  it('resolves contextual deletion in double-cut, vacuous, inconsistent, erasure, deiteration order', () => {
    const inconsistent = inconsistentCut()
    const found = discoverProofActions(
      inconsistent.diagram, [{ kind: 'region', id: inconsistent.cut }], ctx(), 'forward',
    )!
    const staged = (kinds: Array<'doubleCutElim' | 'vacuousElim' | 'inconsistentCutElim' | 'erase' | 'deiterate'>) => ({
      ...found,
      actions: kinds.map((kind) => ({ kind, label: kind })),
    })

    expect(contextualDeleteStep(inconsistent.diagram, staged([
      'deiterate', 'erase', 'inconsistentCutElim', 'vacuousElim', 'doubleCutElim',
    ]), 64)).toEqual({ rule: 'doubleCutElim', region: inconsistent.cut })
    expect(contextualDeleteStep(inconsistent.diagram, staged([
      'deiterate', 'erase', 'inconsistentCutElim', 'vacuousElim',
    ]), 64)).toEqual({ rule: 'vacuousElim', region: inconsistent.cut })
    expect(contextualDeleteStep(inconsistent.diagram, staged([
      'deiterate', 'erase', 'inconsistentCutElim',
    ]), 64)).toMatchObject({ rule: 'inconsistentCutElim', region: inconsistent.cut })

    const duplicate = new DiagramBuilder()
    const original = duplicate.termNode(duplicate.root, p('y'))
    const copy = duplicate.termNode(duplicate.root, p('y'))
    duplicate.wire(duplicate.root, [original, copy]
      .map((node) => ({ node, port: { kind: 'freeVar' as const, name: 'y' } })))
    duplicate.wire(duplicate.root, [original, copy]
      .map((node) => ({ node, port: { kind: 'output' as const } })))
    const duplicateDiagram = duplicate.build()
    const forward = discoverProofActions(duplicateDiagram, [{ kind: 'node', id: copy }], ctx(), 'forward')!
    const backward = discoverProofActions(duplicateDiagram, [{ kind: 'node', id: copy }], ctx(), 'backward')!
    expect(contextualDeleteStep(duplicateDiagram, forward, 64)?.rule).toBe('erasure')
    expect(contextualDeleteStep(duplicateDiagram, backward, 64)?.rule).toBe('deiteration')
  })

  it('uses inconsistent-cut elimination before available positive-region erasure', () => {
    const fixture = inconsistentCut()
    const found = discoverProofActions(
      fixture.diagram, [{ kind: 'region', id: fixture.cut }], ctx(), 'forward',
    )!

    expect(found.actions.map((action) => action.kind)).toEqual(expect.arrayContaining([
      'inconsistentCutElim', 'erase',
    ]))
    expect(contextualDeleteStep(fixture.diagram, found, 64)).toMatchObject({
      rule: 'inconsistentCutElim', region: fixture.cut,
    })
  })

  it('falls through to erasure when every plausible pair has the same normal form', () => {
    const fixture = inconsistentCut('\\x. x', '\\renamed. renamed')
    const found = discoverProofActions(
      fixture.diagram, [{ kind: 'region', id: fixture.cut }], ctx(), 'forward',
    )!

    expect(found.actions.map((action) => action.kind)).toContain('inconsistentCutElim')
    expect(contextualDeleteStep(fixture.diagram, found, 1)?.rule).toBe('erasure')
  })

  it('refuses final exhaustion without returning a proof step', () => {
    const fixture = inconsistentCut('(\\x. x x) (\\x. x x)', '\\x. x')
    const found = discoverProofActions(
      fixture.diagram, [{ kind: 'region', id: fixture.cut }], ctx(), 'forward',
    )!
    let step: ProofStep | null = null

    expect(() => { step = contextualDeleteStep(fixture.diagram, found, 1) })
      .toThrow(/inconsistency is undecided under the current fuel/)
    expect(step).toBeNull()
  })

  it('uses a later certifying pair after an earlier pair exhausts fuel', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const exhausted = b.termNode(cut, p('(\\x. x x) (\\x. x x)'))
    const first = b.termNode(cut, p('\\x. x'))
    const second = b.termNode(cut, p('\\x. \\y. x'))
    b.wire(cut, [exhausted, first, second]
      .map((node) => ({ node, port: { kind: 'output' as const } })))
    const diagram = b.build()
    const found = discoverProofActions(diagram, [{ kind: 'region', id: cut }], ctx(), 'forward')!

    expect(contextualDeleteStep(diagram, found, 1)).toMatchObject({
      rule: 'inconsistentCutElim', region: cut, first, second,
    })
  })

  it('absorb-normalizes a selected double-cut subtree and chooses its elimination first', () => {
    const b = new DiagramBuilder()
    const outer = b.cut(b.root)
    const inner = b.cut(outer)
    const node = b.termNode(inner, p('x'))
    const d = b.build()
    const found = discoverProofActions(d, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
      { kind: 'node', id: node },
    ], ctx(), 'forward')!

    expect(found.sel.regions).toEqual([outer])
    expect(found.sel.nodes).toEqual([])
    expect(contextualDeleteStep(d, found, 64)).toEqual({ rule: 'doubleCutElim', region: outer })
  })

  it('adds same-region orphan riders to erasure but stores no unrelated wire', () => {
    const b = new DiagramBuilder()
    const doomed = b.termNode(b.root, p('x'))
    const survivor = b.termNode(b.root, p('y'))
    const d = b.build()
    const found = discoverProofActions(d, [{ kind: 'node', id: doomed }], ctx(), 'forward')!
    const step = contextualDeleteStep(d, found, 64)
    expect(step?.rule).toBe('erasure')
    if (step?.rule !== 'erasure') throw new Error('expected erasure')
    const doomedWires = Object.entries(d.wires)
      .filter(([, wire]) => wire.endpoints.every((endpoint) => endpoint.node === doomed))
      .map(([id]) => id)
      .sort()
    const survivorWires = Object.entries(d.wires)
      .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === survivor))
      .map(([id]) => id)
    expect([...step.sel.wires].sort()).toEqual(doomedWires)
    expect(step.sel.wires.some((wire) => survivorWires.includes(wire))).toBe(false)
  })

  it('uses one vocabulary in both orientations while flipping only polarity gates', () => {
    const b = new DiagramBuilder()
    const node = b.termNode(b.root, p('(\\x. x) y'))
    const d = b.build()
    const forward = discoverProofActions(d, [{ kind: 'node', id: node }], ctx(), 'forward')!.actions.map((action) => action.kind)
    const backward = discoverProofActions(d, [{ kind: 'node', id: node }], ctx(), 'backward')!.actions.map((action) => action.kind)
    for (const shared of ['doubleCutWrap', 'abstractWrap', 'iterate', 'deiterate', 'convert', 'relFold']) {
      expect(forward).toContain(shared)
      expect(backward).toContain(shared)
    }
    expect(forward).toContain('erase')
    expect(backward).not.toContain('erase')
  })
})

describe('inconsistent-cut interaction dispatch', () => {
  it.each(['Backspace', 'Delete'])('%s authors the same certified action', (pressed) => {
    const fixture = inconsistentController('forward')

    expect(fixture.controller.keyDown(key(pressed))).toBe(true)
    expect(fixture.steps).toEqual([{
      rule: 'inconsistentCutElim',
      region: fixture.cut,
      first: fixture.first,
      second: fixture.second,
      certificate: { firstSteps: [], secondSteps: [] },
    }])
  })

  it('authors the same result through forward and backward controllers', () => {
    const forward = inconsistentController('forward')
    const backward = inconsistentController('backward')

    expect(forward.controller.keyDown(key('Delete'))).toBe(true)
    expect(backward.controller.keyDown(key('Delete'))).toBe(true)
    expect(backward.steps).toEqual(forward.steps)
  })

  it.each([
    ['Backspace', 'forward'],
    ['Backspace', 'backward'],
    ['Delete', 'forward'],
    ['Delete', 'backward'],
  ] as const)('%s in %s consumes undecided authoring and reports the refusal', (pressed, orientation) => {
    const fixture = inconsistentController(
      orientation,
      1,
      undefined,
      '(\\x. x x) (\\x. x x)',
      '\\x. x',
    )
    let consumed: boolean | undefined

    expect(() => { consumed = fixture.controller.keyDown(key(pressed)) }).not.toThrow()
    expect(consumed).toBe(true)
    expect(fixture.steps).toEqual([])
    expect(fixture.refusals).toEqual(['inconsistency is undecided under the current fuel'])
  })

  it('authors and commits the same proof step from the contextual menu', () => {
    const menu = menuHost()
    const fixture = inconsistentController('forward', 64, menu.host)
    const expected = contextualDeleteStep(
      fixture.diagram,
      discoverProofActions(fixture.diagram, [{ kind: 'region', id: fixture.cut }], ctx(), 'forward')!,
      64,
    )

    expect(fixture.controller.contextMenu(contextPointer({ kind: 'region', id: fixture.cut }))).toBe(true)
    const action = menu.appended[0]?.children.find((element) =>
      element.textContent === 'Eliminate the inconsistent cut')
    expect(action).toBeDefined()
    action!.click()
    expect(fixture.steps).toEqual([expected])
    expect(fixture.refusals).toEqual([])
  })
})

describe('proof context routing', () => {
  it('opens shared spawning for unselected blank space in the smallest containing region', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const diagram = b.build()
    const engine = mkEngine(diagram, [])
    recomputeRegions(engine)
    engine.regions.get(cut)!.center = { x: 0, y: 0 }
    engine.regions.get(cut)!.radius = 40
    const opened: Array<{ sample: PointerSample; region: string }> = []
    const controller = new ProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      selection: () => [],
      setSelection: () => {},
      context: () => (EMPTY_PROOF_CONTEXT),
      orientation: () => 'forward',
      apply: () => {},
      commitFission: () => {},
      refuse: () => {},
      theme: () => LIGHT,
      fuel: () => 64,
      openComprehension: () => {},
      openAbstraction: () => {},
      openSpawn: (sample, region) => { opened.push({ sample, region }) },
    })
    const sample = contextPointer(null)

    expect(controller.contextMenu(sample)).toBe(true)
    expect(opened).toEqual([{ sample, region: cut }])
  })

  it('does not replace object or selected-region proof menus with spawning', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const node = b.termNode(cut, p('x'))
    const diagram = b.build()
    const engine = mkEngine(diagram, [])
    const opened: string[] = []
    let selection: Hit[] = []
    const controller = new ProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      selection: () => selection,
      setSelection: () => {},
      context: () => (EMPTY_PROOF_CONTEXT),
      orientation: () => 'forward',
      apply: () => {},
      commitFission: () => {},
      refuse: () => {},
      theme: () => LIGHT,
      fuel: () => 64,
      openComprehension: () => {},
      openAbstraction: () => {},
      openSpawn: (_sample, region) => { opened.push(region) },
    })

    expect(controller.contextMenu(contextPointer({ kind: 'node', id: node }))).toBe(true)
    selection = [{ kind: 'region', id: cut }]
    expect(controller.contextMenu(contextPointer({ kind: 'region', id: cut }))).toBe(true)
    expect(opened).toEqual([])
  })
})

describe('proof move parameters', () => {
  it('offers one anonymous relation before matching named folded relations', () => {
    expect(instantiationChoices(ctx(), 2)).toEqual([
      { kind: 'anonymous', label: 'New relation…' },
      { kind: 'named', label: 'succ', name: 'succ' },
    ])
  })

  it('builds a named comprehension as one folded reference with ordered boundary wires', () => {
    const proof = ctx()
    const comp = foldedComprehension(proof, 'succ')
    const refs = Object.values(comp.diagram.nodes)
    expect(refs).toEqual([{ kind: 'ref', region: comp.diagram.root, defId: 'succ', arity: 2 }])
    expect(comp.boundary).toHaveLength(2)
    expect(comp.boundary.map((wire) => comp.diagram.wires[wire]!.endpoints[0]!.port)).toEqual([
      { kind: 'arg', index: 0 },
      { kind: 'arg', index: 1 },
    ])
  })
})

const outputEnd = (wire: string, node: string): ConnectionEnd => ({
  wire,
  endpoint: { node, port: { kind: 'output' } },
})

describe('proof connection resolution', () => {
  it('refuses head-strip on a three-output equality wire until it is severed', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('\\x. x y z'))
    const ignored = b.termNode(b.root, p('\\x. x q r'))
    const c = b.termNode(b.root, p('\\x. x m n'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: ignored, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
    ])

    expect(() => proofConnectionStep(
      b.build(), outputEnd(wire, a), outputEnd(wire, c), 'forward', 64,
    )).toThrow(/binary equation wire.*extra endpoints.*sever/i)
  })

  it('does not guess a head-strip pair from a same-wire trunk', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('\\x. x y'))
    const c = b.termNode(b.root, p('\\x. x z'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
    ])

    expect(() => proofConnectionStep(b.build(), { wire, endpoint: null }, outputEnd(wire, c), 'forward', 64))
      .toThrow(/another term's output strand/)
  })

  it('uses wireJoin for a legal different-wire proof connection', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.termNode(cut, p('x'))
    const c = b.termNode(cut, p('y'))
    const d = b.build()
    const wa = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === a && ep.port.kind === 'output'))![0]
    const wc = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === c && ep.port.kind === 'output'))![0]

    expect(proofConnectionStep(d, outputEnd(wa, a), outputEnd(wc, c), 'forward', 64))
      .toEqual({ rule: 'wireJoin', a: wa, b: wc })
  })

  it('uses congruenceJoin when equal output producers justify a polarity-blind connection', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('\\x. x'))
    const c = b.termNode(b.root, p('(\\z. z) (\\x. x)'))
    const d = b.build()
    const wa = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === a && ep.port.kind === 'output'))![0]
    const wc = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === c && ep.port.kind === 'output'))![0]
    const step = proofConnectionStep(d, outputEnd(wa, a), outputEnd(wc, c), 'forward', 64)

    expect(step.rule).toBe('congruenceJoin')
    expect(step).toMatchObject({ a, b: c })
  })

  it('uses the dragged producer pair rather than another pair on multi-output wires', () => {
    const b = new DiagramBuilder()
    const a0 = b.termNode(b.root, p('\\x. x'))
    const a1 = b.termNode(b.root, p('\\x. x'))
    const c0 = b.termNode(b.root, p('\\x. x'))
    const c1 = b.termNode(b.root, p('\\x. x'))
    const wa = b.wire(b.root, [
      { node: a0, port: { kind: 'output' } },
      { node: a1, port: { kind: 'output' } },
    ])
    const wc = b.wire(b.root, [
      { node: c0, port: { kind: 'output' } },
      { node: c1, port: { kind: 'output' } },
    ])

    expect(proofConnectionStep(b.build(), outputEnd(wa, a1), outputEnd(wc, c0), 'forward', 64))
      .toMatchObject({ rule: 'congruenceJoin', a: a1, b: c0 })
  })

  it('refuses ambiguous certificate resolution from multi-output wire trunks', () => {
    const b = new DiagramBuilder()
    const a0 = b.termNode(b.root, p('\\x. x'))
    const a1 = b.termNode(b.root, p('\\x. x'))
    const c0 = b.termNode(b.root, p('\\x. x'))
    const c1 = b.termNode(b.root, p('\\x. x'))
    const wa = b.wire(b.root, [
      { node: a0, port: { kind: 'output' } },
      { node: a1, port: { kind: 'output' } },
    ])
    const wc = b.wire(b.root, [
      { node: c0, port: { kind: 'output' } },
      { node: c1, port: { kind: 'output' } },
    ])

    expect(() => proofConnectionStep(b.build(), { wire: wa, endpoint: null }, { wire: wc, endpoint: null }, 'forward', 64))
      .toThrow(/ambiguous.*output strand/i)
  })

  it('uses anchored contraction for equal closed witnesses in different regions', () => {
    const b = new DiagramBuilder()
    const bubble = b.bubble(b.root, 0)
    const redundant = b.termNode(b.root, p('\\x. x'))
    const survivor = b.termNode(bubble, p('\\x. x'))
    const d = b.build()
    const drop = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === redundant && ep.port.kind === 'output'))![0]
    const keep = Object.entries(d.wires).find(([, wire]) => wire.endpoints.some((ep) => ep.node === survivor && ep.port.kind === 'output'))![0]
    const step = proofConnectionStep(d, outputEnd(drop, redundant), outputEnd(keep, survivor), 'forward', 64)

    expect(step.rule).toBe('anchoredWireContract')
    expect(step).toMatchObject({ redundant, survivor })
  })

  it('swaps the conversion certificate when only reverse anchored contraction is legal', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const shielded = b.termNode(cut, p('(\\z. z) (\\x. x)'))
    const flat = b.termNode(b.root, p('\\x. x'))
    const shieldedWire = b.wire(b.root, [{ node: shielded, port: { kind: 'output' } }])
    const flatWire = b.wire(b.root, [{ node: flat, port: { kind: 'output' } }])
    const step = proofConnectionStep(
      b.build(), outputEnd(shieldedWire, shielded), outputEnd(flatWire, flat), 'forward', 64,
    )

    expect(step.rule).toBe('anchoredWireContract')
    expect(step).toMatchObject({ redundant: flat, survivor: shielded })
  })

  it('authors headStrip by dragging between two output legs on the same wire', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('\\x. x y'))
    const c = b.termNode(b.root, p('\\x. x z'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
    ])
    let diagram = b.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(a)!.pos = { x: -40, y: 0 }
    engine.bodies.get(c)!.pos = { x: 40, y: 0 }
    recomputeRegions(engine)
    const geometry = computeLegs(engine).find(({ leg }) => leg.wid === wire)!
    const pointFor = (node: string) => geometry.leg.from.body === node ? geometry.pts[0]! : geometry.pts.at(-1)!
    const applied: ProofStep[] = []
    const controller = new ProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      selection: () => [],
      setSelection: () => {},
      context: () => (EMPTY_PROOF_CONTEXT),
      orientation: () => 'forward',
      apply: (action) => {
        applied.push(...action.steps)
        diagram = applyAction(diagram, action, EMPTY_PROOF_CONTEXT)
      },
      commitFission: () => {},
      refuse: (text) => { throw new Error(text) },
      theme: () => LIGHT,
      fuel: () => 64,
      openComprehension: () => {},
      openAbstraction: () => {},
      openSpawn: () => {},
    })
    const from = { ...pointer({ kind: 'wire', id: wire }), world: pointFor(a), client: pointFor(a), screen: pointFor(a) }
    const to = { ...pointer({ kind: 'wire', id: wire }), world: pointFor(c), client: pointFor(c), screen: pointFor(c) }
    const claim = controller.claim(from)

    expect(claim).not.toBeNull()
    claim!.move(to)
    claim!.release(to, true)
    expect(applied).toEqual([{
      rule: 'headStrip', a, b: c,
      correspondence: { commonArity: 2, left: { s0: 0 }, right: { s0: 1 } },
    }])
  })

  it('refuses the same endpoint and preserves a kernel head mismatch refusal', () => {
    const b = new DiagramBuilder()
    const a = b.termNode(b.root, p('\\x. \\y. x'))
    const c = b.termNode(b.root, p('\\x. \\y. y'))
    const wire = b.wire(b.root, [
      { node: a, port: { kind: 'output' } },
      { node: c, port: { kind: 'output' } },
    ])
    const d = b.build()

    expect(() => proofConnectionStep(d, outputEnd(wire, a), outputEnd(wire, a), 'forward', 64))
      .toThrow(/another term's output strand/)
    expect(() => proofConnectionStep(d, outputEnd(wire, a), outputEnd(wire, c), 'forward', 64))
      .toThrow(/bound indices differ/)
  })
})

describe('fusion gesture dispatch', () => {
  it('opens provisional abstraction from Shift+W without submitting an immediate proof step', () => {
    const fixture = fusionController('node')

    expect(fixture.controller.keyDown(key('W'))).toBe(true)
    expect(fixture.applied).toEqual([])
    expect(fixture.abstractions).toEqual([{
      sel: expect.objectContaining({ nodes: [fixture.producer] }),
      pointer: { x: 0, y: 0 },
    }])
  })

  it('submits the existing fusion step when its wire is double-clicked', () => {
    const fixture = fusionController()

    expect(fixture.controller.doubleClick(pointer({ kind: 'wire', id: fixture.wire }))).toBe(true)
    expect(fixture.applied).toEqual([{ rule: 'fusion', wire: fixture.wire }])
    expect(fixture.diagram().nodes[fixture.producer]).toBeUndefined()
    expect(fixture.diagram().wires[fixture.wire]).toBeUndefined()
  })

  it('submits the same fusion step when F is pressed with exactly its wire selected', () => {
    const selected = fusionController('wire')

    expect(selected.controller.keyDown(key('f'))).toBe(true)
    expect(selected.applied).toEqual([{ rule: 'fusion', wire: selected.wire }])
    expect(selected.diagram().nodes[selected.producer]).toBeUndefined()
    expect(selected.diagram().wires[selected.wire]).toBeUndefined()
  })

  it('does not claim F for a node or a multi-item selection', () => {
    const nodeOnly = fusionController('node')
    expect(nodeOnly.controller.keyDown(key('f'))).toBe(false)
    expect(nodeOnly.applied).toEqual([])

    const mixed = fusionController('mixed')
    expect(mixed.controller.keyDown(key('f'))).toBe(false)
    expect(mixed.applied).toEqual([])
  })
})
