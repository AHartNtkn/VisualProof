import { describe, expect, it } from 'vitest'
import {
  SpawnCascade,
  SpawnRecents,
  atomHeadOptions,
  buildSpawnCatalog,
  searchSpawnCatalog,
  snapshotSpawnInvocation,
} from '../../src/app/interact/spawn'
import {
  ProofSpawnController,
  proofTermSpawnStep,
} from '../../src/app/interact/proof-spawn'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId } from '../../src/kernel/diagram/diagram'
import { IOTA } from '../../src/kernel/diagram/sig'
import { applyAction, singleStepAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import {
  applyTrack,
  currentTrack,
  redoTrack,
  startTrack,
  undoTrack,
} from '../../src/app/session'
import { BINARY, UNARY } from '../fixtures/zero-signature'
import { segment } from './helpers/build'

class SpawnElement extends EventTarget {
  readonly children: SpawnElement[] = []
  readonly style: Record<string, string> = {}
  readonly dataset: Record<string, string> = {}
  readonly attributes = new Map<string, string>()
  readonly classList = {
    add: (...names: string[]): void => {
      const classes = new Set(this.className.split(/\s+/u).filter(Boolean))
      for (const name of names) classes.add(name)
      this.className = [...classes].join(' ')
    },
  }
  parentElement: SpawnElement | null = null
  className = ''
  textContent = ''
  value = ''
  type = ''
  autocomplete = ''

  constructor(readonly ownerDocument: SpawnDocument, readonly tagName: string) {
    super()
  }

  get childElementCount(): number { return this.children.length }
  get firstElementChild(): SpawnElement | null { return this.children[0] ?? null }

  append(...children: SpawnElement[]): void {
    for (const child of children) {
      child.parentElement = this
      this.children.push(child)
    }
  }

  prepend(...children: SpawnElement[]): void {
    for (const child of children.slice().reverse()) {
      child.parentElement = this
      this.children.unshift(child)
    }
  }

  replaceChildren(...children: SpawnElement[]): void {
    for (const child of this.children) child.parentElement = null
    this.children.length = 0
    this.append(...children)
  }

  remove(): void {
    if (this.parentElement === null) return
    const index = this.parentElement.children.indexOf(this)
    if (index >= 0) this.parentElement.children.splice(index, 1)
    this.parentElement = null
  }

  contains(target: unknown): boolean {
    return target === this || this.children.some((child) => child.contains(target))
  }

  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
  focus(): void { this.ownerDocument.activeElement = this }
}

class SpawnDocument {
  activeElement: SpawnElement | null = null
  readonly defaultView = { innerWidth: 1200, innerHeight: 800 }
  createElement(tagName: string): SpawnElement {
    return new SpawnElement(this, tagName.toLowerCase())
  }
}

function descendants(root: SpawnElement): SpawnElement[] {
  return root.children.flatMap((child) => [child, ...descendants(child)])
}

function renderedText(element: SpawnElement): string {
  return [element.textContent, ...element.children.map(renderedText)].join('').trim()
}

function clickRow(host: SpawnElement, label: string): void {
  const row = descendants(host).find((element) =>
    element.tagName === 'button' && renderedText(element) === label)
  if (row === undefined) throw new Error(`no row '${label}'`)
  row.dispatchEvent(new Event('click'))
}

function submitText(host: SpawnElement, source: string): void {
  const input = descendants(host).find((element) => element.tagName === 'input')
  if (input === undefined) throw new Error('spawn input is absent')
  input.value = source
  const event = new Event('keydown', { cancelable: true })
  Object.defineProperty(event, 'key', { value: 'Enter' })
  input.dispatchEvent(event)
}

function onlyTermNode(diagram: Diagram): readonly [NodeId, Extract<Diagram['nodes'][string], { kind: 'term' }>] {
  const terms = Object.entries(diagram.nodes)
    .filter((entry): entry is [NodeId, Extract<Diagram['nodes'][string], { kind: 'term' }>] =>
      entry[1].kind === 'term')
  if (terms.length !== 1) throw new Error(`expected one term node, got ${terms.length}`)
  return terms[0]!
}

function incidentUnaryIdentityCount(diagram: Diagram, termNode: NodeId): number {
  const incidentWires = Object.entries(diagram.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === termNode))
  return incidentWires.filter(([, wire]) => wire.endpoints.some((endpoint) => {
    const node = diagram.nodes[endpoint.node]
    return node?.kind === 'identity'
      && node.arity === 1
      && node.sig.kind === IOTA.kind
  })).length
}

function proofSpawnHarness() {
  const builder = new DiagramBuilder()
  const region = builder.cut(builder.root)
  let diagram = builder.build()
  const document = new SpawnDocument()
  const host = document.createElement('div')
  const steps: ProofStep[] = []
  const actions: ProofAction[] = []
  const placements: Array<{ readonly node: NodeId; readonly at: { readonly x: number; readonly y: number } }> = []
  const refusals: string[] = []
  const controller = new ProofSpawnController({
    host: host as unknown as HTMLElement,
    diagram: () => diagram,
    context: () => EMPTY_PROOF_CONTEXT,
    commit: (action) => {
      actions.push(action)
      steps.push(...action.steps)
      diagram = applyAction(diagram, action, EMPTY_PROOF_CONTEXT)
      return diagram
    },
    place: (node, at) => { placements.push({ node, at }) },
    refuse: (text) => { refusals.push(text) },
    headWireColor: () => '#000',
  })
  return {
    controller,
    host,
    region,
    diagram: () => diagram,
    steps,
    actions,
    placements,
    refusals,
  }
}

describe('structural spawn catalog', () => {
  it('groups and searches opaque definition IDs', () => {
    const catalog = buildSpawnCatalog([
      ['logic/Unary', { boundary: [0] }],
      ['Pair', { boundary: [0, 1] }],
    ])
    expect(catalog.groups.map((group) => group.label)).toEqual(['Unqualified', 'logic'])
    expect(searchSpawnCatalog(catalog, 'unary').map((entry) => entry.defId))
      .toEqual(['logic/Unary'])
    const recents = new SpawnRecents(1)
    recents.note('Pair')
    expect(recents.list(catalog).map((entry) => entry.defId)).toEqual(['Pair'])
  })

  it('offers visible relational head wires from inner to outer scope', () => {
    const builder = new DiagramBuilder()
    const outer = segment(builder, builder.root, UNARY)
    const cut = builder.cut(builder.root)
    const inner = segment(builder, cut, BINARY)
    const diagram = builder.build()
    expect(atomHeadOptions(diagram, cut)).toEqual([
      { wire: inner.wire, arity: 2, position: 1, total: 2 },
      { wire: outer.wire, arity: 1, position: 2, total: 2 },
    ])
    expect(() => atomHeadOptions(diagram, 'missing')).toThrow(/unknown region/)
  })

  it('snapshots invocation coordinates', () => {
    const input = { screen: { x: 1, y: 2 }, world: { x: 3, y: 4 }, region: 'r0' }
    const output = snapshotSpawnInvocation(input)
    expect(output).toEqual(input)
    expect(output).not.toBe(input)
  })
})

describe('Lambda expression spawning', () => {
  it('offers Lambda expression, uses the captured placement, and caps every spawned incidence', () => {
    const fixture = proofSpawnHarness()
    fixture.controller.open({
      screen: { x: 17, y: 23 },
      world: { x: 101, y: 202 },
      region: fixture.region,
    })

    clickRow(fixture.host, 'Lambda expression')
    submitText(fixture.host, '\\x. x y')

    const [node, term] = onlyTermNode(fixture.diagram())
    expect(fixture.steps).toEqual([{
      rule: 'lambdaTermSpawn',
      region: fixture.region,
      term: term.term,
      freeArity: 1,
    }])
    expect(fixture.actions[0]!.placements).toEqual([{
      introducedNode: 0,
      x: 101,
      y: 202,
    }])
    expect(incidentUnaryIdentityCount(fixture.diagram(), node)).toBe(2)
    expect(fixture.placements).toEqual([{
      node,
      at: { x: 101, y: 202 },
    }])
  })

  it('caps the output of a closed term and every free slot of an open term', () => {
    const closed = proofSpawnHarness()
    closed.controller.open({
      screen: { x: 0, y: 0 }, world: { x: 1, y: 2 }, region: closed.region,
    })
    clickRow(closed.host, 'Lambda expression')
    submitText(closed.host, '\\x. x')
    const [closedNode] = onlyTermNode(closed.diagram())
    expect(incidentUnaryIdentityCount(closed.diagram(), closedNode)).toBe(1)

    const open = proofSpawnHarness()
    open.controller.open({
      screen: { x: 0, y: 0 }, world: { x: 3, y: 4 }, region: open.region,
    })
    clickRow(open.host, 'Lambda expression')
    submitText(open.host, 'f x y')
    const [openNode] = onlyTermNode(open.diagram())
    expect(incidentUnaryIdentityCount(open.diagram(), openNode)).toBe(4)
  })

  it('reports a whole-term parse refusal and leaves Lambda input open', () => {
    const fixture = proofSpawnHarness()
    fixture.controller.open({
      screen: { x: 9, y: 10 }, world: { x: 11, y: 12 }, region: fixture.region,
    })
    clickRow(fixture.host, 'Lambda expression')
    submitText(fixture.host, '\\x. x) trailing')

    expect(fixture.steps).toEqual([])
    expect(fixture.refusals.join('\n')).toMatch(/unexpected '\)' at position 5/)
    expect(descendants(fixture.host).some((element) => element.tagName === 'input')).toBe(true)
  })

  it('records one replayable spawn action that undo and redo restore exactly', () => {
    const builder = new DiagramBuilder()
    const region = builder.cut(builder.root)
    const origin = builder.build()
    const action = singleStepAction(
      'Lambda expression',
      proofTermSpawnStep(parseTerm('\\x. x y'), region),
      [{ introducedNode: 0, x: 12, y: 34 }],
    )
    const advanced = applyTrack(
      startTrack(mkDiagramWithBoundary(origin, []), 'forward', EMPTY_PROOF_CONTEXT),
      action,
    )

    expect(onlyTermNode(currentTrack(advanced))[1].freeArity).toBe(1)
    expect(currentTrack(undoTrack(advanced))).toEqual(origin)
    expect(currentTrack(redoTrack(undoTrack(advanced)))).toBe(currentTrack(advanced))
  })

  it('retains the cascade lifecycle contract with a parsed-term callback', () => {
    const document = new SpawnDocument()
    const host = document.createElement('div')
    const cascade = new SpawnCascade({
      host: host as unknown as HTMLElement,
      spawnTerm: () => undefined,
      spawnRef: () => undefined,
      spawnAtom: () => undefined,
      headWireColor: () => '#000',
      refuse: () => undefined,
    })
    expect(cascade.close()).toBe(false)
    cascade.dispose()
    expect(() => cascade.open(
      { screen: { x: 0, y: 0 }, world: { x: 0, y: 0 }, region: 'r0' },
      [],
      [],
    )).toThrow(/disposed/)
  })
})
