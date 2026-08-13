import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import {
  mkDiagram,
  type Diagram,
  type NodeId,
  type RegionId,
  type WireId,
} from '../../../src/kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig, type RelSig, type Sig } from '../../../src/kernel/diagram/sig'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { wireAt } from '../../../src/kernel/rules/access'
import { applyFold, applyUnfold, definitionSig } from '../../../src/kernel/rules/fold'

const R1 = relSig([IOTA])
const R2 = relSig([IOTA, IOTA])

function atomDefinition(args: readonly Sig[] = [IOTA], repeated = false): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const sig = relSig(args)
  const atom = builder.atom(builder.root, sig)
  builder.wire([{ node: atom, port: { kind: 'head' } }], sig)
  const boundary = args.map((arg, index) =>
    builder.wire([{ node: atom, port: { kind: 'arg', index } }], arg))
  return builder.buildOpen(repeated ? [boundary[0]!, boundary[0]!] : boundary)
}

function refDefinition(leaf: string): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, leaf, R1)
  const boundary = builder.wire(
    [{ node: ref, port: { kind: 'arg', index: 0 } }],
    IOTA,
  )
  return builder.buildOpen([boundary])
}

function definitions(...entries: readonly (readonly [string, DiagramWithBoundary])[]) {
  return new Map(entries)
}

type RefHost = {
  readonly diagram: Diagram
  readonly ref: NodeId
  readonly region: RegionId
  readonly args: readonly WireId[]
  readonly carriers: readonly NodeId[]
}

function refHost(defId: string, sig: RelSig, negative = false): RefHost {
  const builder = new DiagramBuilder()
  const region = negative ? builder.cut(builder.root) : builder.root
  const ref = builder.ref(region, defId, sig)
  const carriers: NodeId[] = []
  const args = sig.args.map((argSig, index) => {
    const carrier = builder.ref(region, `Carrier${index}`, relSig([argSig]))
    carriers.push(carrier)
    const argument = builder.wire([
      { node: ref, port: { kind: 'arg', index } },
      { node: carrier, port: { kind: 'arg', index: 0 } },
    ], argSig)
    // Folding removes the occurrence's end of this wire; the pin keeps it
    // above the two-end floor at its own scope while that happens.
    builder.pin(argument, region)
    return argument
  })
  return { diagram: builder.build(), ref, region, args, carriers }
}

function outerScopedRefHost(defId: string, sig: RelSig, negative: boolean): RefHost {
  const builder = new DiagramBuilder()
  const outerCut = builder.cut(builder.root)
  const region = negative ? outerCut : builder.cut(outerCut)
  const ref = builder.ref(region, defId, sig)
  const carriers: NodeId[] = []
  const args = sig.args.map((argSig, index) => {
    const carrier = builder.ref(builder.root, `OuterCarrier${index}`, relSig([argSig]))
    carriers.push(carrier)
    const argument = builder.wire([
      { node: ref, port: { kind: 'arg', index } },
      { node: carrier, port: { kind: 'arg', index: 0 } },
    ], argSig)
    builder.pin(argument, builder.root)
    return argument
  })
  return { diagram: builder.build(), ref, region, args, carriers }
}

function copiedNodes(before: Diagram, after: Diagram): NodeId[] {
  return Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined)
}

function reverseIdentityIncidences(diagram: Diagram, identity: NodeId): Diagram {
  const node = diagram.nodes[identity]
  if (node === undefined || node.kind !== 'identity') {
    throw new Error(`fixture node '${identity}' is not an identity`)
  }
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes: { ...diagram.nodes },
    wires: Object.fromEntries(
      Object.entries(diagram.wires).map(([wireId, wire]) => [
        wireId,
        {
          sig: wire.sig,
          endpoints: wire.endpoints.map((endpoint) =>
            endpoint.node === identity && endpoint.port.kind === 'identity'
              ? {
                  node: endpoint.node,
                  port: {
                    kind: 'identity' as const,
                    index: node.arity - endpoint.port.index - 1,
                  },
                }
              : endpoint),
        },
      ]),
    ),
  })
}

function selectionOf(diagram: Diagram, region: RegionId, nodes: readonly NodeId[]) {
  const selected = new Set(nodes)
  const wires = Object.entries(diagram.wires)
    .filter(([id, wire]) =>
      derivedScope(diagram, id) === region
      && wire.endpoints.length > 0
      && wire.endpoints.every((endpoint) => selected.has(endpoint.node)))
    .map(([id]) => id)
  return mkSelection(diagram, { region, regions: [], nodes, wires })
}

describe('definition-store unfolding', () => {
  it('freshens the stored graph, attaches ordered boundary positions, and removes only the ref', () => {
    const definition = atomDefinition([IOTA, relSig([])])
    const sig = definitionSig(definition)
    const host = refHost('R', sig)
    const unfolded = applyUnfold(host.diagram, host.ref, definitions(['R', definition]))
    const fresh = copiedNodes(host.diagram, unfolded)

    expect(unfolded.nodes[host.ref]).toBeUndefined()
    expect(host.carriers.every((id) => unfolded.nodes[id] === host.diagram.nodes[id])).toBe(true)
    const freshAtoms = fresh.filter((id) => unfolded.nodes[id]!.kind === 'atom')
    expect(freshAtoms).toHaveLength(1)
    expect(freshAtoms[0]).not.toBe(Object.keys(definition.diagram.nodes)[0])
    expect(wireAt(unfolded, freshAtoms[0]!, { kind: 'arg', index: 0 })).toBe(host.args[0])
    expect(wireAt(unfolded, freshAtoms[0]!, { kind: 'arg', index: 1 })).toBe(host.args[1])
    // The stored definition is untouched: its atom and the pin holding its
    // head wire above the two-end floor.
    expect(Object.keys(definition.diagram.nodes)).toEqual(['n0', 'n1'])
  })

  for (const negative of [false, true]) {
    it(`round-trips unfold then fold and fold then unfold in a ${negative ? 'negative' : 'positive'} region`, () => {
      const definition = atomDefinition()
      const store = definitions(['R', definition])
      const host = refHost('R', definitionSig(definition), negative)
      const unfolded = applyUnfold(host.diagram, host.ref, store)
      const occurrence = selectionOf(unfolded, host.region, copiedNodes(host.diagram, unfolded))
      const folded = applyFold(unfolded, occurrence, host.args, 'R', store)

      expect(exploreForm(folded)).toBe(exploreForm(host.diagram))
      const unfoldedAgain = applyUnfold(
        folded,
        Object.keys(folded.nodes).find((id) => folded.nodes[id]!.kind === 'ref'
          && folded.nodes[id]!.defId === 'R')!,
        store,
      )
      expect(exploreForm(unfoldedAgain)).toBe(exploreForm(unfolded))
    })
  }

  // NEEDS-ADJUDICATION: this asserts that no identity node survives a
  // repeated boundary incidence — eager-normalizer behavior. Splice now
  // creates one identity node at the application region and it persists
  // until an identification step absorbs it.
  it('uses identity normalization for repeated stored boundary incidences', () => {
    const definition = atomDefinition([IOTA], true)
    const store = definitions(['Repeated', definition])
    const host = refHost('Repeated', definitionSig(definition))
    const unfolded = applyUnfold(host.diagram, host.ref, store)
    const body = copiedNodes(host.diagram, unfolded).find((id) => unfolded.nodes[id]!.kind === 'atom')!
    const first = wireAt(unfolded, body, { kind: 'arg', index: 0 })

    expect(unfolded.wires[first]).toBeDefined()
    expect(Object.values(unfolded.wires).some((wire) =>
      wire.endpoints.some((endpoint) => endpoint.node === host.carriers[0])
      && wire.endpoints.some((endpoint) => endpoint.node === host.carriers[1]))).toBe(true)
    expect(Object.values(unfolded.nodes).some((node) => node.kind === 'identity')).toBe(false)

    const occurrence = selectionOf(unfolded, host.region, [body])
    const folded = applyFold(
      unfolded,
      occurrence,
      [first, first],
      'Repeated',
      store,
    )
    const foldedRef = Object.entries(folded.nodes).find(([, node]) =>
      node.kind === 'ref' && node.defId === 'Repeated')!
    expect(foldedRef[1].kind).toBe('ref')
    expect(wireAt(folded, foldedRef[0], { kind: 'arg', index: 0 }))
      .toBe(wireAt(folded, foldedRef[0], { kind: 'arg', index: 1 }))
  })

  for (const negative of [false, true]) {
    it(`round-trips a repeated boundary onto distinct outer-scoped arguments in a ${
      negative ? 'negative' : 'positive'
    } region`, () => {
      const definition = atomDefinition([IOTA], true)
      const store = definitions(['Repeated', definition])
      const host = outerScopedRefHost(
        'Repeated',
        definitionSig(definition),
        negative,
      )
      const unfolded = applyUnfold(host.diagram, host.ref, store)
      const copied = copiedNodes(host.diagram, unfolded)
      const identity = copied.find((id) => unfolded.nodes[id]!.kind === 'identity')
      const occurrence = selectionOf(unfolded, host.region, copied)

      expect(identity).toBeDefined()
      expect(host.args[0]).not.toBe(host.args[1])

      const folded = applyFold(
        unfolded,
        occurrence,
        host.args,
        'Repeated',
        store,
      )
      const permuted = reverseIdentityIncidences(unfolded, identity!)
      const permutedOccurrence = selectionOf(permuted, host.region, copied)
      const foldedPermuted = applyFold(
        permuted,
        permutedOccurrence,
        host.args,
        'Repeated',
        store,
      )

      expect(exploreForm(folded)).toBe(exploreForm(host.diagram))
      expect(exploreForm(foldedPermuted)).toBe(exploreForm(folded))
    })
  }

  it('refuses missing definitions, wrong arity, wrong nested signatures, and atoms', () => {
    const unary = atomDefinition()
    const missing = refHost('Missing', R1)
    expect(() => applyUnfold(missing.diagram, missing.ref, definitions()))
      .toThrowError(/no relation named 'Missing'/)

    const wrongArity = refHost('R', R2)
    expect(() => applyUnfold(wrongArity.diagram, wrongArity.ref, definitions(['R', unary])))
      .toThrowError(/signature '\(i,i\)' does not match definition 'R' signature '\(i\)'/)

    const nested = atomDefinition([relSig([IOTA])])
    const wrongNested = refHost('Nested', R1)
    expect(() => applyUnfold(wrongNested.diagram, wrongNested.ref, definitions(['Nested', nested])))
      .toThrowError(/signature '\(i\)' does not match definition 'Nested' signature '\(\(i\)\)'/)

    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, R1)
    const diagram = builder.build()
    expect(() => applyUnfold(diagram, atom, definitions(['R', unary])))
      .toThrowError(/applies to ref nodes/)
  })
})

describe('definition-store folding', () => {
  it('recognizes the exact boundary-pinned definition and creates exactly one ref', () => {
    const definition = atomDefinition()
    const store = definitions(['R', definition])
    const host = refHost('R', definitionSig(definition))
    const unfolded = applyUnfold(host.diagram, host.ref, store)
    const occurrence = selectionOf(unfolded, host.region, copiedNodes(host.diagram, unfolded))
    const folded = applyFold(unfolded, occurrence, host.args, 'R', store)
    const created = Object.entries(folded.nodes)
      .filter(([id]) => unfolded.nodes[id] === undefined)

    expect(created).toHaveLength(1)
    expect(created[0]![1]).toMatchObject({ kind: 'ref', defId: 'R', sig: R1 })
  })

  it('is defId-directed and refuses a near-match', () => {
    const left = refDefinition('LeafA')
    const right = refDefinition('LeafB')
    const store = definitions(['Left', left], ['Right', right])
    const host = refHost('Left', definitionSig(left))
    const unfolded = applyUnfold(host.diagram, host.ref, store)
    const occurrence = selectionOf(unfolded, host.region, copiedNodes(host.diagram, unfolded))

    expect(() => applyFold(unfolded, occurrence, host.args, 'Right', store))
      .toThrowError(/occurrence does not match the definition/)
  })

  it('refuses a missing definition, wrong argument count, and unused attachment', () => {
    const definition = atomDefinition([IOTA, IOTA])
    const store = definitions(['R', definition])
    const host = refHost('R', definitionSig(definition))
    const unfolded = applyUnfold(host.diagram, host.ref, store)
    const copied = copiedNodes(host.diagram, unfolded)
    const occurrence = selectionOf(unfolded, host.region, copied)

    expect(() => applyFold(unfolded, occurrence, host.args, 'Missing', store))
      .toThrowError(/no relation named 'Missing'/)
    expect(() => applyFold(unfolded, occurrence, [], 'R', store))
      .toThrowError(/signature '\(i,i\)' but 0 argument wires were given/)

    expect(() => applyFold(
      unfolded,
      occurrence,
      [host.args[0]!, host.args[0]!],
      'R',
      store,
    ))
      .toThrowError(/attachment wire .* is not used by any argument position/)
  })

  it('rejects the displaced wire/body target shape', () => {
    const definition = atomDefinition()
    const store = definitions(['R', definition])
    const host = refHost('R', definitionSig(definition))
    const unfolded = applyUnfold(host.diagram, host.ref, store)
    const occurrence = selectionOf(unfolded, host.region, copiedNodes(host.diagram, unfolded))

    expect(() => applyFold(
      unfolded,
      occurrence,
      host.args,
      { wireId: host.args[0] } as never,
      store,
    )).toThrowError(/no relation named/)
  })
})
