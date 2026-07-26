import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  applyWireJoin,
  applyWireSever,
  type ContentOccurrence,
} from '../../../src/kernel/rules/wire-quantifier'

function relationSeverFixture(options: {
  readonly secondDefinition?: string
  readonly separateParameters?: boolean
} = {}) {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const firstA = builder.ref(builder.root, 'A', relSig([IOTA]))
  const firstB = builder.ref(builder.root, 'B', relSig([IOTA, IOTA]))
  const secondA = builder.ref(negative, 'A', relSig([IOTA]))
  const secondB = builder.ref(
    negative,
    options.secondDefinition ?? 'B',
    relSig([IOTA, IOTA]),
  )
  const firstX = builder.wire(builder.root, [
    { node: firstA, port: { kind: 'arg', index: 0 } },
    { node: firstB, port: { kind: 'arg', index: 0 } },
  ])
  const secondX = builder.wire(builder.root, [
    { node: secondA, port: { kind: 'arg', index: 0 } },
    { node: secondB, port: { kind: 'arg', index: 0 } },
  ])
  const firstParameter = builder.wire(builder.root, [
    { node: firstB, port: { kind: 'arg', index: 1 } },
    ...(!options.separateParameters
      ? [{ node: secondB, port: { kind: 'arg' as const, index: 1 } }]
      : []),
  ])
  const secondParameter = options.separateParameters
    ? builder.wire(builder.root, [
        { node: secondB, port: { kind: 'arg', index: 1 } },
      ])
    : firstParameter
  const diagram = builder.build()
  const first = mkSelection(diagram, {
    region: diagram.root,
    regions: [],
    nodes: [firstA, firstB],
    wires: [],
  })
  const second = mkSelection(diagram, {
    region: negative,
    regions: [],
    nodes: [secondA, secondB],
    wires: [],
  })
  return {
    diagram,
    negative,
    first,
    second,
    firstNodes: [firstA, firstB] as const,
    secondNodes: [secondA, secondB] as const,
    firstX,
    secondX,
    firstParameter,
    secondParameter,
  }
}

describe('relation wire sever', () => {
  it('abstracts disjoint multi-node copies at different cut parities under one fresh relation wire', () => {
    const fixture = relationSeverFixture()

    const severed = applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        { sel: fixture.first, args: [fixture.firstX] },
        { sel: fixture.second, args: [fixture.secondX] },
      ],
    })

    for (const node of [...fixture.firstNodes, ...fixture.secondNodes]) {
      expect(severed.nodes[node]).toBeUndefined()
    }
    const introducedNodes = Object.entries(severed.nodes)
      .filter(([id]) => fixture.diagram.nodes[id] === undefined)
    expect(introducedNodes).toHaveLength(2)
    expect(introducedNodes.map(([, node]) => node.region).sort())
      .toEqual([fixture.diagram.root, fixture.negative].sort())
    expect(introducedNodes.every(([, node]) =>
      node.kind === 'atom'
      && node.sig.kind === 'rel'
      && node.sig.args.length === 1
      && node.sig.args[0]?.kind === 'iota')).toBe(true)

    const introducedWires = Object.entries(severed.wires)
      .filter(([id]) => fixture.diagram.wires[id] === undefined)
    expect(introducedWires).toHaveLength(1)
    const [quantifierId, quantifier] = introducedWires[0]!
    expect(quantifier.scope).toBe(fixture.diagram.root)
    expect(quantifier.sig).toEqual(relSig([IOTA]))
    expect(quantifier.endpoints.map((endpoint) => endpoint.port))
      .toEqual([{ kind: 'head' }, { kind: 'head' }])
    expect(introducedNodes.map(([id]) => id).sort())
      .toEqual(quantifier.endpoints.map((endpoint) => endpoint.node).sort())
    expect(severed.wires[fixture.firstX]!.endpoints).toContainEqual({
      node: introducedNodes.find(([, node]) =>
        node.region === fixture.diagram.root)![0],
      port: { kind: 'arg', index: 0 },
    })
    expect(severed.wires[fixture.secondX]!.endpoints).toContainEqual({
      node: introducedNodes.find(([, node]) =>
        node.region === fixture.negative)![0],
      port: { kind: 'arg', index: 0 },
    })
    expect(severed.wires[fixture.firstParameter]!.endpoints).toEqual([])
    expect(severed.wires[quantifierId]).toBe(quantifier)
  })

  it('accepts True as empty content at distinct occurrence sites and rejects a duplicate empty site', () => {
    const builder = new DiagramBuilder()
    const first = builder.cut(builder.root)
    const second = builder.cut(builder.root)
    const diagram = builder.build()
    const occurrence = (region: string): ContentOccurrence => ({
      sel: { region, regions: [], nodes: [], wires: [] },
      args: [],
    })

    const severed = applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [occurrence(first), occurrence(second)],
    })
    expect(Object.values(severed.nodes)).toHaveLength(2)
    expect(Object.values(severed.wires)).toHaveLength(1)

    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [occurrence(first), occurrence(first)],
    })).toThrowError(/duplicate.*empty|empty.*same occurrence site/i)
  })

  it('preserves repeated formal argument positions as repeated boundary pins', () => {
    const fixture = relationSeverFixture()
    const severed = applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        {
          sel: fixture.first,
          args: [fixture.firstX, fixture.firstX],
        },
        {
          sel: fixture.second,
          args: [fixture.secondX, fixture.secondX],
        },
      ],
    })
    const quantifier = Object.values(severed.wires)
      .find((candidate) =>
        candidate.sig.kind === 'rel'
        && candidate.sig.args.length === 2)!
    expect(quantifier.sig).toEqual(relSig([IOTA, IOTA]))
    for (const endpoint of quantifier.endpoints) {
      const application = endpoint.node
      expect(severed.wires[
        severed.nodes[application]!.region === fixture.diagram.root
          ? fixture.firstX
          : fixture.secondX
      ]!.endpoints).toEqual(expect.arrayContaining([
        { node: application, port: { kind: 'arg', index: 0 } },
        { node: application, port: { kind: 'arg', index: 1 } },
      ]))
    }
  })

  it('rejects an empty occurrence list', () => {
    const diagram = new DiagramBuilder().build()
    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [],
    })).toThrowError(/at least one occurrence/i)
  })

  it('rejects duplicate and overlapping selected content', () => {
    const fixture = relationSeverFixture()
    const duplicate = {
      sel: fixture.first,
      args: [fixture.firstX],
    } as const
    expect(() => applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [duplicate, duplicate],
    })).toThrowError(/overlap|duplicate/i)

    const partial = mkSelection(fixture.diagram, {
      region: fixture.diagram.root,
      regions: [],
      nodes: [fixture.firstNodes[0]],
      wires: [],
    })
    expect(() => applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        duplicate,
        { sel: partial, args: [fixture.firstX] },
      ],
    })).toThrowError(/overlap/i)
  })

  it('rejects occurrence regions outside the quantifier scope', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positive = builder.cut(negative)
    const diagram = builder.build()
    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: positive,
      occurrences: [{
        sel: {
          region: diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [],
      }],
    })).toThrowError(/occurrence region.*descend.*scope/i)
  })

  it('rejects non-isomorphic pinned content', () => {
    const fixture = relationSeverFixture({ secondDefinition: 'C' })
    expect(() => applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        { sel: fixture.first, args: [fixture.firstX] },
        { sel: fixture.second, args: [fixture.secondX] },
      ],
    })).toThrowError(/not isomorphic|same pinned content/i)
  })

  it('rejects asymmetric same-signature copies with swapped formal pins', () => {
    const builder = new DiagramBuilder()
    const firstA = builder.ref(builder.root, 'A', relSig([IOTA]))
    const firstB = builder.ref(builder.root, 'B', relSig([IOTA]))
    const secondA = builder.ref(builder.root, 'A', relSig([IOTA]))
    const secondB = builder.ref(builder.root, 'B', relSig([IOTA]))
    const firstAPin = builder.wire(builder.root, [{
      node: firstA,
      port: { kind: 'arg', index: 0 },
    }])
    const firstBPin = builder.wire(builder.root, [{
      node: firstB,
      port: { kind: 'arg', index: 0 },
    }])
    const secondAPin = builder.wire(builder.root, [{
      node: secondA,
      port: { kind: 'arg', index: 0 },
    }])
    const secondBPin = builder.wire(builder.root, [{
      node: secondB,
      port: { kind: 'arg', index: 0 },
    }])
    const diagram = builder.build()
    const selection = (nodes: readonly string[]) => mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes,
      wires: [],
    })

    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [
        {
          sel: selection([firstA, firstB]),
          args: [firstAPin, firstBPin],
        },
        {
          sel: selection([secondA, secondB]),
          args: [secondBPin, secondAPin],
        },
      ],
    })).toThrowError(/not isomorphic|same pinned content/i)
  })

  it('rejects mismatched ordered formal argument signatures', () => {
    const builder = new DiagramBuilder()
    const first = builder.ref(builder.root, 'G', relSig([IOTA]))
    const second = builder.ref(builder.root, 'G', relSig([relSig([])]))
    const firstArg = builder.wire(builder.root, [{
      node: first,
      port: { kind: 'arg', index: 0 },
    }])
    const secondArg = builder.wire(builder.root, [{
      node: second,
      port: { kind: 'arg', index: 0 },
    }], relSig([]))
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [
        {
          sel: mkSelection(diagram, {
            region: diagram.root,
            regions: [],
            nodes: [first],
            wires: [],
          }),
          args: [firstArg],
        },
        {
          sel: mkSelection(diagram, {
            region: diagram.root,
            regions: [],
            nodes: [second],
            wires: [],
          }),
          args: [secondArg],
        },
      ],
    })).toThrowError(/formal argument.*signature|ordered argument.*signature/i)
  })

  it('rejects copies attached to different ambient parameter wires', () => {
    const fixture = relationSeverFixture({ separateParameters: true })
    expect(fixture.firstParameter).not.toBe(fixture.secondParameter)
    expect(() => applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        { sel: fixture.first, args: [fixture.firstX] },
        { sel: fixture.second, args: [fixture.secondX] },
      ],
    })).toThrowError(/ambient attachment.*identical|same ambient/i)
  })

  it('rejects an ambient parameter whose scope does not enclose the quantifier scope', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positive = builder.cut(negative)
    const first = builder.ref(negative, 'G', relSig([IOTA, IOTA]))
    const second = builder.ref(positive, 'G', relSig([IOTA, IOTA]))
    const firstX = builder.wire(negative, [{
      node: first,
      port: { kind: 'arg', index: 0 },
    }])
    const secondX = builder.wire(negative, [{
      node: second,
      port: { kind: 'arg', index: 0 },
    }])
    const parameter = builder.wire(negative, [
      { node: first, port: { kind: 'arg', index: 1 } },
      { node: second, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    expect(() => applyWireSever(diagram, {
      kind: 'relation',
      scope: diagram.root,
      occurrences: [
        {
          sel: mkSelection(diagram, {
            region: negative,
            regions: [],
            nodes: [first],
            wires: [],
          }),
          args: [firstX],
        },
        {
          sel: mkSelection(diagram, {
            region: positive,
            regions: [],
            nodes: [second],
            wires: [],
          }),
          args: [secondX],
        },
      ],
    })).toThrowError(new RegExp(
      `ambient.*'${parameter}'.*scope.*enclose.*'${diagram.root}'`,
      'i',
    ))
  })

  it('rejects selecting one prospective application site recursively inside another occurrence', () => {
    const fixture = relationSeverFixture()
    const recursive = mkSelection(fixture.diagram, {
      region: fixture.diagram.root,
      regions: [fixture.negative],
      nodes: [],
      wires: [],
    })
    expect(() => applyWireSever(fixture.diagram, {
      kind: 'relation',
      scope: fixture.diagram.root,
      occurrences: [
        { sel: recursive, args: [fixture.secondX] },
        { sel: fixture.second, args: [fixture.secondX] },
      ],
    })).toThrowError(/recursive|occurrence site.*selected/i)
  })

  it('rejects relation content passed through the iota variant', () => {
    const builder = new DiagramBuilder()
    const relation = builder.relWire(builder.root, relSig([]))
    const diagram = builder.build()
    expect(() => applyWireSever(diagram, {
      kind: 'iota',
      wire: relation,
      keep: [],
    })).toThrowError(/iota.*requires.*iota|relation.*iota/i)
  })
})

function unaryContent() {
  const builder = new DiagramBuilder()
  const first = builder.ref(builder.root, 'A', relSig([IOTA]))
  const second = builder.ref(builder.root, 'B', relSig([IOTA, IOTA]))
  const formal = builder.wire(builder.root, [
    { node: first, port: { kind: 'arg', index: 0 } },
    { node: second, port: { kind: 'arg', index: 0 } },
  ])
  const parameter = builder.wire(builder.root, [{
    node: second,
    port: { kind: 'arg', index: 1 },
  }])
  return mkDiagramWithBoundary(
    builder.build(),
    [formal, parameter],
  )
}

function relationJoinFixture(scope: 'negative' | 'positive' = 'negative') {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const nested = builder.cut(negative)
  const relationScope = scope === 'negative' ? negative : builder.root
  const firstRegion = scope === 'negative' ? negative : builder.root
  const secondRegion = scope === 'negative' ? nested : builder.root
  const firstApplication = builder.atom(firstRegion, relSig([IOTA]))
  const secondApplication = builder.atom(secondRegion, relSig([IOTA]))
  const firstX = builder.wire(relationScope, [{
    node: firstApplication,
    port: { kind: 'arg', index: 0 },
  }])
  const secondX = builder.wire(relationScope, [{
    node: secondApplication,
    port: { kind: 'arg', index: 0 },
  }])
  const relation = builder.wire(relationScope, [
    { node: firstApplication, port: { kind: 'head' } },
    { node: secondApplication, port: { kind: 'head' } },
  ], relSig([IOTA]))
  const parameter = builder.wire(builder.root, [])
  return {
    diagram: builder.build(),
    negative,
    nested,
    relation,
    parameter,
    applications: [firstApplication, secondApplication] as const,
    arguments: [firstX, secondX] as const,
  }
}

describe('relation wire join', () => {
  it('grounds every headed application with a fresh splice of explicit multi-node content', () => {
    const fixture = relationJoinFixture()

    const joined = applyWireJoin(fixture.diagram, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [fixture.parameter],
    })

    expect(joined.wires[fixture.relation]).toBeUndefined()
    for (const application of fixture.applications) {
      expect(joined.nodes[application]).toBeUndefined()
    }
    const introduced = Object.entries(joined.nodes)
      .filter(([id]) => fixture.diagram.nodes[id] === undefined)
    expect(introduced).toHaveLength(4)
    expect(introduced.map(([, node]) =>
      node.kind === 'ref' ? node.defId : node.kind).sort())
      .toEqual(['A', 'A', 'B', 'B'])
    expect(introduced.map(([, node]) => node.region).sort())
      .toEqual([
        fixture.negative,
        fixture.negative,
        fixture.nested,
        fixture.nested,
      ].sort())
    expect(joined.wires[fixture.arguments[0]]!.endpoints).toHaveLength(2)
    expect(joined.wires[fixture.arguments[1]]!.endpoints).toHaveLength(2)
    expect(joined.wires[fixture.parameter]!.endpoints).toHaveLength(2)
  })

  it('preserves repeated formal boundary stubs through authoritative identity normalization', () => {
    const contentBuilder = new DiagramBuilder()
    const body = contentBuilder.ref(
      contentBuilder.root,
      'EqBody',
      relSig([IOTA, IOTA]),
    )
    const repeated = contentBuilder.wire(contentBuilder.root, [
      { node: body, port: { kind: 'arg', index: 0 } },
      { node: body, port: { kind: 'arg', index: 1 } },
    ])
    const content = mkDiagramWithBoundary(
      contentBuilder.build(),
      [repeated, repeated],
    )

    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([IOTA, IOTA]))
    const first = builder.wire(negative, [{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    const second = builder.wire(negative, [{
      node: application,
      port: { kind: 'arg', index: 1 },
    }])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA, IOTA]))
    const diagram = builder.build()

    const joined = applyWireJoin(diagram, {
      kind: 'relation',
      wire: relation,
      content,
      parameters: [],
    })

    const survivor = [first, second].sort()[0]!
    const absorbed = survivor === first ? second : first
    expect(joined.wires[absorbed]).toBeUndefined()
    expect(joined.wires[survivor]!.endpoints).toHaveLength(2)
    expect(Object.values(joined.nodes)).toEqual([expect.objectContaining({
      kind: 'ref',
      defId: 'EqBody',
    })])
    expect(Object.values(joined.nodes).some((node) =>
      node.kind === 'identity')).toBe(false)
  })

  it('grounds a proposition with empty-sheet content', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, relSig([]))
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([]))
    const diagram = builder.build()
    const empty = mkDiagramWithBoundary(new DiagramBuilder().build(), [])

    const joined = applyWireJoin(diagram, {
      kind: 'relation',
      wire: relation,
      content: empty,
      parameters: [],
    })

    expect(Object.keys(joined.nodes)).toEqual([])
    expect(Object.keys(joined.wires)).toEqual([])
  })

  it('uses the forward/backward polarity matrix for the quantified relation scope', () => {
    const fixture = relationJoinFixture('positive')
    const input = {
      kind: 'relation' as const,
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [fixture.parameter],
    }
    expect(() => applyWireJoin(fixture.diagram, input))
      .toThrowError(/relation wire join requires a negative scope/i)
    expect(() => applyWireJoin(fixture.diagram, input, 'backward')).not.toThrow()
  })

  it('rejects a dying-wire endpoint that is not an atom head', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const use = builder.ref(negative, 'UseRelation', relSig([relSig([])]))
    const relation = builder.wire(negative, [{
      node: use,
      port: { kind: 'arg', index: 0 },
    }], relSig([]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, {
      kind: 'relation',
      wire: relation,
      content: mkDiagramWithBoundary(new DiagramBuilder().build(), []),
      parameters: [],
    })).toThrowError(/endpoint.*atom head/i)
  })

  it('rejects a headed atom whose signature or required argument ports disagree', () => {
    const fixture = relationJoinFixture()
    const application = fixture.applications[0]
    const node = fixture.diagram.nodes[application]!
    const mismatched = {
      ...fixture.diagram,
      nodes: {
        ...fixture.diagram.nodes,
        [application]: { ...node, sig: relSig([]) },
      },
    } as Diagram
    expect(() => applyWireJoin(mismatched, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [fixture.parameter],
    })).toThrowError(/headed atom.*signature/i)

    const argument = fixture.arguments[0]
    const missingPort = {
      ...fixture.diagram,
      wires: {
        ...fixture.diagram.wires,
        [argument]: {
          ...fixture.diagram.wires[argument]!,
          endpoints: [],
        },
      },
    } as Diagram
    expect(() => applyWireJoin(missingPort, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [fixture.parameter],
    })).toThrowError(/required argument port/i)
  })

  it('rejects content with too few formal boundary positions', () => {
    const fixture = relationJoinFixture()
    expect(() => applyWireJoin(fixture.diagram, {
      kind: 'relation',
      wire: fixture.relation,
      content: mkDiagramWithBoundary(new DiagramBuilder().build(), []),
      parameters: [],
    })).toThrowError(/at least 1 boundary|too few.*formal/i)
  })

  it('rejects a formal boundary-prefix signature mismatch', () => {
    const contentBuilder = new DiagramBuilder()
    const relationalStub = contentBuilder.relWire(
      contentBuilder.root,
      relSig([]),
    )
    const fixture = relationJoinFixture()
    expect(() => applyWireJoin(fixture.diagram, {
      kind: 'relation',
      wire: fixture.relation,
      content: mkDiagramWithBoundary(
        contentBuilder.build(),
        [relationalStub],
      ),
      parameters: [],
    })).toThrowError(/formal boundary.*signature/i)
  })

  it('rejects parameter count and signature mismatches against the boundary suffix', () => {
    const fixture = relationJoinFixture()
    expect(() => applyWireJoin(fixture.diagram, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [],
    })).toThrowError(/parameter count|boundary suffix/i)

    const builder = new DiagramBuilder()
    const relationParameter = builder.relWire(builder.root, relSig([]))
    const host = {
      ...fixture.diagram,
      wires: {
        ...fixture.diagram.wires,
        [relationParameter]: builder.build().wires[relationParameter]!,
      },
    } as Diagram
    expect(() => applyWireJoin(host, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [relationParameter],
    })).toThrowError(/parameter.*signature|boundary suffix.*signature/i)
  })

  it('rejects using the dying relation wire as an ambient parameter', () => {
    const fixture = relationJoinFixture()
    const contentBuilder = new DiagramBuilder()
    const formal = contentBuilder.wire(contentBuilder.root, [])
    const dyingSig = contentBuilder.relWire(
      contentBuilder.root,
      relSig([IOTA]),
    )
    const content = mkDiagramWithBoundary(
      contentBuilder.build(),
      [formal, dyingSig],
    )
    expect(() => applyWireJoin(fixture.diagram, {
      kind: 'relation',
      wire: fixture.relation,
      content,
      parameters: [fixture.relation],
    })).toThrowError(/dying relation wire.*parameter/i)
  })

  it('rejects an ambient parameter whose scope does not enclose the relation scope', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positive = builder.cut(negative)
    const application = builder.atom(positive, relSig([IOTA]))
    const argument = builder.wire(negative, [{
      node: application,
      port: { kind: 'arg', index: 0 },
    }])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const parameter = builder.wire(positive, [])
    const diagram = builder.build()
    expect(argument).toBeDefined()

    expect(() => applyWireJoin(diagram, {
      kind: 'relation',
      wire: relation,
      content: unaryContent(),
      parameters: [parameter],
    })).toThrowError(/parameter.*scope.*enclose.*relation scope/i)
  })

  it('rejects an application outside the dying wire scope', () => {
    const fixture = relationJoinFixture()
    const application = fixture.applications[0]
    const node = fixture.diagram.nodes[application]!
    const forged = {
      ...fixture.diagram,
      nodes: {
        ...fixture.diagram.nodes,
        [application]: { ...node, region: fixture.diagram.root },
      },
    } as Diagram

    expect(() => applyWireJoin(forged, {
      kind: 'relation',
      wire: fixture.relation,
      content: unaryContent(),
      parameters: [fixture.parameter],
    })).toThrowError(/application.*outside.*scope|scope.*does not enclose.*application/i)
  })

  it('rejects relation wires passed through the iota variant', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const first = builder.relWire(builder.root, relSig([]))
    const second = builder.relWire(negative, relSig([]))
    const diagram = builder.build()
    expect(() => applyWireJoin(diagram, {
      kind: 'iota',
      a: first,
      b: second,
    })).toThrowError(/iota.*requires.*iota|relation.*iota/i)
  })
})
