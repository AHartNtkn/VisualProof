import { describe, expect, it } from 'vitest'
import { canonicalArgOrder, defineRelation, inferFoldArgs } from '../../src/app/define'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { sameDiagram } from '../../src/kernel/diagram/canonical/iso'
import type { DiagramNode, RegionId, Wire } from '../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { IOTA } from '../../src/kernel/diagram/sig'
import { findOccurrences } from '../../src/kernel/diagram/subgraph/match'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { extendRelations, verifyTheory } from '../../src/kernel/proof/context'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { BINARY, UNARY } from '../fixtures/zero-signature'
import { segment } from './helpers/build'

function definitionFixture() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, UNARY)
  const head = builder.wire([
    { node: atom, port: { kind: 'head' } },
  ], UNARY)
  // The head wire is internal to the definition, so the pin holding its
  // quantifier is part of the body too.
  const headPin = builder.pin(head, builder.root)
  const argument = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: diagram.root,
    regions: [],
    nodes: [atom, headPin],
    wires: [head],
  })
  return { diagram, selection, argument }
}

function boundedIdentityFixture(swap: boolean) {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const identity = builder.identity(cut, IOTA, 2)
  builder.wire([
    { node: identity, port: { kind: 'identity', index: swap ? 1 : 0 } },
  ])
  builder.wire([
    { node: identity, port: { kind: 'identity', index: swap ? 0 : 1 } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: cut,
    regions: [],
    nodes: [identity],
    wires: [],
  })
  return { diagram, cut, selection }
}

/** One "identity pair" component: an arity-2 identity whose two ports are
 *  pinned by two separate arity-1 identities. Every component built with
 *  this helper is structurally identical to every other (same content keys
 *  throughout) and disconnected from them — no wire crosses between
 *  components — so content-key filtering alone cannot tell them apart. */
function addIdentityPairComponent(
  nodes: Record<string, DiagramNode>,
  wires: Record<string, Wire>,
  region: RegionId,
  tag: string,
): void {
  nodes[`j${tag}`] = { kind: 'identity', region, sig: IOTA, arity: 2 }
  nodes[`pinA${tag}`] = { kind: 'identity', region, sig: IOTA, arity: 1 }
  nodes[`pinB${tag}`] = { kind: 'identity', region, sig: IOTA, arity: 1 }
  wires[`wA${tag}`] = {
    sig: IOTA,
    endpoints: [
      { node: `j${tag}`, port: { kind: 'identity', index: 0 } },
      { node: `pinA${tag}`, port: { kind: 'identity', index: 0 } },
    ],
  }
  wires[`wB${tag}`] = {
    sig: IOTA,
    endpoints: [
      { node: `j${tag}`, port: { kind: 'identity', index: 1 } },
      { node: `pinB${tag}`, port: { kind: 'identity', index: 0 } },
    ],
  }
}

/**
 * A fold body with two mutually disconnected, structurally identical
 * "identity pair" components, matched against a host region holding six
 * such components (the real fold target plus five decoy same-shape
 * candidates). Nothing in propagation can split the pattern components'
 * candidate sets — every host component looks equally viable to either
 * pattern component until injectivity and the identity-port checks cut
 * branches down during backtracking — so a bound derived from element
 * counts alone (elements * host-region-node-count) undercounts the true,
 * multiplicative cost. This is the shape the fuel formula in the previous
 * revision of `inferFoldArgs` mis-refused.
 */
function disconnectedIdentityPairsFoldFixture() {
  const bodyNodes: Record<string, DiagramNode> = {}
  const bodyWires: Record<string, Wire> = {}
  addIdentityPairComponent(bodyNodes, bodyWires, 'broot', '0')
  addIdentityPairComponent(bodyNodes, bodyWires, 'broot', '1')
  const body = mkDiagramWithBoundary(
    {
      root: 'broot',
      regions: { broot: { kind: 'sheet' } },
      nodes: bodyNodes,
      wires: bodyWires,
    },
    [],
  )

  const hostNodes: Record<string, DiagramNode> = {}
  const hostWires: Record<string, Wire> = {}
  for (const tag of ['0', '1', '2', '3', '4', '5']) {
    addIdentityPairComponent(hostNodes, hostWires, 'root', tag)
  }
  const diagram = mkDiagram({
    root: 'root',
    regions: { root: { kind: 'sheet' } },
    nodes: hostNodes,
    wires: hostWires,
  })

  // The real fold target: components '2' and '4', not the first two the
  // search would try — the matcher must reject the other decoy pairings
  // (and, per component, the losing half of the port-swap ambiguity) before
  // landing on this exact selection.
  const selection = mkSelection(diagram, {
    region: diagram.root,
    regions: [],
    nodes: ['j2', 'pinA2', 'pinB2', 'j4', 'pinA4', 'pinB4'],
    wires: ['wA2', 'wB2', 'wA4', 'wB4'],
  })

  return { body, diagram, selection }
}

/**
 * Generalizes `disconnectedIdentityPairsFoldFixture` to `m` pattern
 * components matched against `k` host components (`m` real targets plus
 * `k - m` same-shape decoys), targeting the LAST `m` host tags — the worst
 * case, where the search must reject every earlier decoy component first.
 */
function identityPairScalingFixture(m: number, k: number) {
  const bodyNodes: Record<string, DiagramNode> = {}
  const bodyWires: Record<string, Wire> = {}
  for (let i = 0; i < m; i++) addIdentityPairComponent(bodyNodes, bodyWires, 'broot', String(i))
  const body = mkDiagramWithBoundary(
    { root: 'broot', regions: { broot: { kind: 'sheet' } }, nodes: bodyNodes, wires: bodyWires },
    [],
  )

  const hostNodes: Record<string, DiagramNode> = {}
  const hostWires: Record<string, Wire> = {}
  const tags: string[] = []
  for (let i = 0; i < k; i++) {
    const tag = String(i)
    tags.push(tag)
    addIdentityPairComponent(hostNodes, hostWires, 'root', tag)
  }
  const diagram = mkDiagram({
    root: 'root', regions: { root: { kind: 'sheet' } }, nodes: hostNodes, wires: hostWires,
  })

  const targetTags = tags.slice(k - m)
  const selNodes: string[] = []
  const selWires: string[] = []
  for (const tag of targetTags) {
    selNodes.push(`j${tag}`, `pinA${tag}`, `pinB${tag}`)
    selWires.push(`wA${tag}`, `wB${tag}`)
  }
  return { body, diagram, selNodes, selWires }
}

describe('structural relation definition', () => {
  it('registers and persists bounded identities independent of incidence indices', () => {
    const runs = [false, true].map((swap, index) => {
      const fixture = boundedIdentityFixture(swap)
      const name = `BoundedIdentity${index}`
      const empty = verifyTheory({ relations: [], theorems: [] })
      const { relation } = defineRelation(
        fixture.diagram,
        fixture.selection,
        name,
        empty,
      )
      const ctx = extendRelations(empty, [[name, relation]])
      const serialized = theoryToJson({
        relations: [[name, relation]],
        theorems: [],
      })
      const loaded = loadTheory(JSON.parse(JSON.stringify(serialized)))
      const stored = ctx.relations.get(name)!
      const reloaded = loaded.ctx.relations.get(name)!

      expect(stored.boundary).toHaveLength(2)
      expect(reloaded.boundary).toHaveLength(2)
      return {
        fixture,
        relation,
        reloaded,
      }
    })

    expect(sameDiagram(
      runs[1]!.reloaded.diagram, runs[0]!.reloaded.diagram,
      runs[1]!.reloaded.boundary, runs[0]!.reloaded.boundary,
    )).toBe(true)
    expect(findOccurrences(
      runs[1]!.fixture.diagram,
      runs[0]!.relation,
      { inRegion: runs[1]!.fixture.cut },
    ).matches).toHaveLength(2)
    expect(findOccurrences(
      runs[0]!.fixture.diagram,
      runs[1]!.relation,
      { inRegion: runs[0]!.fixture.cut },
    ).matches).toHaveLength(2)
  })

  it('extracts an exact ordered boundary and infers the same fold attachment', () => {
    const fixture = definitionFixture()
    const { relation } = defineRelation(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    const ctx = verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] })
    expect(relation.boundary).toHaveLength(1)
    expect(inferFoldArgs(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      ctx,
    )).toEqual([fixture.argument])
  })

  it('reports exact structural mismatch without conversion advice', () => {
    const fixture = definitionFixture()
    const { relation } = defineRelation(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    const empty = new DiagramBuilder().build()
    const emptySelection = mkSelection(empty, {
      region: empty.root, regions: [], nodes: [], wires: [],
    })
    expect(() => inferFoldArgs(
      empty,
      emptySelection,
      'LocalUnary',
      verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] }),
    )).toThrow('the selection must match the definition exactly.')
  })

  it('uses canonical boundary order as the sole definition order', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, BINARY)
    const head = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const headPin = builder.pin(head, builder.root)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [atom, headPin], wires: [head],
    })
    const canonical = canonicalArgOrder(diagram, selection)
    const { relation } = defineRelation(
      diagram,
      selection,
      'CanonicalBinary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    expect(canonical).toHaveLength(2)
    expect(relation.boundary).toHaveLength(2)

    const legacy = defineRelation as unknown as (
      d: typeof diagram,
      s: typeof selection,
      order: readonly string[],
      name: string,
      context: ReturnType<typeof verifyTheory>,
    ) => unknown
    expect(() => legacy(
      diagram,
      selection,
      [...canonical].reverse(),
      'ManualBinary',
      verifyTheory({ relations: [], theorems: [] }),
    )).toThrow(/manual boundary order is not supported/)
  })

  it('infers fold args for a body with disconnected, structurally identical substructures against extra same-shape host candidates', () => {
    const { body, diagram, selection } = disconnectedIdentityPairsFoldFixture()
    const ctx = extendRelations(
      verifyTheory({ relations: [], theorems: [] }),
      [['DisconnectedPair', body]],
    )
    expect(inferFoldArgs(diagram, selection, 'DisconnectedPair', ctx)).toEqual([])
  })

  it.each(['region', 'wire'] as const)(
    'rejects an exact occurrence padded with an extra selected %s',
    (extra) => {
      const builder = new DiagramBuilder()
      const atom = builder.atom(builder.root, UNARY)
      const head = builder.wire([
        { node: atom, port: { kind: 'head' } },
      ], UNARY)
      const headPin = builder.pin(head, builder.root)
      builder.wire([
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      const extraRegion = builder.cut(builder.root)
      const extraWire = segment(builder, builder.root)
      const diagram = builder.build()
      const exact = mkSelection(diagram, {
        region: diagram.root, regions: [], nodes: [atom, headPin], wires: [head],
      })
      const { relation } = defineRelation(
        diagram,
        exact,
        'LocalUnary',
        verifyTheory({ relations: [], theorems: [] }),
      )
      const padded = mkSelection(diagram, {
        region: diagram.root,
        regions: extra === 'region' ? [extraRegion] : [],
        nodes: extra === 'wire' ? [atom, headPin, ...extraWire.ends] : [atom, headPin],
        wires: extra === 'wire' ? [head, extraWire.wire] : [head],
      })
      expect(() => inferFoldArgs(
        diagram,
        padded,
        'LocalUnary',
        verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] }),
      )).toThrow('the selection must match the definition exactly.')
    },
  )
})

describe('inferFoldArgs search is bounded by the selection, not the host', () => {
  it('restricts findOccurrences to the selection: derived exact step count, unaffected by decoy count', () => {
    // m=3 pattern components against k=8 host components (5 decoys) is the
    // size at which the UNRESTRICTED search previously exploded.
    const m = 3
    const { body, diagram, selNodes, selWires } = identityPairScalingFixture(m, 8)

    const unrestricted = findOccurrences(diagram, body, { inRegion: diagram.root })
    expect(unrestricted.explorationSteps).toBe(16569)

    const restricted = findOccurrences(diagram, body, {
      inRegion: diagram.root,
      images: { regions: [], nodes: selNodes, wires: selWires },
    })
    // Derivation, traced exactly against match.ts's tryAssign/pickNext (the
    // trace was checked by instrumenting a print of every tryAssign call for
    // m=1, m=3, and m=4 and confirming each against the recursion below):
    //
    // With `images` restricted to precisely this selection's m components,
    // every candidate set is drawn from EXACTLY those 3m nodes and 2m wires
    // — no decoy ever enters any candidate set. The root region is a
    // singleton (`inRegion`), 1 step.
    //
    // Every pattern `j`-node's raw candidate set has size m (one host `j`
    // per component, sharing one content key, never arc-narrowed — only
    // rejected at usage time), UNLESS a component's own elements have
    // already narrowed below m via propagation, which happens only once
    // that component's `j` is actually committed. Since m=3 > 2, a
    // committed component's residual elements (size 2, see below) always
    // rank below an unstarted component's `j` (size 3) in pickNext's
    // smallest-candidate-set order, so each component resolves FULLY, one
    // at a time, before the next component's `j` is ever tried. (This
    // ordering fails for m=2, where the tie between size 2 and size 2 falls
    // to id order instead — m=3 is the smallest case where the clean
    // recursion below holds.)
    //
    // Once a `j` commits to a free host component c (1 step), propagation
    // immediately narrows that component's wA/wB/pinA/pinB candidates from
    // 2m/2m down to {c's own 2 wires}/{c's own 2 pins} (size 2 each) —
    // no other component is affected. pickNext then picks pinA (node rank
    // beats wire rank): the search tries BOTH of pinA's 2 candidates in
    // full (backtracking explores every candidate, not just the first
    // success) — each commits wA (now a singleton, always free, 1 step),
    // then tries BOTH of pinB's 2 candidates (exactly one always collides
    // with pinA's choice and is rejected in 1 step; the other succeeds and
    // commits wB, a singleton, always free, 1 step), then recurses into
    // the remaining components. So one successful `j` commit costs:
    //   1 (j) + 2 branches * (1 pinA + 1 wA + 2 pinB attempts + 1 wB + recurse)
    //   = 1 + 2 * (5 + recurse)
    // Writing R(k) for the total cost of resolving k of the m components
    // still unassigned (a not-yet-tried `j` always has raw candidate size
    // m, so m - k of its m candidates are already-used rejects):
    //   R(0) = 0
    //   R(k) = (m - k) * 1 + k * (1 + 2 * (5 + R(k - 1)))
    //        = (m - k) + k * (11 + 2 * R(k - 1))
    // For m = 3:
    //   R(1) = 2 + 1 * (11 + 2*0)  = 13
    //   R(2) = 1 + 2 * (11 + 2*13) = 1 + 74  = 75
    //   R(3) = 0 + 3 * (11 + 2*75) = 3 * 161 = 483
    // Total = 1 (root) + R(3) = 484 — independent of the host's decoy
    // count k, since `images` removes every decoy from candidacy entirely.
    expect(restricted.explorationSteps).toBe(484)
    expect(restricted.matches).toHaveLength(1)

    // Confirms the independence from k directly: the same selection size m,
    // matched against fewer decoys, costs the identical number of steps.
    const fewerDecoys = identityPairScalingFixture(m, 6)
    const restrictedFewerDecoys = findOccurrences(fewerDecoys.diagram, fewerDecoys.body, {
      inRegion: fewerDecoys.diagram.root,
      images: { regions: [], nodes: fewerDecoys.selNodes, wires: fewerDecoys.selWires },
    })
    expect(restrictedFewerDecoys.explorationSteps).toBe(484)
  })

  it('still infers the correct fold args for the disconnected-pairs regression fixture', () => {
    const { body, diagram, selection } = disconnectedIdentityPairsFoldFixture()
    const ctx = extendRelations(
      verifyTheory({ relations: [], theorems: [] }),
      [['DisconnectedPair', body]],
    )
    expect(inferFoldArgs(diagram, selection, 'DisconnectedPair', ctx)).toEqual([])
  })
})
