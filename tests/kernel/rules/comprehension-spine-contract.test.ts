import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import type { RegionId } from '../../../src/kernel/diagram/diagram'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

function host(targetArities: readonly number[]) {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const targets: RegionId[] = []
  let parent = cut
  for (const arity of targetArities) {
    parent = b.bubble(parent, arity)
    targets.push(parent)
  }
  const eliminated = b.bubble(parent, 0)
  b.atom(eliminated, eliminated)
  return { diagram: b.build(), eliminated, targets }
}

function pattern(proxyArities: readonly number[]) {
  const b = new DiagramBuilder()
  const proxies: RegionId[] = []
  let body = b.root
  for (const arity of proxyArities) {
    body = b.bubble(body, arity)
    proxies.push(body)
  }
  const content = b.ref(body, 'Body', 0)
  return { comp: mkDiagramWithBoundary(b.build(), []), proxies, content }
}

describe('comprehension binder spine positive cases', () => {
  it('uses the pattern root as the body for an empty spine', () => {
    const h = host([])
    const p = pattern([])
    const out = applyComprehensionInstantiate(h.diagram, h.eliminated, p.comp, [], [])

    expect(out.regions[h.eliminated]).toBeUndefined()
    expect(Object.values(out.nodes).some((node) => node.kind === 'ref' && node.defId === 'Body')).toBe(true)
  })

  it('uses one designated proxy as the terminal body container', () => {
    const h = host([1])
    const p = pattern([1])
    const out = applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      p.comp,
      [],
      [[p.proxies[0]!, h.targets[0]!]],
    )

    expect(Object.values(out.regions).filter((region) => region.kind === 'bubble')).toHaveLength(1)
    expect(Object.values(out.nodes).some((node) => node.kind === 'ref' && node.defId === 'Body')).toBe(true)
  })

  it('accepts a multi-proxy outer-to-inner spine and copies only its terminal body', () => {
    const h = host([1, 2])
    const p = pattern([1, 2])
    const out = applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      p.comp,
      [],
      [
        [p.proxies[0]!, h.targets[0]!],
        [p.proxies[1]!, h.targets[1]!],
      ],
    )

    expect(Object.values(out.nodes).some((node) => node.kind === 'ref' && node.defId === 'Body')).toBe(true)
    expect(Object.values(out.regions).filter((region) => region.kind === 'bubble')).toHaveLength(2)
  })
})

describe('comprehension binder spine structural refusals', () => {
  it('rejects sibling mapped proxies', () => {
    const h = host([1, 1])
    const b = new DiagramBuilder()
    const left = b.bubble(b.root, 1)
    const right = b.bubble(b.root, 1)
    const comp = mkDiagramWithBoundary(b.build(), [])

    expect(() => applyComprehensionInstantiate(h.diagram, h.eliminated, comp, [], [
      [left, h.targets[0]!],
      [right, h.targets[1]!],
    ])).toThrowError(/only direct child|root-prefix/i)
  })

  it('rejects an incomplete prefix that skips the outer proxy', () => {
    const h = host([2])
    const p = pattern([1, 2])

    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      p.comp,
      [],
      [[p.proxies[1]!, h.targets[0]!]],
    )).toThrowError(/root-prefix|direct child/i)
  })

  it('rejects a complete proxy set presented in inner-to-outer order', () => {
    const h = host([1, 2])
    const p = pattern([1, 2])

    expect(() => applyComprehensionInstantiate(h.diagram, h.eliminated, p.comp, [], [
      [p.proxies[1]!, h.targets[1]!],
      [p.proxies[0]!, h.targets[0]!],
    ])).toThrowError(/ordered root-prefix/i)
  })

  it('rejects a ghost extra mapping and a non-bubble proxy', () => {
    const h = host([1])
    const p = pattern([])
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      p.comp,
      [],
      [['ghost', h.targets[0]!]],
    )).toThrowError(/ghost.*pattern region/i)

    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const comp = mkDiagramWithBoundary(b.build(), [])
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      comp,
      [],
      [[cut, h.targets[0]!]],
    )).toThrowError(/not a bubble/i)
  })

  it('rejects node content at the root and at a nonterminal proxy', () => {
    const h = host([1, 2])
    const rootImpure = new DiagramBuilder()
    const rootProxy = rootImpure.bubble(rootImpure.root, 1)
    rootImpure.ref(rootImpure.root, 'Impurity', 0)
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      mkDiagramWithBoundary(rootImpure.build(), []),
      [],
      [[rootProxy, h.targets[0]!]],
    )).toThrowError(/root.*node content/i)

    const nestedImpure = new DiagramBuilder()
    const outer = nestedImpure.bubble(nestedImpure.root, 1)
    const inner = nestedImpure.bubble(outer, 2)
    nestedImpure.ref(outer, 'Impurity', 0)
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      mkDiagramWithBoundary(nestedImpure.build(), []),
      [],
      [[outer, h.targets[0]!], [inner, h.targets[1]!]],
    )).toThrowError(/nonterminal.*node content/i)
  })

  it('rejects non-boundary wire scope at the root and at a nonterminal proxy', () => {
    const h = host([1, 2])
    const rootImpure = new DiagramBuilder()
    const rootProxy = rootImpure.bubble(rootImpure.root, 1)
    rootImpure.wire(rootImpure.root, [])
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      mkDiagramWithBoundary(rootImpure.build(), []),
      [],
      [[rootProxy, h.targets[0]!]],
    )).toThrowError(/root.*non-boundary wire/i)

    const nestedImpure = new DiagramBuilder()
    const outer = nestedImpure.bubble(nestedImpure.root, 1)
    const inner = nestedImpure.bubble(outer, 2)
    nestedImpure.wire(outer, [])
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      mkDiagramWithBoundary(nestedImpure.build(), []),
      [],
      [[outer, h.targets[0]!], [inner, h.targets[1]!]],
    )).toThrowError(/nonterminal.*non-boundary wire/i)
  })

  it('rejects extra child content at a nonterminal proxy', () => {
    const h = host([1, 2])
    const b = new DiagramBuilder()
    const outer = b.bubble(b.root, 1)
    const inner = b.bubble(outer, 2)
    b.cut(outer)
    const comp = mkDiagramWithBoundary(b.build(), [])

    expect(() => applyComprehensionInstantiate(h.diagram, h.eliminated, comp, [], [
      [outer, h.targets[0]!],
      [inner, h.targets[1]!],
    ])).toThrowError(/nonterminal.*only direct child/i)
  })
})

describe('comprehension binder pair correspondence refusals', () => {
  it('rejects duplicate pattern proxies and duplicate host targets', () => {
    const h = host([1, 2])
    const p = pattern([1, 2])
    expect(() => applyComprehensionInstantiate(h.diagram, h.eliminated, p.comp, [], [
      [p.proxies[0]!, h.targets[0]!],
      [p.proxies[0]!, h.targets[1]!],
    ])).toThrowError(/duplicate pattern proxy/i)
    expect(() => applyComprehensionInstantiate(h.diagram, h.eliminated, p.comp, [], [
      [p.proxies[0]!, h.targets[0]!],
      [p.proxies[1]!, h.targets[0]!],
    ])).toThrowError(/duplicate host target/i)
  })

  it('rejects proxy/target arity mismatch', () => {
    const h = host([2])
    const p = pattern([1])
    expect(() => applyComprehensionInstantiate(
      h.diagram,
      h.eliminated,
      p.comp,
      [],
      [[p.proxies[0]!, h.targets[0]!]],
    )).toThrowError(/arity mismatch/i)
  })
})
