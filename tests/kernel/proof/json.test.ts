import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyConversion } from '../../../src/kernel/rules/conversion'
import type { ProofStep } from '../../../src/kernel/proof/step'
import { stepToJson, stepFromJson, theoremToJson, theoremFromJson, dwbToJson, dwbFromJson } from '../../../src/kernel/proof/json'
import type { Theorem } from '../../../src/kernel/proof/theorem'
import type { ProofAction } from '../../../src/kernel/proof/action'

const p = (s: string) => parseTerm(s)

function roundTrip(s: ProofStep): void {
  const j = JSON.parse(JSON.stringify(stepToJson(s)))
  expect(stepFromJson(j)).toEqual(s)
}

describe('step round-trips through JSON', () => {
  it('covers every step kind', () => {
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const pat = mkDiagramWithBoundary(b.build(), [bw])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    // the node's source free 'y' is canonical s0 after construction
    const { certificate } = applyConversion(d, n, p('s0'), 10)

    const sel = { region: 'r0', regions: ['r1'], nodes: ['n0'], wires: ['w0'] }
    const steps: ProofStep[] = [
      { rule: 'openTermSpawn', region: 'r1', term: p('x') },
      { rule: 'relationSpawn', region: 'r1', defId: 'nat', arity: 1 },
      { rule: 'boundRelationSpawn', region: 'r1', binder: 'r2', arity: 2 },
      { rule: 'wireJoin', a: 'w0', b: 'w1' },
      { rule: 'erasure', sel },
      { rule: 'wireSever', wire: 'w0', keep: [{ node: 'n0', port: { kind: 'freeVar', name: 'y' } }] },
      { rule: 'iteration', sel, target: 'r1' },
      { rule: 'deiteration', sel, fuel: 50 },
      { rule: 'doubleCutIntro', sel },
      { rule: 'doubleCutElim', region: 'r1' },
      { rule: 'conversion', node: 'n0', term: p('s0'), certificate, attachments: { z: 'w0' } },
      { rule: 'congruenceJoin', a: 'n0', b: 'n1', certificate },
      { rule: 'anchoredWireSplit', wire: 'w0', witness: 'n0', endpoints: [
        { node: 'n1', port: { kind: 'freeVar', name: 's0' } },
      ], target: 'r1' },
      { rule: 'anchoredWireContract', redundant: 'n0', survivor: 'n1', certificate },
      { rule: 'headStrip', a: 'n0', b: 'n1' },
      { rule: 'closedTermIntro', region: 'r1', term: p('\\x. \\y. x') },
      { rule: 'fusion', wire: 'w0' },
      { rule: 'fission', node: 'n0', path: ['fn', 'arg'] },
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat, attachments: [], binders: {} },
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat, attachments: ['w3', 'w7'], binders: {} },
      { rule: 'comprehensionAbstract', wrap: sel, comp: pat, occurrences: [{ sel, args: ['w0'] }] },
      { rule: 'theorem', name: 'dropQ', at: { sel, args: ['w0'] }, direction: 'reverse' },
      { rule: 'vacuousIntro', sel, arity: 2 },
      { rule: 'vacuousElim', region: 'r1' },
      { rule: 'relUnfold', node: 'n0' },
      { rule: 'relFold', sel, defId: 'nat', args: ['w0'] },
    ]
    for (const s of steps) roundTrip(s)
  })

  it('rejects malformed steps loudly', () => {
    expect(() => stepFromJson({ rule: 'nonsense' })).toThrowError(/malformed proof JSON/)
    expect(() => stepFromJson({ rule: 'insertion', region: 'r1', pattern: {}, attachments: [], binders: {} }))
      .toThrowError(/unknown rule 'insertion'/)
    expect(() => stepFromJson({ rule: 'erasure', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, extra: 1 }))
      .toThrowError(/unknown field 'extra'/)
    expect(() => stepFromJson({ rule: 'fission', node: 'n0', path: ['sideways'] }))
      .toThrowError(/path segment/)
    expect(() => stepFromJson({ rule: 'headStrip', a: 'n0', b: 'n1', certificate: { leftSteps: [], rightSteps: [] } }))
      .toThrowError(/unknown field 'certificate'/)
    expect(() => stepFromJson({
      ...(stepToJson({ rule: 'closedTermIntro', region: 'r1', term: p('\\x. x') }) as Record<string, unknown>),
      node: 'n0',
    })).toThrowError(/unknown field 'node'/)
    expect(() => stepFromJson({ rule: 'deiteration', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, fuel: -1 }))
      .toThrowError(/fuel/)
    expect(() => stepFromJson({ rule: 'relUnfold', node: 'n0', extra: 1 }))
      .toThrowError(/unknown field 'extra'/)
    expect(() => stepFromJson({ rule: 'relFold', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, defId: 'nat', args: ['w0'], extra: 1 }))
      .toThrowError(/unknown field 'extra'/)
  })

  it('requires the attachments field on comprehensionInstantiate — no optional-field parsing', () => {
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('\\x. x'))
    const bw = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const pat = mkDiagramWithBoundary(b.build(), [bw])
    const j = JSON.parse(JSON.stringify(stepToJson(
      { rule: 'comprehensionInstantiate', bubble: 'r1', comp: pat, attachments: [], binders: {} },
    ))) as Record<string, unknown>
    delete j['attachments']
    expect(() => stepFromJson(j)).toThrowError(/attachments must be an array/)
    expect(() => stepFromJson({ ...j, attachments: [], extra: 1 })).toThrowError(/unknown field 'extra'/)
  })

  it('requires every anchored wire split field and rejects unknown fields', () => {
    const valid = {
      rule: 'anchoredWireSplit',
      wire: 'w0',
      witness: 'n0',
      endpoints: [{ node: 'n1', port: 'a:0' }],
      target: 'r1',
    }
    const withoutRule: Record<string, unknown> = { ...valid }
    delete withoutRule['rule']
    expect(() => stepFromJson(withoutRule)).toThrowError(/step.rule must be a string/)
    for (const field of ['wire', 'witness', 'target'] as const) {
      const malformed: Record<string, unknown> = { ...valid }
      delete malformed[field]
      expect(() => stepFromJson(malformed)).toThrowError(new RegExp(`${field} must be a string`))
    }
    const withoutEndpoints: Record<string, unknown> = { ...valid }
    delete withoutEndpoints['endpoints']
    expect(() => stepFromJson(withoutEndpoints)).toThrowError(/endpoints must be an array/)
    expect(() => stepFromJson({ ...valid, extra: 1 })).toThrowError(/anchoredWireSplit step has unknown field 'extra'/)
  })

  it('requires the anchored wire contraction certificate and rejects unknown fields', () => {
    const valid = {
      rule: 'anchoredWireContract',
      redundant: 'n0',
      survivor: 'n1',
      certificate: { leftSteps: [], rightSteps: [] },
    }
    const withoutCertificate: Record<string, unknown> = { ...valid }
    delete withoutCertificate['certificate']
    expect(() => stepFromJson(withoutCertificate)).toThrowError(/certificate must be an object/)
    expect(() => stepFromJson({ ...valid, extra: 1 })).toThrowError(/anchoredWireContract step has unknown field 'extra'/)
  })
})

describe('certFromJson rejects invalid reduction-step kinds', () => {
  it('rejects a conversion whose certificate has kind "gamma" instead of beta|eta', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { certificate } = applyConversion(d, n, p('s0'), 10)
    // Build a valid conversion step JSON, then corrupt one reduction-step kind
    const step: ProofStep = { rule: 'conversion', node: 'n0', term: p('s0'), certificate, attachments: {} }
    const j = JSON.parse(JSON.stringify(stepToJson(step))) as Record<string, unknown>
    const cert = j['certificate'] as { leftSteps: unknown[] }
    if (cert.leftSteps.length > 0) {
      ;(cert.leftSteps[0] as Record<string, unknown>)['kind'] = 'gamma'
    } else {
      ;(j['certificate'] as { rightSteps: unknown[] }).rightSteps.push({ kind: 'gamma', path: [] })
    }
    expect(() => stepFromJson(j)).toThrowError(/beta\|eta/)
  })
})

describe('diagram-with-boundary JSON preserves ordered alias incidences', () => {
  it('round-trips repeated boundary positions without collapsing arity', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const aliased = mkDiagramWithBoundary(b.build(), [w, w])
    const back = dwbFromJson(JSON.parse(JSON.stringify(dwbToJson(aliased))))
    expect(back.boundary).toEqual([w, w])
  })
})

describe('dwbFromJson error context', () => {
  it('dwbFromJson includes the what label when boundary wire is missing from diagram', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const serialized = { diagram: { root: b.build().root, regions: b.build().regions, nodes: b.build().nodes, wires: b.build().wires }, boundary: ['nonexistent-wire'] }
    expect(() => dwbFromJson(serialized, "relation 'myRel'")).toThrowError(/relation 'myRel'/)
  })
})

describe('theorem round-trips through JSON', () => {
  it('persists gesture actions with labels, constituent steps, and placements', () => {
    const b = new DiagramBuilder()
    const side = mkDiagramWithBoundary(b.build(), [])
    const action: ProofAction = {
      label: 'introduce two cuts',
      steps: [
        { rule: 'doubleCutIntro', sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] } },
        { rule: 'doubleCutElim', region: 'dc' },
      ],
      placements: [{ introducedNode: 0, x: 12, y: -4 }],
    }
    const theorem: Theorem = { name: 'grouped', lhs: side, rhs: side, actions: [action], backActions: [] }
    const json = theoremToJson(theorem) as Record<string, unknown>
    expect(json).toMatchObject({ actions: [{ label: action.label, placements: action.placements }] })
    expect(theoremFromJson(JSON.parse(JSON.stringify(json))).actions).toEqual([action])
  })

  it('rejects obsolete flat theorem step fields', () => {
    const b = new DiagramBuilder()
    const side = dwbToJson(mkDiagramWithBoundary(b.build(), []))
    expect(() => theoremFromJson({ name: 'old', lhs: side, rhs: side, actions: [], steps: [] }))
      .toThrowError(/unknown field 'steps'/)
    expect(() => theoremFromJson({ name: 'old', lhs: side, rhs: side, actions: [], backSteps: [] }))
      .toThrowError(/unknown field 'backSteps'/)
  })
  it('preserves sides, boundary order, and actions', () => {
    const l = new DiagramBuilder()
    const lp = l.termNode(l.root, p('\\a. a'))
    const lb = l.wire(l.root, [{ node: lp, port: { kind: 'output' } }])
    const side = mkDiagramWithBoundary(l.build(), [lb])
    const t: Theorem = {
      name: 'noop', lhs: side, rhs: side,
      actions: [{ label: 'round trip group', placements: [], steps: [
        { rule: 'doubleCutIntro', sel: { region: side.diagram.root, regions: [], nodes: [], wires: [] } },
        { rule: 'doubleCutElim', region: 'dc' },
      ] }],
    }
    const j = JSON.parse(JSON.stringify(theoremToJson(t)))
    const back = theoremFromJson(j)
    expect(back.name).toBe('noop')
    expect(back.lhs.boundary).toEqual([lb])
    expect(back.actions).toEqual(t.actions)
  })
})
