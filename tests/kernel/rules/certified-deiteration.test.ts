import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import {
  __benchCounter,
  findOccurrences,
  type OccurrenceCertificate,
} from '../../../src/kernel/diagram/subgraph/match'
import { checkOccurrenceCertificate } from '../../../src/kernel/diagram/subgraph/occurrence-certificate'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { parseTerm } from '../../../src/kernel/term/parse'
import { applyStep, type ProofContext, type ProofStep } from '../../../src/kernel/proof/step'
import { stepFromJson, stepToJson } from '../../../src/kernel/proof/json'
import {
  applyDeiteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'

const p = (source: string) => parseTerm(source)
const ctx: ProofContext = { theorems: new Map(), relations: new Map() }

function betaEtaCopies() {
  const builder = new DiagramBuilder()
  const justifier = builder.termNode(builder.root, p('(\\x. x) y'))
  const targetRegion = builder.cut(builder.root)
  const target = builder.termNode(targetRegion, p('y'))
  builder.wire(builder.root, [
    { node: justifier, port: { kind: 'freeVar', name: 'y' } },
    { node: target, port: { kind: 'freeVar', name: 'y' } },
  ])
  builder.wire(builder.root, [
    { node: justifier, port: { kind: 'output' } },
    { node: target, port: { kind: 'output' } },
  ])
  const diagram = builder.build()
  const targetSelection = mkSelection(diagram, {
    region: targetRegion, regions: [], nodes: [target], wires: [],
  })
  const justifierSelection = mkSelection(diagram, {
    region: diagram.root, regions: [], nodes: [justifier], wires: [],
  })
  return { diagram, justifier, target, targetSelection, justifierSelection }
}

describe('certified open occurrences', () => {
  it('betaEta matching retains a mechanically checkable conversion certificate', () => {
    const { diagram, targetSelection } = betaEtaCopies()
    const { pattern } = extractSubgraph(diagram, targetSelection)
    const result = findOccurrences(diagram, pattern, { fuel: 100, mode: 'betaEta' })
    const occurrence = result.matches.find((match) => match.region === diagram.root)!

    expect(occurrence).toBeDefined()
    expect([...occurrence.termCertificates.values()].some(
      (certificate) => certificate.leftSteps.length + certificate.rightSteps.length > 0,
    )).toBe(true)
    expect(checkOccurrenceCertificate(diagram, pattern, occurrence)).toEqual({ ok: true })
  })

  it('exact name-blind matching checks different source port names by position and uses reflexive certificates', () => {
    const builder = new DiagramBuilder()
    const patternNode = builder.termNode(builder.root, p('y'))
    const boundary = builder.wire(builder.root, [
      { node: patternNode, port: { kind: 'freeVar', name: 'y' } },
    ])
    const pattern = { diagram: builder.build(), boundary: [boundary] }
    const hostBuilder = new DiagramBuilder()
    const hostNode = hostBuilder.termNode(hostBuilder.root, p('q'))
    const attachment = hostBuilder.wire(hostBuilder.root, [
      { node: hostNode, port: { kind: 'freeVar', name: 'q' } },
    ])
    const host = hostBuilder.build()
    const occurrence = findOccurrences(host, pattern, {
      fuel: 1, mode: 'exact', attachments: [attachment],
    }).matches[0]!

    expect([...occurrence.termCertificates.values()]).toEqual([
      { leftSteps: [], rightSteps: [] },
    ])
    expect(checkOccurrenceCertificate(host, pattern, occurrence)).toEqual({ ok: true })
  })

  it('rejects tampered graph maps and tampered term evidence', () => {
    const { diagram, targetSelection, target } = betaEtaCopies()
    const { pattern } = extractSubgraph(diagram, targetSelection)
    const occurrence = findOccurrences(diagram, pattern, { fuel: 100 }).matches.find(
      (match) => match.region === diagram.root,
    )!
    const patternNode = [...occurrence.nodeMap.keys()][0]!
    const graphTamper: OccurrenceCertificate = {
      ...occurrence,
      nodeMap: new Map(occurrence.nodeMap).set(patternNode, target),
    }
    expect(checkOccurrenceCertificate(diagram, pattern, graphTamper)).toMatchObject({ ok: false })

    const termTamper: OccurrenceCertificate = {
      ...occurrence,
      termCertificates: new Map(occurrence.termCertificates).set(
        patternNode,
        { leftSteps: [], rightSteps: [] },
      ),
    }
    expect(checkOccurrenceCertificate(diagram, pattern, termTamper)).toMatchObject({ ok: false })
  })
})

describe('certified deiteration replay', () => {
  it('checks the selected certificate directly without matcher search or fuel', () => {
    const { diagram, target, targetSelection, justifierSelection } = betaEtaCopies()
    const evidence = findDeiterationEvidence(diagram, targetSelection, 100)
    expect(evidence.justifier).toEqual(justifierSelection)
    const step: ProofStep = {
      rule: 'deiteration', sel: targetSelection,
      justifier: evidence.justifier, certificate: evidence.certificate,
    }

    __benchCounter.n = 0
    __benchCounter.permutations = 0
    const replayed = applyStep(diagram, step, ctx)
    expect(__benchCounter).toEqual({ n: 0, permutations: 0 })
    expect(replayed.nodes[target]).toBeUndefined()
    expect(exploreForm(replayed)).toBe(exploreForm(
      applyDeiteration(diagram, targetSelection, evidence.justifier, evidence.certificate),
    ))
  })

  it('round-trips the certificate payload through JSON and rejects the removed fuel schema', () => {
    const { diagram, targetSelection } = betaEtaCopies()
    const evidence = findDeiterationEvidence(diagram, targetSelection, 100)
    const step: ProofStep = {
      rule: 'deiteration', sel: targetSelection,
      justifier: evidence.justifier, certificate: evidence.certificate,
    }
    expect(stepFromJson(JSON.parse(JSON.stringify(stepToJson(step))))).toEqual(step)
    expect(() => stepFromJson({
      rule: 'deiteration', sel: targetSelection, fuel: 100,
    })).toThrowError(/unknown field 'fuel'|justifier/)
  })
})
