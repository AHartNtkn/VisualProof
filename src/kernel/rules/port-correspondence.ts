import type { Term } from '../term/term'
import { freePorts, renameFreePorts } from '../term/term'
import { RuleError } from './error'

/** A serializable witness that embeds each term's native free-port names into
 * one finite common carrier. A column may occur on one side only, but every
 * column must occur somewhere and neither side may alias two ports. */
export type PortCorrespondence = {
  readonly commonArity: number
  readonly left: Readonly<Record<string, number>>
  readonly right: Readonly<Record<string, number>>
}

function exactKeys(
  side: 'left' | 'right',
  mapping: Readonly<Record<string, number>>,
  expected: readonly string[],
): void {
  const actual = new Set(Object.keys(mapping))
  const required = new Set(expected)
  const missing = [...required].filter((name) => !actual.has(name)).sort()
  const unexpected = [...actual].filter((name) => !required.has(name)).sort()
  if (missing.length !== 0 || unexpected.length !== 0) {
    throw new RuleError(
      `${side} keys must exactly cover free ports; missing [${missing.join(', ')}]; unexpected [${unexpected.join(', ')}]`,
    )
  }
}

/** Kernel validation for both the finite carrier and its exact term-side domains. */
export function validatePortCorrespondenceCarrier(correspondence: PortCorrespondence): void {
  if (!Number.isSafeInteger(correspondence.commonArity) || correspondence.commonArity < 0) {
    throw new RuleError('port correspondence commonArity must be a non-negative safe integer')
  }
  const covered = new Set<number>()
  for (const side of ['left', 'right'] as const) {
    const seen = new Set<number>()
    for (const [name, column] of Object.entries(correspondence[side])) {
      if (!Number.isSafeInteger(column) || column < 0 || column >= correspondence.commonArity) {
        throw new RuleError(
          `port correspondence ${side} port '${name}' column must be a safe integer in range 0..<${correspondence.commonArity}`,
        )
      }
      if (seen.has(column)) {
        throw new RuleError(`port correspondence must be injective on the ${side}; column ${column} is repeated`)
      }
      seen.add(column)
      covered.add(column)
    }
  }
  if (covered.size !== correspondence.commonArity) {
    let first = 0
    while (covered.has(first)) first++
    throw new RuleError(`port correspondence common column ${first} is uncovered`)
  }
}

export function validatePortCorrespondence(
  correspondence: PortCorrespondence,
  leftPorts: readonly string[],
  rightPorts: readonly string[],
): void {
  validatePortCorrespondenceCarrier(correspondence)
  exactKeys('left', correspondence.left, leftPorts)
  exactKeys('right', correspondence.right, rightPorts)
}

/** Rename a validated side into private carrier names before independent term checking. */
export function mapTermToCommonCarrier(
  term: Term,
  mapping: Readonly<Record<string, number>>,
): Term {
  return renameFreePorts(term, new Map(
    Object.entries(mapping).map(([name, column]) => [name, `__common_port_${column}`]),
  ))
}

/** Deterministic authoring helper. Shared names pair first; remaining native
 * names pair by occurrence order, with either tail receiving one-sided columns. */
export function proposePortCorrespondence(leftTerm: Term, rightTerm: Term): PortCorrespondence {
  const leftPorts = freePorts(leftTerm)
  const rightPorts = freePorts(rightTerm)
  const rightSet = new Set(rightPorts)
  const left: Record<string, number> = {}
  const right: Record<string, number> = {}
  let commonArity = 0

  for (const name of leftPorts) {
    if (!rightSet.has(name)) continue
    left[name] = commonArity
    right[name] = commonArity
    commonArity++
  }
  const leftRest = leftPorts.filter((name) => left[name] === undefined)
  const rightRest = rightPorts.filter((name) => right[name] === undefined)
  const paired = Math.min(leftRest.length, rightRest.length)
  for (let i = 0; i < paired; i++) {
    left[leftRest[i]!] = commonArity
    right[rightRest[i]!] = commonArity
    commonArity++
  }
  for (let i = paired; i < leftRest.length; i++) left[leftRest[i]!] = commonArity++
  for (let i = paired; i < rightRest.length; i++) right[rightRest[i]!] = commonArity++

  return { commonArity, left, right }
}
