import type { RegionId } from '../../kernel/diagram/diagram'
import type { ProofStep } from '../../kernel/proof/step'
import { parseTerm } from '../../kernel/term/parse'
import { freePorts } from '../../kernel/term/term'

export function closedTermIntroStep(source: string, region: RegionId): ProofStep {
  const term = parseTerm(source)
  const free = freePorts(term)
  if (free.length > 0) {
    throw new Error(
      `closed-term introduction requires a closed term; free ports [${free.map((name) => `'${name}'`).join(', ')}] remain`,
    )
  }
  return { rule: 'closedTermIntro', region, term }
}
