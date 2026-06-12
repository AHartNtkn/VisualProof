import { checkTheorem } from '../../../../../src/kernel/proof/theorem'
import type { ProofContext } from '../../../../../src/kernel/proof/step'
import { fregeDefinitions } from '../../../../../src/theories/frege'
import { p } from './lib4'
import { deriveSuccShiftS4 } from './succshift4'

const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
const t = deriveSuccShiftS4(ctx, false)
checkTheorem(t, ctx)
const J = JSON.stringify
const zeroAtRoot = (d: typeof t.lhs.diagram): number =>
  Object.values(d.nodes).filter((n) => n.kind === 'term' && n.region === d.root && J(n.term) === J(p('ZERO'))).length
console.log(`succShiftS4 checkTheorem PASSED (${t.steps.length} steps)`)
console.log('audit: lhs/rhs root ZERO nodes:', zeroAtRoot(t.lhs.diagram), zeroAtRoot(t.rhs.diagram),
  '| lhs root nodes:', Object.values(t.lhs.diagram.nodes).filter((n) => n.region === t.lhs.diagram.root).length,
  '| rhs root nodes:', Object.values(t.rhs.diagram.nodes).filter((n) => n.region === t.rhs.diagram.root).length)
