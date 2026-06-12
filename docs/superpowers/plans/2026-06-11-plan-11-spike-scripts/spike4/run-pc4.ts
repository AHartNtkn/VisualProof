import { checkTheorem } from '../../../../../src/kernel/proof/theorem'
import type { ProofContext } from '../../../../../src/kernel/proof/step'
import { fregeDefinitions } from '../../../../../src/theories/frege'
import { p } from './lib4'
import { deriveSuccShiftS4 } from './succshift4'
import { derivePlusComm4 } from './pluscomm4'

const ctx0: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
const ss = deriveSuccShiftS4(ctx0, true)
checkTheorem(ss, ctx0)
console.log(`succShiftS4 checkTheorem PASSED (${ss.steps.length} steps)`)
const ctx1: ProofContext = { definitions: fregeDefinitions, theorems: new Map([[ss.name, ss]]) }
const pc = derivePlusComm4(ctx1, false)
checkTheorem(pc, ctx1)
console.log(`plusComm4 checkTheorem PASSED (${pc.steps.length} steps)`)
const rootNodes = (d: typeof pc.lhs.diagram) => Object.values(d.nodes).filter((n) => n.region === d.root).length
const eps = (d: typeof pc.lhs.diagram, w: string) => d.wires[w]!.endpoints.length
console.log('audit: lhs/rhs root nodes:', rootNodes(pc.lhs.diagram), rootNodes(pc.rhs.diagram),
  '| wa endpoints lhs/rhs:', eps(pc.lhs.diagram, pc.lhs.boundary[0]!), eps(pc.rhs.diagram, pc.rhs.boundary[0]!),
  '| wb endpoints lhs/rhs:', eps(pc.lhs.diagram, pc.lhs.boundary[1]!), eps(pc.rhs.diagram, pc.rhs.boundary[1]!))
const count = (d: typeof pc.lhs.diagram) =>
  [Object.keys(d.nodes).length, Object.keys(d.regions).length, Object.keys(d.wires).length].join('/')
console.log('audit deltas (nodes/regions/wires): ss lhs', count(ss.lhs.diagram), 'rhs', count(ss.rhs.diagram),
  '| pc lhs', count(pc.lhs.diagram), 'rhs', count(pc.rhs.diagram))
const rootTerms = Object.values(pc.rhs.diagram.nodes)
  .filter((n) => n.kind === 'term' && n.region === pc.rhs.diagram.root)
  .map((n) => (n.kind === 'term' ? JSON.stringify(n.term) : ''))
console.log('audit: rhs root node terms are both PLUS s0 s1:',
  rootTerms.length === 2 && rootTerms.every((t) => t === JSON.stringify(p('PLUS s0 s1'))))
