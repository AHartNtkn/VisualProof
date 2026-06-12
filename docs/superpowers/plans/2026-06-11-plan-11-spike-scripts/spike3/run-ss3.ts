import { checkTheorem } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/theorem'
import type { ProofContext } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/proof/step'
import { fregeDefinitions } from '/home/ahart/Documents/VisualProofAssistant/src/theories/frege'
import { p } from '/tmp/spike2/lib'
import { deriveSuccShift3 } from '/tmp/spike3/succshift3'

const ctx: ProofContext = { definitions: fregeDefinitions, theorems: new Map() }
try {
  const t = deriveSuccShift3(ctx, false)
  checkTheorem(t, ctx)
  const J = JSON.stringify
  const zeroAtRoot = (d: typeof t.lhs.diagram): number =>
    Object.values(d.nodes).filter((n) => n.kind === 'term' && n.region === d.root && J(n.term) === J(p('ZERO'))).length
  console.log(`succShiftS3 checkTheorem PASSED (${t.steps.length} steps)`)
  console.log('audit: lhs root ZERO nodes:', zeroAtRoot(t.lhs.diagram), '| rhs root ZERO nodes:', zeroAtRoot(t.rhs.diagram),
    '| lhs root nodes:', Object.values(t.lhs.diagram.nodes).filter((n) => n.region === t.lhs.diagram.root).length,
    '| rhs root nodes:', Object.values(t.rhs.diagram.nodes).filter((n) => n.region === t.rhs.diagram.root).length)
} catch (err) {
  console.log(`succShiftS3: ERROR — ${err instanceof Error ? err.message : String(err)}`)
}
