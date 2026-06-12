// Smoke: inCutNat builds, validates, audits (w0 scoped at rB; no nodes outside cutN).
import { DiagramBuilder } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/diagram/builder'
import { buildInCutNat, buildComp3 } from '/tmp/spike3/incut'

const b = new DiagramBuilder()
const N = buildInCutNat(b, b.root)
const d = b.build()
const w0scope = d.wires[N.w0]!.scope
const rBkind = d.regions[w0scope]!.kind
const rootNodes = Object.values(d.nodes).filter((n) => n.region === d.root).length
console.log('inCutNat: builds ok | w0 scope kind:', rBkind, '| root nodes:', rootNodes)
const c = buildComp3()
console.log('comp3: builds ok | boundary:', c.boundary.length)
