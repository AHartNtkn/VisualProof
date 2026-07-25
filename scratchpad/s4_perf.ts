import { bootFixture } from '../tests/app/boot-fixture'
import { mkReplay } from '../src/app/replay'
import { mkEngine } from '../src/view/engine'
import type { Engine } from '../src/view/engine'
import { settle, settleStep, seedProject, establishProofFrame, recomputeRegions } from '../src/view/relax'
import { __PROBE2 } from '../src/view/relax'
import { __PROBE } from '../src/view/engine'
const boot=(await bootFixture()).ctx
const thm=boot.theorems.get('plusComm')!
const r=mkReplay(thm.name,boot)
const steps=Array.from({length:r.actionCount+1},(_,k)=>({diagram:r.diagramAt(k),boundary:r.boundaryAt(k)}))
const probe=mkEngine(r.diagramAt(0),r.boundaryAt(0));establishProofFrame(probe,steps);const frame=probe.frame!
function dofCounts(e:Engine){let br=0,tan=0,end=0,vias=0;for(const w of e.wires.values()){br+=w.branches.length;for(const l of w.legs){if(l.a.kind==='branch')tan++;if(l.b.kind==='branch')tan++}if(w.endBodyId?.startsWith('x:'))vias++;if(w.endBodyId)end++}return{br,tan,end,vias}}
// time a settle of each step (cap 250) to find the slow one
console.error('step timings (settle cap 400, app seed path):')
const times:{k:number;ms:number;rl:number;sweeps:number}[]=[]
for(const k of [16,24,32,40,48,52,60,66]){
  const e=mkEngine(r.diagramAt(k),r.boundaryAt(k));e.frame=frame;seedProject(e)
  __PROBE.resolveLegCalls=0;__PROBE2.teCalls=0;__PROBE2.teMs=0;__PROBE2.fcCalls=0;__PROBE2.faceCross.length=0
  const dc=dofCounts(e)
  const t0=performance.now();let sweeps=0;for(let t=0;t<400;t++){sweeps++;if(!settleStep(e))break}const ms=performance.now()-t0
  times.push({k,ms,rl:__PROBE.resolveLegCalls,sweeps})
  console.error(`  k${k}: ${ms.toFixed(0)}ms sweeps=${sweeps} resolveLegCalls=${__PROBE.resolveLegCalls} teCalls=${__PROBE2.teCalls} teMs=${__PROBE2.teMs.toFixed(0)} fcCalls=${__PROBE2.fcCalls} | DOFs br=${dc.br} tan=${dc.tan} end=${dc.end} vias=${dc.vias}`)
}
const slow=times.reduce((a,b)=>a.ms>b.ms?a:b)
console.error(`\nSLOWEST: k${slow.k} @ ${slow.ms.toFixed(0)}ms. Attribution:`)
// re-profile the slow step precisely
const k=slow.k
const e=mkEngine(r.diagramAt(k),r.boundaryAt(k));e.frame=frame;seedProject(e)
__PROBE.resolveLegCalls=0;__PROBE2.teCalls=0;__PROBE2.teMs=0;__PROBE2.fcCalls=0;__PROBE2.faceCross.length=0
const t0=performance.now();let sweeps=0;for(let t=0;t<400;t++){sweeps++;if(!settleStep(e))break}const ms=performance.now()-t0
console.error(`  total settle: ${ms.toFixed(0)}ms over ${sweeps} sweeps (${(ms/sweeps).toFixed(2)}ms/sweep)`)
console.error(`  resolveLeg (grid solve) calls: ${__PROBE.resolveLegCalls}  (~${(__PROBE.resolveLegCalls/sweeps).toFixed(0)}/sweep)`)
console.error(`  (b) near-face tryFaceCross: fcCalls=${__PROBE2.fcCalls} totalEnergy calls=${__PROBE2.teCalls} time=${__PROBE2.teMs.toFixed(1)}ms (${(100*__PROBE2.teMs/ms).toFixed(2)}% of total)`)
const dc=dofCounts(e)
console.error(`  (a) ∀-via wires in this step: ${dc.vias} -> added ∀-via DOFs = ${dc.vias===0?'ZERO':'see br/tan'}`)
console.error(`  DOFs per sweep: branch=${dc.br} legTangent=${dc.tan} endBody=${dc.end}`)
console.error(`  (c) everything else = ${(ms-__PROBE2.teMs).toFixed(0)}ms (${(100*(ms-__PROBE2.teMs)/ms).toFixed(1)}%) = resolveLeg grid solves in localE gates over ${dc.br+dc.tan+dc.end}+ DOFs × ${sweeps} sweeps`)
