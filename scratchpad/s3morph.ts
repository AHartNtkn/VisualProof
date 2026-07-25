import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import type { Engine } from '../src/view/engine'
import { settleStep, recomputeRegions, establishFrame } from '../src/view/relax'
import { __PROBE2 } from '../src/view/relax'
import { junctionWire, pinAt, minInternal, topoSig, resetProbes, MERGE_EPS } from './harness'
const rel=(n:number)=>relSig(Array.from({length:n},()=>TERM))
function rect4(){const b=new DiagramBuilder();const refs=Array.from({length:4},(_,i)=>b.ref(b.root,`r${i}`,rel(3)));b.wire(b.root,refs.map(r=>({node:r,port:{kind:'arg' as const,index:0}})));const e=mkEngine(b.build(),[]);return{e,w:junctionWire(e)}}
function rest(e:Engine,p:Set<string>,cap:number){for(let t=0;t<cap;t++)if(!settleStep(e,p))break}
const corners=(a:number,b:number)=>[{x:-a,y:-b},{x:-a,y:b},{x:a,y:-b},{x:a,y:b}]
const {e,w}=rect4()
let C=corners(40,12);let pin=pinAt(e,w,C);recomputeRegions(e);establishFrame(e);rest(e,pin,2000)
console.error(`start a40 b12: topo=${topoSig(w)} minL=${minInternal(w).toFixed(4)}`)
resetProbes();let minEver=minInternal(w);const N=120
for(let i=1;i<=N;i++){const u=i/N;const a=40+(12-40)*u,b=12+(40-12)*u;pin=pinAt(e,w,corners(a,b));rest(e,pin,300);const mi=minInternal(w);minEver=Math.min(minEver,mi);if(i%15===0||mi<1)console.error(`  step${i} a=${a.toFixed(1)} b=${b.toFixed(1)} aspect=${(a/b).toFixed(2)}: topo=${topoSig(w)} minL=${mi.toFixed(4)} cross=${__PROBE2.faceCross.length}`)}
console.error(`quasi-static wide->tall morph: minL EVER=${minEver.toFixed(5)} reachedFace=${minEver<=MERGE_EPS} totalCrossings=${__PROBE2.faceCross.length}`)
