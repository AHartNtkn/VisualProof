import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { WireId } from '../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg, traceLeg } from '../src/view/engine'
import type { WireView } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../src/view/relax'
import { QN } from '../src/view/elastica'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function fourWay() { const b = new DiagramBuilder(); const r1 = b.ref(b.root, 'a', rel(3)); const r2 = b.ref(b.root, 'bb', rel(3)); const r3 = b.ref(b.root, 'cc', rel(3)); const r4 = b.ref(b.root, 'dd', rel(3)); b.wire(b.root, [{ node: r1, port: { kind: 'arg', index: 0 } }, { node: r2, port: { kind: 'arg', index: 0 } }, { node: r3, port: { kind: 'arg', index: 0 } }, { node: r4, port: { kind: 'arg', index: 0 } }]); return b.build() }
function pairing(w: WireView) { const per = new Map<number, number[]>(); for (const leg of w.legs) { let br = -1, term = -1; for (const end of [leg.a, leg.b]) { if (end.kind === 'branch') br = end.i; if (end.kind === 'bind') term = end.i } if (br >= 0 && term >= 0) { const a = per.get(br) ?? []; a.push(term); per.set(br, a) } } return [...per.values()].map(a => a.sort().join('')).sort().join('|') }
const gap = (w: WireView) => Math.hypot(w.branches[0]!.x - w.branches[1]!.x, w.branches[0]!.y - w.branches[1]!.y)
function run(label:string,corners:any[]){const e=mkEngine(fourWay(),[]as readonly WireId[]);const w=[...e.wires.values()].find(x=>x.binds.length===4)!;const cx=(corners[0].x+corners[1].x+corners[2].x+corners[3].x)/4,cy=(corners[0].y+corners[1].y+corners[2].y+corners[3].y)/4;const ids=[...e.bodies.values()].filter((x:any)=>x.kind==='ref').map((x:any)=>x.id);const pinned=new Set<string>();ids.forEach((id:string,n:number)=>{const b=e.bodies.get(id)!;b.pos={...corners[n]};const la=b.localAnchor.get(w.binds[n]!.key)!;b.theta=Math.atan2(cy-b.pos.y,cx-b.pos.x)-Math.atan2(la.y,la.x);pinned.add(id)});e.frame=null;recomputeRegions(e);establishFrame(e)
  let g0=Infinity;for(let t=0;t<3000;t++){if(!settleStep(e,pinned))break;g0=Math.min(g0,gap(w))}
  // internal edge tangent info
  let intInfo='';for(const leg of w.legs){if(leg.a.kind==='branch'&&leg.b.kind==='branch'){const s=resolveLeg(e,w,leg);intInfo=`L=${s.sol.L.toFixed(3)} c1=${s.sol.c1.toFixed(2)} c2=${s.sol.c2.toFixed(2)} angA=${leg.angA.toFixed(2)} angB=${leg.angB.toFixed(2)}`}}
  console.log(`${label}: pair=${pairing(w)} restGap=${gap(w).toFixed(4)} minGap=${g0.toFixed(4)} E=${totalEnergy(e).toFixed(1)} internalEdge[${intInfo}]`)}
run('SQUARE(±30)',[{x:-30,y:-30},{x:30,y:-30},{x:-30,y:30},{x:30,y:30}])
run('SQUARE(±60 big)',[{x:-60,y:-60},{x:60,y:-60},{x:-60,y:60},{x:60,y:60}])
run('DIAMOND(±40)',[{x:0,y:-40},{x:40,y:0},{x:0,y:40},{x:-40,y:0}])
