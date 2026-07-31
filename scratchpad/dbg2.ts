import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { WireId } from '../src/kernel/diagram/diagram'
import { mkEngine } from '../src/view/engine'
import type { WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame, clampDragToFeasible } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function fourWay() { const b = new DiagramBuilder(); const r1 = b.ref(b.root, 'a', rel(3)); const r2 = b.ref(b.root, 'bb', rel(3)); const r3 = b.ref(b.root, 'cc', rel(3)); const r4 = b.ref(b.root, 'dd', rel(3)); b.wire(b.root, [{ node: r1, port: { kind: 'arg', index: 0 } }, { node: r2, port: { kind: 'arg', index: 0 } }, { node: r3, port: { kind: 'arg', index: 0 } }, { node: r4, port: { kind: 'arg', index: 0 } }]); return b.build() }
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: readonly { x: number; y: number }[]) { const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n }); const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n }); const mid=(a:any,b:any)=>({x:(a.x+b.x)/2,y:(a.y+b.y)/2}); const B0=mid(c[i]!,c[j]!),B1=mid(c[k]!,c[l]!); const chord=(f:any,t:any)=>Math.atan2(t.y-f.y,t.x-f.x); const mk=(a:WireLegEnd,b:WireLegEnd,f:any,t:any):WireLeg=>({a,b,angA:chord(f,t),angB:chord(f,t),cache:mkLegCache()}); w.branches.length=0;w.branches.push(B0,B1);w.legs.length=0;for(const lg of[mk(bind(i),br(0),c[i]!,B0),mk(bind(j),br(0),c[j]!,B0),mk(bind(k),br(1),c[k]!,B1),mk(bind(l),br(1),c[l]!,B1),mk(br(0),br(1),B0,B1)])w.legs.push(lg) }
function pairing(w: WireView) { const per = new Map<number, number[]>(); for (const leg of w.legs) { let br = -1, term = -1; for (const end of [leg.a, leg.b]) { if (end.kind === 'branch') br = end.i; if (end.kind === 'bind') term = end.i } if (br >= 0 && term >= 0) { const a = per.get(br) ?? []; a.push(term); per.set(br, a) } } return [...per.values()].map(a => a.sort().join('')).sort().join('|') }
const gap = (w: WireView) => Math.hypot(w.branches[0]!.x - w.branches[1]!.x, w.branches[0]!.y - w.branches[1]!.y)
function pin(corners: any[], pair: [number, number, number, number]) { const e = mkEngine(fourWay(), [] as readonly WireId[]); const w = [...e.wires.values()].find(x => x.binds.length === 4)!; const cx=(corners[0].x+corners[1].x+corners[2].x+corners[3].x)/4,cy=(corners[0].y+corners[1].y+corners[2].y+corners[3].y)/4; const pinned=new Set<string>(); w.binds.forEach((bd,n)=>{const b=e.bodies.get(bd.body)!;b.pos={...corners[n]};const la=b.localAnchor.get(bd.key)!;b.theta=Math.atan2(cy-b.pos.y,cx-b.pos.x)-Math.atan2(la.y,la.x);pinned.add(bd.body)}); setPairing(w,pair[0],pair[1],pair[2],pair[3],corners); recomputeRegions(e); establishFrame(e); return{e,w,pinned} }
// The drag scenario from the test: start separated {0,1} left, {2,3} right (SPACED, y=±5)
const startCorners=[{x:-30,y:-5},{x:-30,y:5},{x:60,y:-5},{x:60,y:5}]
const {e,w,pinned}=pin(startCorners,[0,1,2,3])
for(let t=0;t<400;t++)if(!settleStep(e,pinned))break
console.log('after settle:', pairing(w), 'gap', gap(w).toFixed(3), 'E', totalEnergy(e).toFixed(2))
const bodyIds=w.binds.map(bd=>bd.body); const start=bodyIds.map(id=>({...e.bodies.get(id)!.pos}))
let minGap=Infinity, crosses=0, lastp=pairing(w)
const N=60
for(let s=1;s<=N;s++){const f=s/N;const tg=start.map(p=>({...p}));tg[2]={x:60-66*f,y:-5+5*f};tg[3]={x:60-54*f,y:5-5*f}
  for(let t=0;t<20;t++){bodyIds.forEach((id,k)=>{const b=e.bodies.get(id)!;b.pos=clampDragToFeasible(e,b,tg[k]!)});settleStep(e,pinned);const g=gap(w);minGap=Math.min(minGap,g);if(pairing(w)!==lastp){crosses++;console.log(`  s${s} ${lastp}->${pairing(w)} gap=${g.toFixed(4)}`);lastp=pairing(w)}}
  if(s%10===0)console.log(`s${s} pair=${pairing(w)} gap=${gap(w).toFixed(3)} minGapSoFar=${minGap.toFixed(4)} E=${totalEnergy(e).toFixed(1)}`)}
console.log('FINAL', pairing(w),'minGap',minGap.toFixed(4),'crosses',crosses)
