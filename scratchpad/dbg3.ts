import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { WireId } from '../src/kernel/diagram/diagram'
import { mkEngine } from '../src/view/engine'
import type { WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function fourWay() { const b = new DiagramBuilder(); const r1 = b.ref(b.root, 'a', rel(3)); const r2 = b.ref(b.root, 'bb', rel(3)); const r3 = b.ref(b.root, 'cc', rel(3)); const r4 = b.ref(b.root, 'dd', rel(3)); b.wire(b.root, [{ node: r1, port: { kind: 'arg', index: 0 } }, { node: r2, port: { kind: 'arg', index: 0 } }, { node: r3, port: { kind: 'arg', index: 0 } }, { node: r4, port: { kind: 'arg', index: 0 } }]); return b.build() }
function pairing(w: WireView) { const per = new Map<number, number[]>(); for (const leg of w.legs) { let br = -1, term = -1; for (const end of [leg.a, leg.b]) { if (end.kind === 'branch') br = end.i; if (end.kind === 'bind') term = end.i } if (br >= 0 && term >= 0) { const a = per.get(br) ?? []; a.push(term); per.set(br, a) } } return [...per.values()].map(a => a.sort().join('')).sort().join('|') }
const gap = (w: WireView) => Math.hypot(w.branches[0]!.x - w.branches[1]!.x, w.branches[0]!.y - w.branches[1]!.y)
function place(e:any,w:WireView,corners:any[]){const ids=[...e.bodies.values()].filter((x:any)=>x.kind==='ref').map((x:any)=>x.id);const cx=(corners[0].x+corners[1].x+corners[2].x+corners[3].x)/4,cy=(corners[0].y+corners[1].y+corners[2].y+corners[3].y)/4;const pinned=new Set<string>();ids.forEach((id:string,n:number)=>{const b=e.bodies.get(id)!;b.pos={...corners[n]};const la=b.localAnchor.get(w.binds[n]!.key)!;b.theta=Math.atan2(cy-b.pos.y,cx-b.pos.x)-Math.atan2(la.y,la.x);pinned.add(id)});return pinned}
const e=mkEngine(fourWay(),[]as readonly WireId[]);const w=[...e.wires.values()].find(x=>x.binds.length===4)!
// start TALL (height>width): 0,1 top pair, 2,3 bottom pair -> 02|13 with branches vertical? build the natural seed then settle
let pinned=place(e,w,[{x:-8,y:-40},{x:8,y:-40},{x:-8,y:40},{x:8,y:40}]);e.frame=null;recomputeRegions(e);establishFrame(e)
for(let t=0;t<2000;t++)if(!settleStep(e,pinned))break
console.log('TALL settled:',pairing(w),'gap',gap(w).toFixed(3),'E',totalEnergy(e).toFixed(1),'b',JSON.stringify(w.branches.map(p=>({x:+p.x.toFixed(1),y:+p.y.toFixed(1)}))))
// now DRAG terminals from tall to wide over many steps
const tall=[{x:-8,y:-40},{x:8,y:-40},{x:-8,y:40},{x:8,y:40}]
const wide=[{x:-40,y:-8},{x:-40,y:8},{x:40,y:-8},{x:40,y:8}]
let lastp=pairing(w),crosses=0,minGap=Infinity
const N=120
for(let s=1;s<=N;s++){const f=s/N;const tg=tall.map((p,i)=>({x:p.x+(wide[i]!.x-p.x)*f,y:p.y+(wide[i]!.y-p.y)*f}))
  const ids=[...e.bodies.values()].filter((x:any)=>x.kind==='ref').map((x:any)=>x.id)
  ids.forEach((id:string,n:number)=>{const b=e.bodies.get(id)!;b.pos={...tg[n]!}})
  for(let t=0;t<15;t++){settleStep(e,pinned);const g=gap(w);minGap=Math.min(minGap,g);if(pairing(w)!==lastp){crosses++;console.log(`  s${s}(f=${f.toFixed(2)}) ${lastp}->${pairing(w)} gap=${g.toFixed(4)} E=${totalEnergy(e).toFixed(1)}`);lastp=pairing(w)}}
  if(s%20===0)console.log(`s${s} pair=${pairing(w)} gap=${gap(w).toFixed(2)} minGap=${minGap.toFixed(4)}`)}
console.log('FINAL',pairing(w),'minGap',minGap.toFixed(4),'crosses',crosses)
