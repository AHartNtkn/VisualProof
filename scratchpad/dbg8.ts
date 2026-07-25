import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import type { WireId } from '../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg, traceLeg } from '../src/view/engine'
import type { WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../src/view/relax'
import { QN, mkLegCache } from '../src/view/elastica'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function fourWay() { const b = new DiagramBuilder(); const r1 = b.ref(b.root, 'a', rel(3)); const r2 = b.ref(b.root, 'bb', rel(3)); const r3 = b.ref(b.root, 'cc', rel(3)); const r4 = b.ref(b.root, 'dd', rel(3)); b.wire(b.root, [{ node: r1, port: { kind: 'arg', index: 0 } }, { node: r2, port: { kind: 'arg', index: 0 } }, { node: r3, port: { kind: 'arg', index: 0 } }, { node: r4, port: { kind: 'arg', index: 0 } }]); return b.build() }
function pairing(w: WireView) { const per = new Map<number, number[]>(); for (const leg of w.legs) { let br = -1, term = -1; for (const end of [leg.a, leg.b]) { if (end.kind === 'branch') br = end.i; if (end.kind === 'bind') term = end.i } if (br >= 0 && term >= 0) { const a = per.get(br) ?? []; a.push(term); per.set(br, a) } } return [...per.values()].map(a => a.sort().join('')).sort().join('|') }
const gap = (w: WireView) => Math.hypot(w.branches[0]!.x - w.branches[1]!.x, w.branches[0]!.y - w.branches[1]!.y)
function cloud(e:any,w:WireView){const pts:any[]=[];for(const leg of w.legs){const s=resolveLeg(e,w,leg);const o:any[]=[];traceLeg(s,o,QN);for(const p of o)pts.push(p)}return pts.sort((a,b)=>a.x-b.x||a.y-b.y)}
function haus(a:any[],b:any[]){let w=0;for(const p of a){let best=Infinity;for(const q of b){const d=Math.hypot(p.x-q.x,p.y-q.y);if(d<best)best=d}w=Math.max(w,best)}return w}
const WIDE = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]
// CLEAN near-face seed of 01|23: branches at (-eps,0),(eps,0) straight, terminal legs clean
function cleanSeed(gap0:number){const e=mkEngine(fourWay(),[]as readonly WireId[]);const w=[...e.wires.values()].find(x=>x.binds.length===4)!;const c=WIDE;const cx=0,cy=0;const pinned=new Set<string>();w.binds.forEach((bd,n)=>{const b=e.bodies.get(bd.body)!;b.pos={...c[n]!};const la=b.localAnchor.get(bd.key)!;b.theta=Math.atan2(cy-b.pos.y,cx-b.pos.x)-Math.atan2(la.y,la.x);pinned.add(bd.body)});
  const bind=(n:number):WireLegEnd=>({kind:'bind',i:n});const br=(n:number):WireLegEnd=>({kind:'branch',i:n});const B0={x:-gap0/2,y:0},B1={x:gap0/2,y:0};const chord=(f:any,t:any)=>Math.atan2(t.y-f.y,t.x-f.x);const mk=(a:WireLegEnd,b:WireLegEnd,f:any,t:any):WireLeg=>({a,b,angA:chord(f,t),angB:chord(f,t),cache:mkLegCache()});
  w.branches.length=0;w.branches.push(B0,B1);w.legs.length=0;for(const lg of[mk(bind(0),br(0),c[0]!,B0),mk(bind(1),br(0),c[1]!,B0),mk(bind(2),br(1),c[2]!,B1),mk(bind(3),br(1),c[3]!,B1),mk(br(0),br(1),B0,B1)])w.legs.push(lg);
  recomputeRegions(e);establishFrame(e);return{e,w,pinned}}
{const{e,w,pinned}=cleanSeed(0.006);console.log('clean seed 01|23 gap',gap(w).toFixed(4),'E',totalEnergy(e).toFixed(2));let checked=false;for(let t=0;t<50;t++){const p0=pairing(w);const before=cloud(e,w);settleStep(e,pinned);if(pairing(w)!==p0){const after=cloud(e,w);const d=Math.max(haus(before,after),haus(after,before));console.log(`CROSS t${t}: ${p0}->${pairing(w)} gap=${gap(w).toFixed(4)} haus=${d.toFixed(4)}`);checked=true;break}}if(!checked)console.log('final',pairing(w),'gap',gap(w).toFixed(4),'NO CROSS')}
console.log('--- per-leg trace endpoints before/after cross ---')
{const{e,w,pinned}=cleanSeed(0.006)
 function legdump(tag:string){for(let i=0;i<w.legs.length;i++){const s=resolveLeg(e,w,w.legs[i]!);const o:any[]=[];traceLeg(s,o,QN);let mnx=1e9,mxx=-1e9,mny=1e9,mxy=-1e9;for(const p of o){mnx=Math.min(mnx,p.x);mxx=Math.max(mxx,p.x);mny=Math.min(mny,p.y);mxy=Math.max(mxy,p.y)}console.log(`${tag} leg${i} a=${w.legs[i]!.a.kind}${(w.legs[i]!.a as any).i??''} b=${w.legs[i]!.b.kind}${(w.legs[i]!.b as any).i??''} L=${s.sol.L.toFixed(2)} bbox=[${mnx.toFixed(1)},${mny.toFixed(1)}..${mxx.toFixed(1)},${mxy.toFixed(1)}]`)}}
 legdump('BEFORE')
 const p0=pairing(w);for(let t=0;t<50;t++){settleStep(e,pinned);if(pairing(w)!==p0){console.log('crossed to',pairing(w),'at t'+t);break}}
 legdump('AFTER ')}
