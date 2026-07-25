import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import type { Engine, WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, __decompose, recomputeRegions, establishFrame } from '../src/view/relax'
import { __PROBE2 } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
import { junctionWire, pinAt, minInternal, internalEdges, topoSig, resetProbes, MERGE_EPS } from './harness'
const rel=(n:number)=>relSig(Array.from({length:n},()=>TERM))
function rect4(){const b=new DiagramBuilder();const refs=Array.from({length:4},(_,i)=>b.ref(b.root,`r${i}`,rel(3)));b.wire(b.root,refs.map(r=>({node:r,port:{kind:'arg' as const,index:0}})));const e=mkEngine(b.build(),[]);return{e,w:junctionWire(e)}}
function setPairing(w:WireView,i:number,j:number,k:number,l:number,c:{x:number;y:number}[],b0:any,b1:any){const bd=(n:number):WireLegEnd=>({kind:'bind',i:n});const br=(n:number):WireLegEnd=>({kind:'branch',i:n});const ch=(f:any,t:any)=>Math.atan2(t.y-f.y,t.x-f.x);const mk=(a:WireLegEnd,bb:WireLegEnd,f:any,t:any):WireLeg=>({a,b:bb,angA:ch(f,t),angB:ch(f,t),cache:mkLegCache()});w.branches.length=0;w.branches.push({...b0},{...b1});w.legs.length=0;for(const lg of [mk(bd(i),br(0),c[i]!,b0),mk(bd(j),br(0),c[j]!,b0),mk(bd(k),br(1),c[k]!,b1),mk(bd(l),br(1),c[l]!,b1),mk(br(0),br(1),b0,b1)])w.legs.push(lg)}
function rest(e:Engine,p:Set<string>,cap:number){let n=0;for(let t=0;t<cap;t++){n++;if(!settleStep(e,p))break}return n}
const corners=(a:number,b:number)=>[{x:-a,y:-b},{x:-a,y:b},{x:a,y:-b},{x:a,y:b}]
function decomp(e:Engine,w:WireView,tag:string){const es=internalEdges(w);if(!es.length){console.error(`  ${tag}: no internal edge`);return}const ed=es.reduce((a,b)=>a.len<b.len?a:b);const before=__decompose(e);const p=w.branches[ed.bi]!,q=w.branches[ed.bj]!;const mx=(p.x+q.x)/2,my=(p.y+q.y)/2;const L=ed.len;const frac=Math.min(0.5,(MERGE_EPS*2)/Math.max(L,1e-6));const sp={...p},sq={...q};w.branches[ed.bi]={x:p.x+(mx-p.x)*frac,y:p.y+(my-p.y)*frac};w.branches[ed.bj]={x:q.x+(mx-q.x)*frac,y:q.y+(my-q.y)*frac};const dL=L*frac;const after=__decompose(e);w.branches[ed.bi]=sp;w.branches[ed.bj]=sq;const keys=Object.keys(before) as (keyof typeof before)[];const rows=keys.map(k=>({k,d:after[k]-before[k]})).filter(r=>Math.abs(r.d)>1e-7).sort((a,b)=>Math.abs(b.d)-Math.abs(a.d));const net=rows.reduce((s,r)=>s+r.d,0)/-dL;console.error(`  ${tag}: floor ℓ=${L.toFixed(4)}, per-term dE/dℓ (compress Δℓ=${dL.toFixed(4)}):`);for(const r of rows)console.error(`     ${r.k.padEnd(12)} dE/dℓ=${(r.d/-dL).toFixed(3)}`);console.error(`     NET dE/dℓ=${net.toFixed(3)}  (>0: shrink lowers E -> wants face; <0: shrink raises E -> floored by these terms)`)}

// (A) decompose the OPTIMAL 03|12 rest (ℓ=0.37) — what holds it at 0.37 not 0?
{const C=corners(40,12);const{e,w}=rect4();const pin=pinAt(e,w,C);setPairing(w,0,3,1,2,C,{x:-20,y:0},{x:20,y:0});recomputeRegions(e);establishFrame(e);rest(e,pin,3000);console.error(`(A) forced-optimal 03|12 rest: topo=${topoSig(w)} minL=${minInternal(w).toFixed(4)} E=${totalEnergy(e).toFixed(1)}`);decomp(e,w,'03|12@rest')}

// (B) SQUARE (a=b): degree-4 point optimal? does descent drive edge->0 and cross?
for(const s of [20, 26]){const C=corners(s,s);const{e,w}=rect4();const pin=pinAt(e,w,C);recomputeRegions(e);establishFrame(e);resetProbes();const u=rest(e,pin,3000);console.error(`(B) square ${s}x${s}: birth topo=? rest topo=${topoSig(w)} minL=${minInternal(w).toFixed(4)} E=${totalEnergy(e).toFixed(1)} ticks=${u} crossings=${__PROBE2.faceCross.length}`);decomp(e,w,`square${s}@rest`)}

// (C) birth-near-zero in a SUBOPTIMAL topology: force 02|13 with branches AT the face
//     (ℓ=0.005<MERGE_EPS), settle. Since 03|12 is lower, does the crossing fire?
{const C=corners(40,12);const{e,w}=rect4();const pin=pinAt(e,w,C);setPairing(w,0,2,1,3,C,{x:-0.0025,y:0},{x:0.0025,y:0});recomputeRegions(e);establishFrame(e);resetProbes();console.error(`(C) seed 02|13 AT face ℓ=${minInternal(w).toFixed(5)} (03|12 is lower by ~308): E0=${totalEnergy(e).toFixed(1)}`);const u=rest(e,pin,3000);console.error(`    -> rest topo=${topoSig(w)} minL=${minInternal(w).toFixed(4)} E=${totalEnergy(e).toFixed(1)} ticks=${u} crossings=${__PROBE2.faceCross.length}`);for(const fc of __PROBE2.faceCross)console.error(`       CROSS ei=${fc.ei} ΔE=${(fc.bestE-fc.E0).toFixed(3)} E0=${fc.E0.toFixed(1)}->${fc.bestE.toFixed(1)}`)}

// (D) same but seed 01|23 AT the face (01|23 rests high at 36.9; 03|12 lower). cross?
{const C=corners(40,12);const{e,w}=rect4();const pin=pinAt(e,w,C);setPairing(w,0,1,2,3,C,{x:0,y:-0.0025},{x:0,y:0.0025});recomputeRegions(e);establishFrame(e);resetProbes();console.error(`(D) seed 01|23 AT face ℓ=${minInternal(w).toFixed(5)}: E0=${totalEnergy(e).toFixed(1)}`);const u=rest(e,pin,3000);console.error(`    -> rest topo=${topoSig(w)} minL=${minInternal(w).toFixed(4)} E=${totalEnergy(e).toFixed(1)} ticks=${u} crossings=${__PROBE2.faceCross.length}`);for(const fc of __PROBE2.faceCross)console.error(`       CROSS ei=${fc.ei} ΔE=${(fc.bestE-fc.E0).toFixed(3)} E0=${fc.E0.toFixed(1)}->${fc.bestE.toFixed(1)}`)}
