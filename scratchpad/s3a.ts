import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import type { Engine, WireView, WireLeg, WireLegEnd } from '../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../src/view/relax'
import { mkLegCache } from '../src/view/elastica'
import { junctionWire, pinAt, minInternal, topoSig } from './harness'
const rel = (n:number)=>relSig(Array.from({length:n},()=>TERM))
function rect4(){const b=new DiagramBuilder();const refs=Array.from({length:4},(_,i)=>b.ref(b.root,`r${i}`,rel(3)));b.wire(b.root,refs.map(r=>({node:r,port:{kind:'arg' as const,index:0}})));const e=mkEngine(b.build(),[]);return{e,w:junctionWire(e)}}
function setPairing(w:WireView,i:number,j:number,k:number,l:number,c:{x:number;y:number}[],b0:{x:number;y:number},b1:{x:number;y:number}){const bind=(n:number):WireLegEnd=>({kind:'bind',i:n});const br=(n:number):WireLegEnd=>({kind:'branch',i:n});const ch=(f:any,t:any)=>Math.atan2(t.y-f.y,t.x-f.x);const mk=(a:WireLegEnd,bb:WireLegEnd,f:any,t:any):WireLeg=>({a,b:bb,angA:ch(f,t),angB:ch(f,t),cache:mkLegCache()});w.branches.length=0;w.branches.push({...b0},{...b1});w.legs.length=0;for(const lg of [mk(bind(i),br(0),c[i]!,b0),mk(bind(j),br(0),c[j]!,b0),mk(bind(k),br(1),c[k]!,b1),mk(bind(l),br(1),c[l]!,b1),mk(br(0),br(1),b0,b1)])w.legs.push(lg)}
function rest(e:Engine,p:Set<string>,cap:number){let n=0;for(let t=0;t<cap;t++){n++;if(!settleStep(e,p))break}return n}
const corners=(a:number,b:number)=>[{x:-a,y:-b},{x:-a,y:b},{x:a,y:-b},{x:a,y:b}]
const C=corners(40,12)
const nat=rect4();const pn=pinAt(nat.e,nat.w,C);recomputeRegions(nat.e);establishFrame(nat.e)
const seedTopo=topoSig(nat.w);const u=rest(nat.e,pn,3000)
console.error(`natural seed: birth=${seedTopo} -> rest=${topoSig(nat.w)} E=${totalEnergy(nat.e).toFixed(2)} minL=${minInternal(nat.w).toFixed(3)} ticks=${u}`)
const b0={x:-20,y:0},b1={x:20,y:0},v0={x:0,y:-6},v1={x:0,y:6}
for(const [nm,p,s0,s1] of [['01|23',[0,1,2,3],b0,b1],['02|13',[0,2,1,3],v0,v1],['03|12',[0,3,1,2],b0,b1]] as const){const {e,w}=rect4();const pin=pinAt(e,w,C);setPairing(w,p[0],p[1],p[2],p[3],C,s0,s1);recomputeRegions(e);establishFrame(e);const uu=rest(e,pin,3000);console.error(`forced ${nm}: rest=${topoSig(w)} E=${totalEnergy(e).toFixed(2)} minL=${minInternal(w).toFixed(3)} ticks=${uu}`)}
