import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import {
  mkdir,
  readFile,
  readdir,
  rm,
  stat,
  writeFile,
} from 'node:fs/promises'
import { relative, resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { chromium, type Browser, type Page } from '@playwright/test'
import { createServer, type ViteDevServer } from 'vite'

const ROOT = resolve(import.meta.dirname, '..')
const REFERENCE_PATH = '/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html'
const DEFAULT_OUTPUT = '/tmp/vpa-lambda-comparison'
const VIEWPORT = { width: 1280, height: 1024 }
const PALETTE = {
  redex: '#f06aa7',
  argument: '#f0bd55',
  copies: ['#58ddcf', '#6da8ff', '#c084fc', '#fb7185', '#34d399'],
  referenceBase: '#b8cbd2',
  lightBase: '#26343a',
  darkBase: '#5bd2de',
} as const

const POSITIVE_BOUNDARIES = [0, 0.15, 0.34, 0.54, 0.82, 0.91, 0.965, 1] as const
const DELETION_BOUNDARIES = [0, 0.15, 0.38, 0.64, 0.93, 1] as const
const EXAMPLES = [
  { key: 'one-use', source: '(\\x. x) a', copies: 1, boundaries: POSITIVE_BOUNDARIES },
  { key: 'duplication', source: '(\\f. \\x. f (f x)) (\\z. z)', copies: 2, boundaries: POSITIVE_BOUNDARIES },
  { key: 'deletion', source: '(\\x. kept) ((\\z. z) discarded)', copies: 0, boundaries: DELETION_BOUNDARIES },
  { key: 'nested-binder', source: '(\\x. \\y. x y) (\\w. w)', copies: 1, boundaries: POSITIVE_BOUNDARIES },
  { key: 'capture-avoidance', source: '(\\x. \\y. x) y', copies: 1, boundaries: POSITIVE_BOUNDARIES },
] as const
const MODES = ['reference', '2d-light', '3d-light', '3d-dark'] as const
type ModeName = (typeof MODES)[number]

type Point = readonly [number, number]
type Bounds = { readonly x: number; readonly y: number; readonly width: number; readonly height: number }
type RawStroke = {
  readonly id: string
  readonly originId: string
  readonly address: string
  readonly sourceStrokeId: string
  readonly renderRole: string
  readonly role: string
  readonly lineage: 'persistent' | 'redex' | 'argument' | 'copy'
  readonly copyIndex: number | null
  readonly color: string
  readonly a: Point
  readonly b: Point
  readonly length: number
  readonly junctionA: string
  readonly junctionB: string
  readonly destinationJunctionA: string | null
  readonly destinationJunctionB: string | null
  readonly rendererOnly: boolean
  readonly raster: StrokeRaster
}
type RawFrame = {
  readonly source: 'live-reference-transition' | 'application-2d-paint' | 'presented-webgl-entities'
  readonly baseColor: string
  readonly phase: string
  readonly copyCount: number
  readonly strokes: readonly RawStroke[]
  readonly endpointStaticError: number
}
type StrokeRaster = {
  readonly screenLength: number
  readonly matchingPixels: number
  readonly bestColorDistance: number
}
type RasterFrame = {
  readonly nonBackgroundPixels: number
  readonly paletteMatches: Readonly<Record<string, number>>
}
type ThreeDFrame = {
  readonly strokeOnly: boolean
  readonly planarFootprint: boolean
  readonly maxPlanarityError: number
  readonly maxNormalError: number
  readonly maxAttachmentGap: number
  readonly entityColorMismatches: number
  readonly bestBasePixelDistance: number
  readonly lambdaFillRatio: number
}
type TwoDFrame = {
  readonly maxAttachmentGap: number
  readonly frameHalf: number
  readonly sourceFrameHalf: number
  readonly viewScale: number
  readonly sourceScale: number
  readonly targetScale: number
  readonly copyVisibility: Readonly<Record<string, {
    readonly strokeCount: number
    readonly visibleStrokeCount: number
    readonly bounds: Bounds
  }>>
}
type BrowserMeasurement = {
  readonly raw: RawFrame
  readonly raster: RasterFrame
  readonly visualBounds: Bounds
  readonly sourceDimensions: { readonly width: number; readonly height: number }
  readonly backingDimensions: { readonly width: number; readonly height: number }
  readonly twoD?: TwoDFrame
  readonly threeD?: ThreeDFrame
}
type ReferenceLoad = {
  readonly copyCount: number
  readonly argumentStrokeAddresses: readonly string[]
  readonly argumentRootJunction: string
}
type StructuralFrame = {
  readonly copyCount: number
  readonly binderPresent: boolean
  readonly stemCount: number
  readonly argumentCount: number
  readonly argumentSpan: number
  readonly persistentTargetError: number
  readonly copyTargetError: number
  readonly endpointStaticError: number
  readonly opaque: boolean
  readonly copies: readonly {
    readonly index: number
    readonly strokeCount: number
    readonly components: number
    readonly centroid: Point
    readonly distanceToTarget: number
    readonly colors: readonly string[]
  }[]
}

const sha256 = (bytes: Uint8Array | string): string => createHash('sha256').update(bytes).digest('hex')
const round = (value: number, places = 9): number => Number(value.toFixed(places))
const normalizePhase = (phase: string): string => phase.replaceAll(' ', '-').toLowerCase()

function outputFromArgs(): string {
  const index = process.argv.indexOf('--output')
  const value = index < 0 ? DEFAULT_OUTPUT : process.argv[index + 1]
  if (value === undefined) throw new Error('--output requires a directory')
  const output = resolve(value)
  if (output === '/tmp' || !output.startsWith('/tmp/')) {
    throw new Error(`Lambda comparison output must be a dedicated directory under /tmp, got '${output}'`)
  }
  return output
}

function samplePoints(boundaries: readonly number[]): readonly {
  readonly progress: number
  readonly sample: 'boundary' | 'midpoint'
}[] {
  return boundaries.flatMap((progress, index) => index === boundaries.length - 1
    ? [{ progress, sample: 'boundary' as const }]
    : [
        { progress, sample: 'boundary' as const },
        { progress: (progress + boundaries[index + 1]!) / 2, sample: 'midpoint' as const },
      ])
}

async function sourceHash(): Promise<string> {
  const files: string[] = []
  const visit = async (directory: string): Promise<void> => {
    for (const entry of await readdir(directory, { withFileTypes: true })) {
      const path = resolve(directory, entry.name)
      if (entry.isDirectory()) await visit(path)
      else if (entry.isFile()) files.push(path)
    }
  }
  for (const directory of ['src', 'app']) await visit(resolve(ROOT, directory))
  for (const file of ['package.json', 'package-lock.json']) files.push(resolve(ROOT, file))
  const digest = createHash('sha256')
  for (const file of files.sort()) {
    digest.update(relative(ROOT, file)).update('\0').update(sha256(await readFile(file))).update('\n')
  }
  return digest.digest('hex')
}

const pointDistance = (left: Point, right: Point): number =>
  Math.hypot(left[0] - right[0], left[1] - right[1])

function pointSegmentDistance(point: Point, from: Point, to: Point): number {
  const delta: Point = [to[0] - from[0], to[1] - from[1]]
  const norm = delta[0] * delta[0] + delta[1] * delta[1]
  const amount = norm === 0 ? 0 : Math.max(0, Math.min(1,
    ((point[0] - from[0]) * delta[0] + (point[1] - from[1]) * delta[1]) / norm,
  ))
  return pointDistance(point, [from[0] + delta[0] * amount, from[1] + delta[1] * amount])
}

function maxTargetError(
  strokes: readonly RawStroke[],
  target: readonly RawStroke[],
  include: (stroke: RawStroke) => boolean,
): number {
  const targetGroups = new Map<string, RawStroke[]>()
  for (const stroke of target.filter(({ rendererOnly }) => !rendererOnly)) {
    const group = targetGroups.get(stroke.address) ?? []
    group.push(stroke)
    targetGroups.set(stroke.address, group)
  }
  const currentGroups = new Map<string, RawStroke[]>()
  for (const stroke of strokes.filter((candidate) => !candidate.rendererOnly && include(candidate))) {
    const group = currentGroups.get(stroke.address) ?? []
    group.push(stroke)
    currentGroups.set(stroke.address, group)
  }
  let maximum = 0
  for (const [address, group] of currentGroups) {
    const targetGroup = targetGroups.get(address)
    if (targetGroup === undefined) throw new Error(`semantic stroke group '${address}' has no final correspondence`)
    for (const stroke of group) for (const point of [stroke.a, stroke.b]) {
      maximum = Math.max(maximum, Math.min(...targetGroup.map((candidate) => (
        pointSegmentDistance(point, candidate.a, candidate.b)
      ))))
    }
  }
  return maximum
}

function components(strokes: readonly RawStroke[]): number {
  if (strokes.length === 0) return 0
  const parent = new Map<string, string>()
  const root = (key: string): string => {
    const current = parent.get(key)
    if (current === undefined) { parent.set(key, key); return key }
    if (current === key) return key
    const found = root(current)
    parent.set(key, found)
    return found
  }
  const union = (left: string, right: string): void => {
    const a = root(left), b = root(right)
    if (a !== b) parent.set(b, a)
  }
  const pointKey = (point: Point): string => `${point[0].toFixed(7)}:${point[1].toFixed(7)}`
  for (const stroke of strokes) union(pointKey(stroke.a), pointKey(stroke.b))
  return new Set([...parent.keys()].map(root)).size
}

function summarize(raw: RawFrame, target: RawFrame): StructuralFrame {
  const structural = raw.strokes.filter(({ rendererOnly }) => !rendererOnly)
  const targetStructural = target.strokes.filter(({ rendererOnly }) => !rendererOnly)
  const copies = Array.from({ length: raw.copyCount }, (_, index) => {
    const strokes = structural.filter((stroke) => stroke.copyIndex === index && stroke.lineage === 'copy')
    const points = strokes.flatMap((stroke) => [stroke.a, stroke.b])
    const centroid: Point = points.length === 0 ? [0, 0] : [
      points.reduce((sum, point) => sum + point[0], 0) / points.length,
      points.reduce((sum, point) => sum + point[1], 0) / points.length,
    ]
    return {
      index,
      strokeCount: strokes.length,
      components: components(strokes),
      centroid: [round(centroid[0]), round(centroid[1])] as const,
      distanceToTarget: round(maxTargetError(strokes, targetStructural, () => true)),
      colors: [...new Set(strokes.map(({ color }) => color.toLowerCase()))].sort(),
    }
  }).filter(({ strokeCount }) => strokeCount > 0)
  return {
    copyCount: raw.copyCount,
    binderPresent: structural.some((stroke) => stroke.lineage === 'redex' && stroke.role === 'lambda'),
    stemCount: structural.filter((stroke) => stroke.lineage === 'redex' && stroke.role === 'variable').length,
    argumentCount: structural.filter((stroke) => stroke.lineage === 'argument').length,
    argumentSpan: round(structural.filter((stroke) => stroke.lineage === 'argument')
      .reduce((sum, stroke) => sum + stroke.length, 0)),
    persistentTargetError: round(maxTargetError(structural, targetStructural, (stroke) => stroke.lineage === 'persistent')),
    copyTargetError: round(maxTargetError(structural, targetStructural, (stroke) => stroke.lineage === 'copy')),
    endpointStaticError: round(raw.endpointStaticError),
    opaque: structural.every(({ color }) => /^#[0-9a-f]{6}$/iu.test(color)),
    copies,
  }
}

function unionBounds(bounds: readonly Bounds[], source: { width: number; height: number }, padding: number): Bounds {
  const minX = Math.min(...bounds.map(({ x }) => x))
  const minY = Math.min(...bounds.map(({ y }) => y))
  const maxX = Math.max(...bounds.map(({ x, width }) => x + width))
  const maxY = Math.max(...bounds.map(({ y, height }) => y + height))
  const x = Math.max(0, Math.floor(minX - padding))
  const y = Math.max(0, Math.floor(minY - padding))
  return {
    x,
    y,
    width: Math.min(source.width - x, Math.ceil(maxX + padding) - x),
    height: Math.min(source.height - y, Math.ceil(maxY + padding) - y),
  }
}

const HARNESS_MODULE = String.raw`
import { DiagramBuilder } from '/src/kernel/diagram/builder.ts'
import { singleStepAction } from '/src/kernel/proof/action.ts'
import { parseTerm } from '/src/kernel/term/parse.ts'
import { stepNormalOrder } from '/src/kernel/term/reduce.ts'
import { MotionCoordinator, defaultMotionPreferences } from '/src/app/interact/motion.ts'
import { convertToWeakHeadNormal } from '/src/app/tactics.ts'
import { adaptCanvas } from '/src/view/canvas.ts'
import { fitCamera } from '/src/view/camera.ts'
import { carryOver, frameBounds, mkEngine } from '/src/view/engine.ts'
import { planBetaMotion } from '/src/view/lambda-motion.ts'
import { DARK, LIGHT, paint } from '/src/view/paint.ts'
import { seedProject, settle } from '/src/view/relax.ts'
import { renderThemeOf } from '/src/view3d/index.ts'
import { fitPose, eyeOf, FOV_DEG } from '/src/view3d/camera.ts'
import { entityColor, mountRender } from '/src/view3d/render.ts'
import { scene3 } from '/src/view3d/scene.ts'
import { planTransition, sceneAt } from '/src/view3d/transition.ts'
import { cross3, dist3, dot3, norm3, sub3 } from '/src/view3d/vec3.ts'

const palette = ['#f06aa7','#f0bd55','#58ddcf','#6da8ff','#c084fc','#fb7185','#34d399','#b8cbd2','#26343a','#5bd2de']
const canvas2 = document.querySelector('#two')
const host3 = document.querySelector('#three')
const surface2 = adaptCanvas(canvas2)
surface2.resize(900, 900)
let state = null
let currentTheme = LIGHT
let renderer3 = null

const endpoint = stroke => stroke.geometry.kind === 'arc'
  ? [
      [Math.cos(stroke.geometry.a0) * stroke.geometry.r, Math.sin(stroke.geometry.a0) * stroke.geometry.r],
      [Math.cos(stroke.geometry.a1) * stroke.geometry.r, Math.sin(stroke.geometry.a1) * stroke.geometry.r],
    ]
  : [[stroke.geometry.from.x, stroke.geometry.from.y], [stroke.geometry.to.x, stroke.geometry.to.y]]
const strokeLength = stroke => stroke.geometry.kind === 'arc'
  ? Math.abs(stroke.geometry.a1 - stroke.geometry.a0) * stroke.geometry.r
  : Math.hypot(stroke.geometry.to.x - stroke.geometry.from.x, stroke.geometry.to.y - stroke.geometry.from.y)
const rgb = hex => {
  const value = Number.parseInt(hex.slice(1), 16)
  return [value >> 16, (value >> 8) & 255, value & 255]
}
const raster = (canvas, background) => {
  const context = document.createElement('canvas').getContext('2d')
  context.canvas.width = canvas.width
  context.canvas.height = canvas.height
  context.drawImage(canvas, 0, 0)
  const data = context.getImageData(0, 0, canvas.width, canvas.height).data
  const bg = rgb(background)
  const colors = Object.fromEntries(palette.map(color => [color, { rgb: rgb(color), count: 0 }]))
  let nonBackgroundPixels = 0
  for (let index=0; index<data.length; index+=4) {
    if (data[index+3] < 8) continue
    const pixel = [data[index],data[index+1],data[index+2]]
    if (Math.hypot(pixel[0]-bg[0],pixel[1]-bg[1],pixel[2]-bg[2]) > 24) nonBackgroundPixels++
    for (const value of Object.values(colors)) {
      if (Math.hypot(pixel[0]-value.rgb[0],pixel[1]-value.rgb[1],pixel[2]-value.rgb[2]) <= 48) value.count++
    }
  }
  return { nonBackgroundPixels, paletteMatches: Object.fromEntries(Object.entries(colors).map(([key,value]) => [key,value.count])) }
}
const canonicalJunction = (junction,copyIndex) => {
  const match=/^copy:(\d+):(.*)$/.exec(junction),source=match===null?junction:match[2]
  const effective=copyIndex??(match===null?null:Number(match[1]))
  return effective===null?source:'copy:'+effective+':'+source
}
const canonicalRole = (sourceStrokeId,renderRole) => sourceStrokeId.startsWith('interface:')
  ? renderRole
  : sourceStrokeId.slice(sourceStrokeId.lastIndexOf(':')+1)
const observationAddress = (sourceStrokeId,copyIndex) => copyIndex===null
  ? sourceStrokeId
  : 'copy:'+copyIndex+':'+sourceStrokeId
const segmentDistance2 = (point,a,b) => {
  const dx=b[0]-a[0],dy=b[1]-a[1],norm=dx*dx+dy*dy
  const t=norm===0?0:Math.max(0,Math.min(1,((point[0]-a[0])*dx+(point[1]-a[1])*dy)/norm))
  return Math.hypot(point[0]-(a[0]+dx*t),point[1]-(a[1]+dy*t))
}
const authoredRaster = (canvas,screenPoints,color,tolerance) => {
  const context=document.createElement('canvas').getContext('2d')
  context.canvas.width=canvas.width;context.canvas.height=canvas.height;context.drawImage(canvas,0,0)
  const data=context.getImageData(0,0,canvas.width,canvas.height).data,target=rgb(color)
  let screenLength=0,bestColorDistance=Infinity,matchingPixels=0
  const seen=new Set()
  for(let index=1;index<screenPoints.length;index++){
    const a=screenPoints[index-1],b=screenPoints[index]
    screenLength+=Math.hypot(b[0]-a[0],b[1]-a[1])
    const x0=Math.max(0,Math.floor(Math.min(a[0],b[0])-3)),x1=Math.min(canvas.width-1,Math.ceil(Math.max(a[0],b[0])+3))
    const y0=Math.max(0,Math.floor(Math.min(a[1],b[1])-3)),y1=Math.min(canvas.height-1,Math.ceil(Math.max(a[1],b[1])+3))
    for(let y=y0;y<=y1;y++)for(let x=x0;x<=x1;x++){
      if(segmentDistance2([x+.5,y+.5],a,b)>2.75)continue
      const key=y*canvas.width+x;if(seen.has(key))continue;seen.add(key)
      const offset=key*4;if(data[offset+3]<8)continue
      const distance=Math.hypot(data[offset]-target[0],data[offset+1]-target[1],data[offset+2]-target[2])
      bestColorDistance=Math.min(bestColorDistance,distance)
      if(distance<=tolerance)matchingPixels++
    }
  }
  return {screenLength,matchingPixels,bestColorDistance}
}
const shapeBounds = (shapes, view) => {
  const points = []
  const point = p => points.push([p.x*view.scale+view.offsetX,p.y*view.scale+view.offsetY])
  for (const shape of shapes) {
    if (shape.kind === 'segment') { point(shape.from); point(shape.to) }
    if (shape.kind === 'arc') {
      if(Math.abs(shape.a1-shape.a0)<=1e-10)continue
      const angles=[shape.a0,shape.a1]
      for(let axis=0;axis<4;axis++){
        let angle=axis*Math.PI/2
        while(angle<shape.a0)angle+=Math.PI*2
        if(angle<=shape.a1+1e-10)angles.push(angle)
      }
      for(const angle of angles)point({x:shape.center.x+Math.cos(angle)*shape.r,y:shape.center.y+Math.sin(angle)*shape.r})
    }
  }
  const xs=points.map(p=>p[0]), ys=points.map(p=>p[1])
  return { x:Math.min(...xs), y:Math.min(...ys), width:Math.max(...xs)-Math.min(...xs), height:Math.max(...ys)-Math.min(...ys) }
}
const shapeError = (moving, staticShapes) => {
  if (moving.length !== staticShapes.length) return Infinity
  let error=0
  for(let index=0;index<moving.length;index++){
    const a=moving[index], b=staticShapes[index]
    if (a.kind!==b.kind) return Infinity
    if(a.kind==='arc') error=Math.max(error,Math.abs(a.center.x-b.center.x),Math.abs(a.center.y-b.center.y),Math.abs(a.r-b.r),Math.abs(a.a0-b.a0),Math.abs(a.a1-b.a1))
    else error=Math.max(error,Math.hypot(a.from.x-b.from.x,a.from.y-b.from.y),Math.hypot(a.to.x-b.to.x,a.to.y-b.to.y))
  }
  return error
}
const smoothStage = value => {const x=Math.max(0,Math.min(1,value));return x*x*(3-2*x)}
const localToIntrinsic = (point,progress) => {
  const view=state.plan.model.view,times=state.plan.times
  const space=smoothStage((progress-times.liftEnd)/(times.spaceEnd-times.liftEnd))
  const mix=(a,b)=>a+(b-a)*space
  const cols=mix(view.sourceGrid.cols,view.targetGrid.cols)
  const rows=mix(view.sourceGrid.rows,view.targetGrid.rows)
  const offset=mix(view.sourceOffset,view.targetOffset)
  let angle=Math.atan2(point[1],point[0]);if(angle<0)angle+=Math.PI*2
  const col=((angle-Math.PI/6)/(Math.PI*5/3))*cols-.5+offset
  return [col,rows+2-Math.hypot(point[0],point[1])]
}
const shapeEndpoints = shape => shape.kind==='arc'
  ? [shape.a0,shape.a1].map(angle=>[shape.center.x+Math.cos(angle)*shape.r,shape.center.y+Math.sin(angle)*shape.r])
  : [[shape.from.x,shape.from.y],[shape.to.x,shape.to.y]]
const shapeSamples = shape => shape.kind==='arc'
  ? Array.from({length:Math.max(2,Math.ceil(Math.abs(shape.a1-shape.a0)*12)+1)},(_,index)=>{
      const angle=shape.a0+(shape.a1-shape.a0)*index/(Math.max(2,Math.ceil(Math.abs(shape.a1-shape.a0)*12)+1)-1)
      return [shape.center.x+Math.cos(angle)*shape.r,shape.center.y+Math.sin(angle)*shape.r]
    })
  : shapeEndpoints(shape)
const lambdaSimilarity = (frame,shapes) => {
  if(frame.strokes.length!==shapes.length)throw Error('2D paint dropped or added a Lambda structural stroke')
  for(let index=0;index<frame.strokes.length;index++){
    const local=endpoint(frame.strokes[index]),world=shapeEndpoints(shapes[index])
    const localDelta=[local[1][0]-local[0][0],local[1][1]-local[0][1]],worldDelta=[world[1][0]-world[0][0],world[1][1]-world[0][1]]
    const localLength=Math.hypot(...localDelta),worldLength=Math.hypot(...worldDelta)
    if(localLength<1e-7||worldLength<1e-7)continue
    const scale=worldLength/localLength
    const theta=Math.atan2(worldDelta[1],worldDelta[0])-Math.atan2(localDelta[1],localDelta[0])
    const c=Math.cos(theta),s=Math.sin(theta)
    const transformed=[scale*(local[0][0]*c-local[0][1]*s),scale*(local[0][0]*s+local[0][1]*c)]
    return {scale,theta,center:[world[0][0]-transformed[0],world[0][1]-transformed[1]]}
  }
  throw Error('2D Lambda frame has no nondegenerate stroke for normalization')
}
const inverseSimilarity = (point,transform) => {
  const x=(point[0]-transform.center[0])/transform.scale,y=(point[1]-transform.center[1])/transform.scale
  const c=Math.cos(transform.theta),s=Math.sin(transform.theta)
  return [x*c+y*s,-x*s+y*c]
}
const raw2dFrame = (frame,shapes,canvas,view,progress,baseColor,endpointStaticError) => {
  const transform=lambdaSimilarity(frame,shapes)
  const origins=new Set(frame.strokes.map(stroke=>stroke.originId))
  return {
    source:'application-2d-paint',baseColor:baseColor.toLowerCase(),phase:frame.phase,
    copyCount:state.plan.copyCount,endpointStaticError,
    strokes:frame.strokes.map((stroke,index)=>{
      const shape=shapes[index],worldEndpoints=shapeEndpoints(shape)
      const localEndpoints=worldEndpoints.map(point=>inverseSimilarity(point,transform))
      const expected=endpoint(stroke)
      for(let point=0;point<2;point++)if(Math.hypot(localEndpoints[point][0]-expected[point][0],localEndpoints[point][1]-expected[point][1])>1e-7)throw Error('2D paint geometry diverged from its structural stroke')
      const screenPoints=shapeSamples(shape).map(point=>[point[0]*view.scale+view.offsetX,point[1]*view.scale+view.offsetY])
      const freeDrop=stroke.originId.endsWith(':variable')?stroke.originId.slice(0,-':variable'.length)+':free-drop':stroke.originId
      const sourceStrokeId=origins.has(freeDrop)?freeDrop:stroke.originId,rendererOnly=sourceStrokeId.startsWith('interface:')
      const [a,b]=localEndpoints.map(point=>localToIntrinsic(point,progress))
      return {
        id:'2d:'+stroke.id,originId:sourceStrokeId,address:observationAddress(sourceStrokeId,stroke.copyIndex),
        sourceStrokeId,renderRole:stroke.role,role:canonicalRole(sourceStrokeId,stroke.role),
        lineage:stroke.lineage,copyIndex:stroke.copyIndex,color:stroke.color.toLowerCase(),a,b,
        length:Math.hypot(a[0]-b[0],a[1]-b[1]),
        junctionA:canonicalJunction(stroke.points[0].junction,stroke.copyIndex),
        junctionB:canonicalJunction(stroke.points[1].junction,stroke.copyIndex),
        destinationJunctionA:stroke.points[0].destinationJunction===null?null:canonicalJunction(stroke.points[0].destinationJunction,stroke.copyIndex),
        destinationJunctionB:stroke.points[1].destinationJunction===null?null:canonicalJunction(stroke.points[1].destinationJunction,stroke.copyIndex),
        rendererOnly,raster:authoredRaster(canvas,screenPoints,stroke.color,48),
      }
    }),
  }
}
const project = (point, pose, width, height) => {
  const eye=eyeOf(pose), fwd=norm3(sub3(pose.target,eye)), right=norm3(cross3(fwd,{x:0,y:1,z:0})), up=cross3(right,fwd)
  const d=sub3(point,eye), z=dot3(d,fwd), tanHalf=Math.tan(FOV_DEG*Math.PI/360), aspect=width/height
  return [((dot3(d,right)/z/(tanHalf*aspect))+1)/2*width,(1-dot3(d,up)/z/tanHalf)/2*height]
}
const threeMetrics = (presented, theme, pose, canvas) => {
  const lambdas=presented.entities.filter(entity=>entity.kind==='lambda')
  const branches=new Map(presented.entities.filter(entity=>entity.kind==='branch').map(entity=>[entity.key.slice(2),entity]))
  let maxPlanarityError=0,maxNormalError=0,maxAttachmentGap=0,entityColorMismatches=0
  const strandEnds=presented.entities.filter(entity=>entity.kind==='strand').flatMap(entity=>[entity.pts[0],entity.pts.at(-1)])
  for(const stroke of lambdas){
    const branch=branches.get(stroke.region), tangent=norm3(sub3(branch.pts.at(-1),branch.pts[0]))
    maxNormalError=Math.max(maxNormalError,1-Math.abs(dot3(tangent,stroke.plane.normal)))
    for(const p of stroke.pts) maxPlanarityError=Math.max(maxPlanarityError,Math.abs(dot3(sub3(p,stroke.center),stroke.plane.normal)))
    const expected=stroke.color??theme.baseWire
    if(entityColor(stroke,theme).toLowerCase()!==expected.toLowerCase()) entityColorMismatches++
    if(stroke.strokeId==='interface:output:line'||/^interface:free:\d+:port-stem$/.test(stroke.strokeId)){
      const anchor=stroke.pts.at(-1)
      maxAttachmentGap=Math.max(maxAttachmentGap,Math.min(...strandEnds.map(point=>dist3(anchor,point))))
    }
  }
  const projected=lambdas.flatMap(entity=>entity.pts.map(point=>project(point,pose,900,900)))
  const xs=projected.map(p=>p[0]),ys=projected.map(p=>p[1])
  const visualBounds={x:Math.min(...xs),y:Math.min(...ys),width:Math.max(...xs)-Math.min(...xs),height:Math.max(...ys)-Math.min(...ys)}
  const context=document.createElement('canvas').getContext('2d');context.canvas.width=canvas.width;context.canvas.height=canvas.height;context.drawImage(canvas,0,0)
  const data=context.getImageData(0,0,canvas.width,canvas.height).data,bg=rgb(theme.background),base=rgb(theme.baseWire)
  const x0=Math.max(0,Math.floor(visualBounds.x)),y0=Math.max(0,Math.floor(visualBounds.y)),x1=Math.min(canvas.width-1,Math.ceil(visualBounds.x+visualBounds.width)),y1=Math.min(canvas.height-1,Math.ceil(visualBounds.y+visualBounds.height))
  const authored=[...new Set(lambdas.map(entity=>rgb(entityColor(entity,theme))))]
  let colored=0,total=0,bestBasePixelDistance=Infinity
  for(let y=y0;y<=y1;y++)for(let x=x0;x<=x1;x++){const i=(y*canvas.width+x)*4,p=[data[i],data[i+1],data[i+2]],fromBg=Math.hypot(p[0]-bg[0],p[1]-bg[1],p[2]-bg[2]);total++;if(fromBg>30&&Math.min(...authored.map(color=>Math.hypot(p[0]-color[0],p[1]-color[1],p[2]-color[2])))<=72)colored++;if(fromBg>30)bestBasePixelDistance=Math.min(bestBasePixelDistance,Math.hypot(p[0]-base[0],p[1]-base[1],p[2]-base[2]))}
  const planarFootprint=lambdas.some(entity=>entity.pts.length>4&&visualBounds.width>8&&visualBounds.height>8)
  return { strokeOnly:lambdas.length>0&&lambdas.every(entity=>!('fill'in entity)&&entity.pts.length>=2),planarFootprint,maxPlanarityError,maxNormalError,maxAttachmentGap,entityColorMismatches,bestBasePixelDistance,lambdaFillRatio:total===0?1:colored/total,visualBounds }
}
const raw3dFrame = (presented,theme,pose,canvas,progress,endpointStaticError) => {
  const entities=presented.entities.filter(entity=>entity.kind==='lambda')
  const origins=new Set(entities.map(entity=>entity.sourceStrokeId))
  const phase=entities.find(entity=>entity.phase!==null)?.phase
  if(phase===undefined)throw Error('presented WebGL Lambda entities lost their structural phase')
  return {
    source:'presented-webgl-entities',baseColor:theme.baseWire.toLowerCase(),phase,
    copyCount:state.plan.copyCount,endpointStaticError,
    strokes:entities.map(entity=>{
      if(entity.lineage===null||entity.junctions===null)throw Error('presented WebGL Lambda entity lost structural provenance')
      const local=point=>{
        const delta=sub3(point,entity.center)
        return [dot3(delta,entity.plane.right)/entity.scale,dot3(delta,entity.plane.up)/entity.scale]
      }
      const localPoints=entity.pts.map(local),a=localToIntrinsic(localPoints[0],progress),b=localToIntrinsic(localPoints.at(-1),progress)
      const freeDrop=entity.sourceStrokeId.endsWith(':variable')?entity.sourceStrokeId.slice(0,-':variable'.length)+':free-drop':entity.sourceStrokeId
      const sourceStrokeId=origins.has(freeDrop)?freeDrop:entity.sourceStrokeId,rendererOnly=sourceStrokeId.startsWith('interface:')||entity.strokeId.startsWith('socket:')
      const color=entityColor(entity,theme).toLowerCase()
      const destinations=entity.destinationJunctions
      return {
        id:'3d:'+entity.strokeId,originId:sourceStrokeId,address:observationAddress(sourceStrokeId,entity.copyIndex),
        sourceStrokeId,renderRole:entity.role,role:canonicalRole(sourceStrokeId,entity.role),
        lineage:entity.lineage,copyIndex:entity.copyIndex,color,a,b,
        length:Math.hypot(a[0]-b[0],a[1]-b[1]),
        junctionA:canonicalJunction(entity.junctions[0],entity.copyIndex),
        junctionB:canonicalJunction(entity.junctions[1],entity.copyIndex),rendererOnly,
        destinationJunctionA:destinations===null||destinations[0]===null?null:canonicalJunction(destinations[0],entity.copyIndex),
        destinationJunctionB:destinations===null||destinations[1]===null?null:canonicalJunction(destinations[1],entity.copyIndex),
        raster:authoredRaster(canvas,entity.pts.map(point=>project(point,pose,900,900)),color,72),
      }
    }),
  }
}

async function load(source){
  const parsed=parseTerm(source),reduced=stepNormalOrder(parsed.term)
  if(reduced===null)throw Error('comparison source has no first beta step')
  const step={kind:'beta',path:reduced.path}
  const plan=planBetaMotion(parsed.term,step,parsed.freeIdentifiers.length)
  const builder=new DiagramBuilder(),node=builder.term(builder.root,parsed.term,parsed.freeIdentifiers.length)
  const sourceBuilt={diagram:builder.build(),node}
  const conversion=convertToWeakHeadNormal(sourceBuilt.diagram,node,1)
  const targetBuilt={diagram:conversion.diagram,node}
  const sourceEngine=mkEngine(sourceBuilt.diagram,[]);seedProject(sourceEngine);settle(sourceEngine,4000)
  const engine=mkEngine(targetBuilt.diagram,[])
  const carried=carryOver(sourceEngine,engine)
  seedProject(engine,false,carried);settle(engine,4000)
  const frame=frameBounds(engine);if(frame===null)throw Error('comparison target engine did not establish a frame')
  const view=fitCamera({center:frame.center,radius:frame.frameR},900,900,1)
  currentTheme=LIGHT
  const coordinator=new MotionCoordinator({preferences:()=>defaultMotionPreferences(false),engine:()=>engine,theme:()=>currentTheme})
  coordinator.observeSwap(sourceEngine,engine,0,singleStepAction('beta',conversion.step))
  const sourceScene=scene3(sourceBuilt.diagram),targetScene=scene3(targetBuilt.diagram)
  state={parsed,step,plan,node:sourceBuilt.node,sourceBuilt,targetBuilt,sourceEngine,engine,view,coordinator,sourceScene,targetScene,tween:null,pose:null,finalByTheme:new Map()}
  if(renderer3!==null){renderer3.dispose();renderer3=null}
  host3.replaceChildren()
  return{copyCount:plan.copyCount,times:plan.times}
}

function set2d(progress,themeName='light'){
  host3.style.display='none';canvas2.style.display='block'
  currentTheme=themeName==='dark'?DARK:LIGHT
  const frame=state.coordinator.scrubBeta(progress)
  const shapes=state.coordinator.paint(0)
  surface2.render({background:currentTheme.canvas,layers:[{shapes}]},state.view)
  const moving=shapes.filter(shape=>shape.kind==='arc'||shape.kind==='segment')
  const wireEnds=shapes.filter(shape=>shape.kind==='bezierPath').flatMap(shape=>[shape.cubics[0].a,shape.cubics.at(-1).b])
  const incident=new Set([...state.engine.wires.values()].flatMap(wire=>wire.binds.filter(bind=>bind.body===state.node).map(bind=>bind.key)))
  let maxAttachmentGap=0
  frame.strokes.forEach((stroke,index)=>{
    const key=stroke.id==='interface:output:line'?'out':/^interface:free:(\d+):port-stem$/.exec(stroke.id)?.[1]
    const portKey=key===undefined?undefined:key==='out'?key:'f:'+key
    if(portKey===undefined||!incident.has(portKey))return
    const shape=moving[index]
    if(shape?.kind!=='segment')throw Error('moving Lambda interface port did not paint as a segment')
    maxAttachmentGap=Math.max(maxAttachmentGap,Math.min(...wireEnds.map(point=>Math.hypot(point.x-shape.to.x,point.y-shape.to.y))))
  })
  const copyVisibility={}
  frame.strokes.forEach((stroke,index)=>{
    if(stroke.lineage!=='copy')return
    const shape=moving[index]
    if(shape.kind==='arc'&&Math.abs(shape.a1-shape.a0)<=1e-10)return
    const points=shape.kind==='arc'
      ? [shape.a0,shape.a1].map(angle=>({x:shape.center.x+Math.cos(angle)*shape.r,y:shape.center.y+Math.sin(angle)*shape.r}))
      : [shape.from,shape.to]
    const screen=points.map(point=>({x:point.x*state.view.scale+state.view.offsetX,y:point.y*state.view.scale+state.view.offsetY}))
    const x0=Math.min(...screen.map(point=>point.x)),y0=Math.min(...screen.map(point=>point.y)),x1=Math.max(...screen.map(point=>point.x)),y1=Math.max(...screen.map(point=>point.y))
    const value=copyVisibility[stroke.color]??{strokeCount:0,visibleStrokeCount:0,minX:Infinity,minY:Infinity,maxX:-Infinity,maxY:-Infinity}
    value.strokeCount++
    if(x1>=0&&x0<=900&&y1>=0&&y0<=900)value.visibleStrokeCount++
    value.minX=Math.min(value.minX,x0);value.minY=Math.min(value.minY,y0);value.maxX=Math.max(value.maxX,x1);value.maxY=Math.max(value.maxY,y1)
    copyVisibility[stroke.color]=value
  })
  const normalizedVisibility=Object.fromEntries(Object.entries(copyVisibility).map(([color,value])=>[color,{strokeCount:value.strokeCount,visibleStrokeCount:value.visibleStrokeCount,bounds:{x:value.minX,y:value.minY,width:value.maxX-value.minX,height:value.maxY-value.minY}}]))
  const staticShapes=paint(state.engine,currentTheme).filter(shape=>shape.kind==='arc'||shape.kind==='segment')
  const endpointStaticError=progress===1?shapeError(moving,staticShapes):0
  return{raw:raw2dFrame(frame,moving,canvas2,state.view,progress,currentTheme.wire,endpointStaticError),raster:raster(canvas2,currentTheme.canvas),visualBounds:shapeBounds(moving,state.view),sourceDimensions:{width:900,height:900},backingDimensions:{width:canvas2.width,height:canvas2.height},twoD:{maxAttachmentGap,frameHalf:state.engine.frame.half,sourceFrameHalf:state.sourceEngine.frame.half,viewScale:state.view.scale,sourceScale:state.sourceEngine.scale,targetScale:state.engine.scale,copyVisibility:normalizedVisibility}}
}

function set3d(progress,themeName='light'){
  canvas2.style.display='none';host3.style.display='block'
  currentTheme=themeName==='dark'?DARK:LIGHT
  const theme=renderThemeOf(currentTheme,state.targetBuilt.diagram)
  state.tween=planTransition(state.sourceScene,state.targetScene,currentTheme.wire)
  const presented=sceneAt(state.tween,progress)
  const center=state.tween.toBounds.center,radius=Math.max(state.tween.fromBounds.radius,state.tween.toBounds.radius)*1.12
  state.pose=fitPose(center,radius,1)
  if(renderer3===null){renderer3=mountRender(host3,theme);renderer3.resize(900,900)}else renderer3.setTheme(theme)
  renderer3.setEntities(presented.entities);renderer3.setPose(state.pose);renderer3.render()
  const canvas=host3.querySelector('canvas')
  const metrics=threeMetrics(presented,theme,state.pose,canvas)
  const targetLambdas=state.targetScene.entities.filter(entity=>entity.kind==='lambda')
  const movingLambdas=presented.entities.filter(entity=>entity.kind==='lambda')
  let endpointStaticError=0
  if(progress===1){
    const movingPoints=movingLambdas.flatMap(entity=>entity.pts),targetPoints=targetLambdas.flatMap(entity=>entity.pts)
    const directed=(from,to)=>Math.max(...from.map(point=>Math.min(...to.map(candidate=>dist3(point,candidate)))))
    endpointStaticError=Math.max(directed(movingPoints,targetPoints),directed(targetPoints,movingPoints))
  }
  const {visualBounds,...threeD}=metrics
  return{raw:raw3dFrame(presented,theme,state.pose,canvas,progress,endpointStaticError),raster:raster(canvas,currentTheme.canvas),visualBounds,sourceDimensions:{width:900,height:900},backingDimensions:{width:canvas.width,height:canvas.height},threeD}
}

window.__lambdaComparison={load,set2d,set3d}
`

async function startHarnessServer(): Promise<{ server: ViteDevServer; url: string }> {
  const server = await createServer({
    root: ROOT,
    logLevel: 'error',
    server: { host: '127.0.0.1', port: 0 },
    plugins: [{
      name: 'lambda-comparison-harness',
      configureServer(dev) {
        dev.middlewares.use('/__lambda_comparison__.html', (_request, response) => {
          response.statusCode = 200
          response.setHeader('Content-Type', 'text/html')
          response.end('<!doctype html><html><head><style>html,body{margin:0;width:100%;height:100%;overflow:hidden}canvas{display:block}#two,#three{position:absolute;left:0;top:0;width:900px;height:900px}#three{background:#000}</style></head><body><canvas id="two" width="900" height="900"></canvas><div id="three"></div><script type="module" src="/@lambda-comparison"></script></body></html>')
        })
      },
      resolveId(id) { return id === '/@lambda-comparison' ? '\0lambda-comparison.ts' : null },
      load(id) { return id === '\0lambda-comparison.ts' ? HARNESS_MODULE : null },
    }],
  })
  await server.listen()
  const address = server.httpServer?.address()
  if (address === null || address === undefined || typeof address === 'string') {
    await server.close()
    throw new Error('Vite did not expose a TCP address for the Lambda comparison harness')
  }
  return { server, url: `http://127.0.0.1:${address.port}/__lambda_comparison__.html` }
}

async function referenceLoad(page: Page, source: string): Promise<ReferenceLoad> {
  return page.evaluate((value) => {
    const win = window as unknown as {
      __lambdaDemo: {
        setPosition(value: number): void
        sequence: {
          terms: readonly Record<string, unknown>[]
          models: readonly { lines: readonly Record<string, unknown>[]; points: Map<string, Record<string, unknown>>; nodeOut: Map<string, string> }[]
          plans: readonly { copyCount: number; argumentId: string; argumentNodeIds: Set<string> }[]
        }
      }
    }
    const input = document.querySelector('#input')
    const load = document.querySelector('#load')
    if (!(input instanceof HTMLTextAreaElement) || !(load instanceof HTMLButtonElement)) {
      throw new Error('corrected Lambda demo controls are unavailable')
    }
    input.value = value
    load.click()
    const plan = win.__lambdaDemo.sequence.plans[0]
    if (plan === undefined) throw new Error('corrected Lambda demo produced no first beta step')
    const sourceTerm = win.__lambdaDemo.sequence.terms[0]!
    const sourceModel = win.__lambdaDemo.sequence.models[0]!
    const paths = new Map<string, string>()
    const visit = (node: Record<string, unknown>, path: string): void => {
      paths.set(String(node['id']), path)
      if (node['kind'] === 'lam') visit(node['body'] as Record<string, unknown>, `${path}/body`)
      if (node['kind'] === 'app') {
        visit(node['fn'] as Record<string, unknown>, `${path}/fn`)
        visit(node['arg'] as Record<string, unknown>, `${path}/argument`)
      }
    }
    visit(sourceTerm, 'root')
    const roleOf = (line: Record<string, unknown>): string => {
      const node = (() => {
        const id = String(line['originSourceId'] ?? line['ownerId'] ?? '')
        const find = (value: Record<string, unknown>): Record<string, unknown> | null => {
          if (String(value['id']) === id) return value
          if (value['kind'] === 'lam') return find(value['body'] as Record<string, unknown>)
          if (value['kind'] === 'app') return find(value['fn'] as Record<string, unknown>) ?? find(value['arg'] as Record<string, unknown>)
          return null
        }
        return find(sourceTerm)
      })()
      if (line['role'] === 'arg-connector') return 'argument-connector'
      return line['role'] === 'variable' && node?.['kind'] === 'var' && node['binding'] === null
        ? 'free-drop'
        : String(line['role'])
    }
    const addressOf = (line: Record<string, unknown>): string => {
      const sourceId = String(line['originSourceId'] ?? line['ownerId'])
      const path = paths.get(sourceId)
      if (path === undefined) throw new Error(`reference stroke ${String(line['id'])} has no semantic source path`)
      return `${path}:${roleOf(line)}`
    }
    const argumentStrokeAddresses = sourceModel.lines
      .filter((line) => plan.argumentNodeIds.has(String(line['ownerId'])))
      .map(addressOf)
      .sort()
    const rootPointId = sourceModel.nodeOut.get(plan.argumentId)
    const rootPoint = rootPointId === undefined ? undefined : sourceModel.points.get(rootPointId)
    const rootOwner = rootPoint === undefined ? undefined : paths.get(String(rootPoint['ownerId']))
    if (rootPoint === undefined || rootOwner === undefined) throw new Error('reference argument has no correspondence root')
    return {
      copyCount: plan.copyCount,
      argumentStrokeAddresses,
      argumentRootJunction: `${rootOwner}:out`,
    }
  }, source)
}

async function referenceMeasure(page: Page, progress: number): Promise<BrowserMeasurement> {
  return page.evaluate((value) => {
    const palette = ['#f06aa7', '#f0bd55', '#58ddcf', '#6da8ff', '#c084fc', '#fb7185', '#34d399', '#b8cbd2', '#26343a', '#5bd2de']
    const win = window as unknown as {
      __lambdaDemo: {
        setPosition(value: number): void
        sequence: {
          terms: readonly Record<string, unknown>[]
          models: readonly {
            points: Map<string, Record<string, unknown>>
            lines: readonly Record<string, unknown>[]
          }[]
          plans: readonly {
            copyCount: number
            lambdaId: string
            redexId: string
            argumentNodeIds: Set<string>
            occurrences: readonly { sourceVarId: string }[]
          }[]
          view: { minCol: number; maxCol: number; minRow: number; maxRow: number }
          transitions: readonly {
            phase(value: number): string
            draw(painter: unknown, value: number): void
          }[]
        }
      }
    }
    win.__lambdaDemo.setPosition(value)
    const canvas = document.querySelector('#canvas')
    if (!(canvas instanceof HTMLCanvasElement)) throw new Error('corrected Lambda demo canvas is unavailable')
    const plan = win.__lambdaDemo.sequence.plans[0]!
    const transition = win.__lambdaDemo.sequence.transitions[0]!
    const sourceTerm = win.__lambdaDemo.sequence.terms[0]!
    const [sourceModel, targetModel] = win.__lambdaDemo.sequence.models
    const paths = new Map<string, string>(), sourceNodes = new Map<string, Record<string, unknown>>()
    const visit = (node: Record<string, unknown>, path: string): void => {
      const id = String(node['id']); paths.set(id, path); sourceNodes.set(id, node)
      if (node['kind'] === 'lam') visit(node['body'] as Record<string, unknown>, `${path}/body`)
      if (node['kind'] === 'app') {
        visit(node['fn'] as Record<string, unknown>, `${path}/fn`)
        visit(node['arg'] as Record<string, unknown>, `${path}/argument`)
      }
    }
    visit(sourceTerm, 'root')
    const sourceIdOf = (record: Record<string, unknown>): string => String(record['originSourceId'] ?? record['ownerId'] ?? '')
    const roleOf = (line: Record<string, unknown>): string => {
      const sourceNode = sourceNodes.get(sourceIdOf(line))
      if (line['role'] === 'arg-connector') return 'argument-connector'
      return line['role'] === 'variable' && sourceNode?.['kind'] === 'var' && sourceNode['binding'] === null
        ? 'free-drop'
        : String(line['role'])
    }
    const sourceStrokeIdOf = (line: Record<string, unknown>): string => {
      const path = paths.get(sourceIdOf(line))
      if (path === undefined) throw new Error(`reference stroke ${String(line['id'])} has no semantic source path`)
      return `${path}:${roleOf(line)}`
    }
    const pointIdentity = (pointId: string, line: Record<string, unknown>, copyIndex: number | null): string => {
      const point = sourceModel!.points.get(pointId) ?? targetModel!.points.get(pointId)
      if (point === undefined) throw new Error(`reference line ${String(line['id'])} has missing junction ${pointId}`)
      const sourceId = sourceIdOf(point), path = paths.get(sourceId), node = sourceNodes.get(sourceId)
      if (path === undefined || node === undefined) throw new Error(`reference junction ${pointId} has no semantic source path`)
      const pointRole = String(point['role'])
      let suffix = pointRole
      if (pointRole === 'bind' && node['kind'] === 'var' && node['binding'] === null) suffix = 'free-rail'
      if ((pointRole === 'left' || pointRole === 'right') && node['kind'] === 'lam') suffix = `lambda:${pointRole}`
      if (pointRole === 'left' && node['kind'] === 'app') suffix = 'out'
      if (pointRole === 'right' && node['kind'] === 'app') suffix = 'application:right'
      const identity = `${path}:${suffix}`
      const pointCopyIndex = typeof point['copyIndex'] === 'number' ? point['copyIndex'] : copyIndex
      return pointCopyIndex === null ? identity : `copy:${pointCopyIndex}:${identity}`
    }
    const rawLines: Array<RawStroke & { screenPoints: readonly Point[] }> = []
    const occurrenceIds = new Set(plan.occurrences.map(({ sourceVarId }) => sourceVarId))
    const painter = {
      disc() {}, output() {}, socket() {}, label() {},
      line(line: Record<string, unknown>, a: { col: number; row: number }, b: { col: number; row: number }, frame: { minCol: number; maxCol: number; minRow: number; maxRow: number }, style: { color?: string } = {}) {
        const copyIndex = typeof line['copyIndex'] === 'number' ? line['copyIndex'] : null
        const owner = String(line['ownerId'] ?? '')
        const lineage: RawStroke['lineage'] = copyIndex !== null ? 'copy'
          : plan.argumentNodeIds.has(owner) ? 'argument'
            : owner === plan.lambdaId || owner === plan.redexId || occurrenceIds.has(owner) ? 'redex'
              : 'persistent'
        const pa: Point = [a.col - 2, a.row], pb: Point = [b.col - 2, b.row]
        const sourceStrokeId = sourceStrokeIdOf(line)
        const targetLine = targetModel!.lines.find((candidate) => candidate['key'] === line['key'])
        const destinationJunction = (endpoint: 'a' | 'b'): string | null => targetLine === undefined
          ? null
          : pointIdentity(String(targetLine[endpoint]), targetLine, copyIndex)
        const mapGrid = (point: { col: number; row: number }): Point => {
          const width = Math.max(1, frame.maxCol - frame.minCol + 1)
          const angle = Math.PI / 6 + ((point.col - frame.minCol + 0.5) / width) * Math.PI * 5 / 3
          const rows = Math.max(1, frame.maxRow - frame.minRow)
          const radius = 1.02 - ((point.row - frame.minRow) / rows) * 0.8
          const scale = Math.min(canvas.width, canvas.height) * 0.355
          return [canvas.width * 0.53 + Math.cos(angle) * radius * scale, canvas.height * 0.49 + Math.sin(angle) * radius * scale]
        }
        const horizontal = line['kind'] === 'h' || line['kind'] === 'tick'
        let screenPoints: Point[]
        if (horizontal) {
          let from = a.col, to = b.col
          if (line['role'] === 'lambda') { from -= 0.25; to += 0.25 }
          else if (line['kind'] === 'tick') { const middle = (from + to) / 2; from = middle - 0.25; to = middle + 0.25 }
          const count = Math.max(2, Math.ceil(Math.abs(to - from) * 12) + 1)
          screenPoints = Array.from({ length: count }, (_, index) => mapGrid({ col: from + (to - from) * index / (count - 1), row: a.row }))
        } else screenPoints = [mapGrid(a), mapGrid(b)]
        rawLines.push({
          id: `reference:${String(line['id'])}`, originId: sourceStrokeId,
          address: copyIndex === null ? sourceStrokeId : `copy:${copyIndex}:${sourceStrokeId}`,
          sourceStrokeId, renderRole: String(line['role']), role: roleOf(line), lineage, copyIndex,
          color: String(style.color ?? '#b8cbd2').toLowerCase(), a: pa, b: pb,
          length: Math.hypot(pa[0] - pb[0], pa[1] - pb[1]),
          junctionA: pointIdentity(String(line['a']), line, copyIndex),
          junctionB: pointIdentity(String(line['b']), line, copyIndex),
          destinationJunctionA: destinationJunction('a'),
          destinationJunctionB: destinationJunction('b'),
          rendererOnly: false,
          raster: { screenLength: 0, matchingPixels: 0, bestColorDistance: Infinity },
          screenPoints,
        })
      },
    }
    transition.draw(painter, value)
    const context = canvas.getContext('2d')!
    const data = context.getImageData(0, 0, canvas.width, canvas.height).data
    const rgb = (hex: string): readonly number[] => { const number = Number.parseInt(hex.slice(1), 16); return [number >> 16, (number >> 8) & 255, number & 255] }
    const colors = Object.fromEntries(palette.map((color) => [color, { rgb: rgb(color), count: 0 }]))
    let nonBackgroundPixels = 0, minX = canvas.width, minY = canvas.height, maxX = 0, maxY = 0
    for (let index = 0; index < data.length; index += 4) {
      if (data[index + 3]! < 8) continue
      const pixel = [data[index]!, data[index + 1]!, data[index + 2]!]
      const at = index / 4, x = at % canvas.width, y = Math.floor(at / canvas.width)
      minX = Math.min(minX, x); minY = Math.min(minY, y); maxX = Math.max(maxX, x); maxY = Math.max(maxY, y)
      nonBackgroundPixels += 1
      for (const candidate of Object.values(colors)) {
        if (Math.hypot(pixel[0]! - candidate.rgb[0]!, pixel[1]! - candidate.rgb[1]!, pixel[2]! - candidate.rgb[2]!) <= 48) candidate.count += 1
      }
    }
    if (nonBackgroundPixels === 0) throw new Error('corrected Lambda demo produced an empty canvas')
    const distanceToSegment = (point: Point, a: Point, b: Point): number => {
      const dx = b[0] - a[0], dy = b[1] - a[1], norm = dx * dx + dy * dy
      const amount = norm === 0 ? 0 : Math.max(0, Math.min(1, ((point[0] - a[0]) * dx + (point[1] - a[1]) * dy) / norm))
      return Math.hypot(point[0] - (a[0] + dx * amount), point[1] - (a[1] + dy * amount))
    }
    const observedLines: RawStroke[] = rawLines.map(({ screenPoints, ...line }) => {
      const target = rgb(line.color), seen = new Set<number>()
      let screenLength = 0, matchingPixels = 0, bestColorDistance = Infinity
      for (let part = 1; part < screenPoints.length; part += 1) {
        const a = screenPoints[part - 1]!, b = screenPoints[part]!
        screenLength += Math.hypot(b[0] - a[0], b[1] - a[1])
        const x0 = Math.max(0, Math.floor(Math.min(a[0], b[0]) - 3)), x1 = Math.min(canvas.width - 1, Math.ceil(Math.max(a[0], b[0]) + 3))
        const y0 = Math.max(0, Math.floor(Math.min(a[1], b[1]) - 3)), y1 = Math.min(canvas.height - 1, Math.ceil(Math.max(a[1], b[1]) + 3))
        for (let y = y0; y <= y1; y += 1) for (let x = x0; x <= x1; x += 1) {
          if (distanceToSegment([x + 0.5, y + 0.5], a, b) > 2.75) continue
          const pixel = y * canvas.width + x
          if (seen.has(pixel)) continue
          seen.add(pixel)
          const offset = pixel * 4
          if (data[offset + 3]! < 8) continue
          const distance = Math.hypot(data[offset]! - target[0]!, data[offset + 1]! - target[1]!, data[offset + 2]! - target[2]!)
          bestColorDistance = Math.min(bestColorDistance, distance)
          if (distance <= 48) matchingPixels += 1
        }
      }
      return { ...line, raster: { screenLength, matchingPixels, bestColorDistance } }
    })
    const rect = canvas.getBoundingClientRect()
    return {
      raw: {
        source: 'live-reference-transition', baseColor: '#b8cbd2',
        phase: transition.phase(value).replaceAll(' ', '-'), copyCount: plan.copyCount,
        strokes: observedLines, endpointStaticError: 0,
      },
      raster: { nonBackgroundPixels, paletteMatches: Object.fromEntries(Object.entries(colors).map(([key, candidate]) => [key, candidate.count])) },
      visualBounds: { x: minX * rect.width / canvas.width, y: minY * rect.height / canvas.height, width: (maxX - minX + 1) * rect.width / canvas.width, height: (maxY - minY + 1) * rect.height / canvas.height },
      sourceDimensions: { width: rect.width, height: rect.height },
      backingDimensions: { width: canvas.width, height: canvas.height },
    }
  }, progress) as Promise<BrowserMeasurement>
}

async function validateReferenceSchedule(page: Page, boundaries: readonly number[], copies: number): Promise<void> {
  const probes = await page.evaluate(({ values, copies: count }) => {
    const demo = (window as unknown as { __lambdaDemo: { sequence: {
      plans: readonly { occurrences: readonly { sourceVarId: string }[] }[]
      transitions: readonly { phase(value: number): string; draw(painter: unknown, value: number): void }[]
    } } }).__lambdaDemo
    const transition = demo.sequence.transitions[0]!
    const occurrences = new Set(demo.sequence.plans[0]!.occurrences.map(({ sourceVarId }) => sourceVarId))
    const inspect = (progress: number) => {
      const lines: { role: string; ownerId: string }[] = []
      transition.draw({ disc() {}, output() {}, socket() {}, label() {}, line(line: { role: string; ownerId: string }) { lines.push(line) } }, progress)
      return {
        phase: transition.phase(progress).replaceAll(' ', '-'),
        lambda: lines.filter(({ role }) => role === 'lambda').length,
        variable: lines.filter(({ role, ownerId }) => role === 'variable' && occurrences.has(ownerId)).length,
      }
    }
    return values.map((boundary) => ({
      boundary,
      before: inspect(Math.max(0, boundary - 0.002)),
      at: inspect(boundary),
      after: inspect(Math.min(1, boundary + 0.002)),
      copies: count,
    }))
  }, { values: boundaries, copies })
  const phases = copies === 0
    ? ['identify', 'discard', 'make-space', 'cleanup', 'settle']
    : ['identify', 'duplicate', 'make-space', 'substitute', 'cleanup', 'settle']
  const phaseBoundaries = copies === 0 ? boundaries.slice(1, -1) : [boundaries[1]!, boundaries[2]!, boundaries[3]!, boundaries[4]!, boundaries[6]!]
  for (const [index, boundary] of phaseBoundaries.entries()) {
    const probe = probes.find((candidate) => candidate.boundary === boundary)!
    if (probe.before.phase !== phases[index] || probe.after.phase !== phases[index + 1]) {
      throw new Error(`corrected reference phase boundary ${boundary} disagrees: ${probe.before.phase} -> ${probe.after.phase}`)
    }
  }
  if (copies > 0) {
    const stem = probes.find(({ boundary }) => boundary === boundaries[5])!
    if (stem.before.variable <= stem.after.variable || stem.at.lambda === 0) {
      throw new Error(`corrected reference stem boundary ${boundaries[5]} disagrees with the required cleanup order: ${JSON.stringify(stem)}`)
    }
  }
}

async function appMeasure(page: Page, mode: Exclude<ModeName, 'reference'>, progress: number): Promise<BrowserMeasurement> {
  return page.evaluate(({ mode: selected, progress: value }) => {
    const api = (window as unknown as { __lambdaComparison: { set2d(progress: number, theme: string): unknown; set3d(progress: number, theme: string): unknown } }).__lambdaComparison
    const theme = selected.endsWith('dark') ? 'dark' : 'light'
    return selected.startsWith('2d') ? api.set2d(value, theme) : api.set3d(value, theme)
  }, { mode, progress }) as Promise<BrowserMeasurement>
}

async function appLoad(page: Page, source: string): Promise<{ copyCount: number; times: Record<string, number> }> {
  return page.evaluate((value) => (window as unknown as { __lambdaComparison: { load(source: string): unknown } }).__lambdaComparison.load(value), source) as Promise<{ copyCount: number; times: Record<string, number> }>
}

async function screenshotCanvas(page: Page, selector: string, crop: Bounds, path: string): Promise<void> {
  const box = await page.locator(selector).boundingBox()
  if (box === null) throw new Error(`${selector} has no screenshot bounds`)
  await page.screenshot({
    path,
    clip: {
      x: box.x + crop.x,
      y: box.y + crop.y,
      width: crop.width,
      height: crop.height,
    },
  })
}

function escapeHtml(value: string): string {
  return value.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;')
}

async function contactSheet(
  page: Page,
  title: string,
  frames: readonly { image: string; progress: number; phase: string }[],
  output: string,
): Promise<void> {
  const columns = 5
  const cellWidth = 214, cellHeight = 242
  const rows = Math.ceil(frames.length / columns)
  await page.setViewportSize({ width: columns * cellWidth + 24, height: rows * cellHeight + 58 })
  const cells = await Promise.all(frames.map(async (frame) => {
    const data = (await readFile(frame.image)).toString('base64')
    return `<figure><img src="data:image/png;base64,${data}"><figcaption>${frame.progress.toFixed(4)} · ${escapeHtml(frame.phase)}</figcaption></figure>`
  }))
  await page.setContent(`<!doctype html><style>html,body{margin:0;background:#111820;color:#e8edf2;font:12px system-ui}h1{font-size:18px;margin:12px}.grid{display:grid;grid-template-columns:repeat(${columns},${cellWidth}px);gap:0 0;padding:0 12px 12px}figure{margin:0;padding:5px;border:1px solid #33414d;background:#19232c;height:${cellHeight - 12}px;box-sizing:border-box}img{width:202px;height:202px;object-fit:contain;background:#0b1015}figcaption{text-align:center;margin-top:5px;white-space:nowrap}</style><h1>${escapeHtml(title)}</h1><div class="grid">${cells.join('')}</div>`)
  await page.screenshot({ path: output, fullPage: true })
}

async function overviewSheet(
  page: Page,
  key: string,
  modes: Readonly<Record<ModeName, { frames: readonly { image: string; progress: number; phase: string }[] }>>,
  output: string,
): Promise<void> {
  const frames = modes.reference.frames.length
  const cellWidth = 142, cellHeight = 164, labelWidth = 100
  await page.setViewportSize({ width: labelWidth + frames * cellWidth + 24, height: 56 + MODES.length * cellHeight })
  const rows: string[] = []
  for (const mode of MODES) {
    const cells = await Promise.all(modes[mode].frames.map(async (frame) => {
      const data = (await readFile(frame.image)).toString('base64')
      return `<figure><img src="data:image/png;base64,${data}"><figcaption>${frame.progress.toFixed(3)}</figcaption></figure>`
    }))
    rows.push(`<div class="row"><b>${mode}</b>${cells.join('')}</div>`)
  }
  await page.setContent(`<!doctype html><style>html,body{margin:0;background:#0c1117;color:#edf3f7;font:11px system-ui}h1{margin:10px 12px;font-size:18px}.row{display:grid;grid-template-columns:${labelWidth}px repeat(${frames},${cellWidth}px);height:${cellHeight}px}.row>b{display:flex;align-items:center;justify-content:center;border:1px solid #40505e}figure{margin:0;padding:3px;border:1px solid #40505e;box-sizing:border-box}img{width:${cellWidth - 8}px;height:${cellHeight - 28}px;object-fit:contain;background:#111923}figcaption{text-align:center}</style><h1>${escapeHtml(key)} · corrected reference / application 2D / application 3D light+dark</h1>${rows.join('')}`)
  await page.screenshot({ path: output, fullPage: true })
}

async function captureMode(
  page: Page,
  output: string,
  example: (typeof EXAMPLES)[number],
  mode: ModeName,
): Promise<{
  readonly sourceDimensions: { readonly width: number; readonly height: number }
  readonly backingDimensions: { readonly width: number; readonly height: number }
  readonly crop: Bounds
  readonly frames: Array<{
    progress: number
    sample: 'boundary' | 'midpoint'
    phase: string
    image: string
    imageSha256: string
    structural: StructuralFrame
    raster: RasterFrame
    observations: {
      source: RawFrame['source']
      baseColor: string
      strokes: Array<{
        pieceId: string
        address: string
        sourceStrokeId: string
        renderRole: string
        role: string
        lineage: RawStroke['lineage']
        copyIndex: number | null
        rendererOnly: boolean
        junctions: readonly [string, string]
        destinations: readonly [string | null, string | null]
        points: readonly [Point, Point]
        color: string
        raster: StrokeRaster
      }>
    }
    twoD?: TwoDFrame
    threeD?: ThreeDFrame
  }>
}> {
  const required = samplePoints(example.boundaries)
  const measured: BrowserMeasurement[] = []
  for (const { progress } of required) {
    measured.push(mode === 'reference'
      ? await referenceMeasure(page, progress)
      : await appMeasure(page, mode, progress))
  }
  const dimensions = measured[0]!.sourceDimensions
  const crop = unionBounds(measured.map(({ visualBounds }) => visualBounds), dimensions, mode === 'reference' ? 16 : 105)
  const final = measured.at(-1)!.raw
  const frames = []
  const directory = resolve(output, example.key, mode)
  await mkdir(directory, { recursive: true })
  for (let index = 0; index < required.length; index += 1) {
    const sample = required[index]!
    const measurement = mode === 'reference'
      ? await referenceMeasure(page, sample.progress)
      : await appMeasure(page, mode, sample.progress)
    const image = resolve(directory, `${String(index).padStart(2, '0')}-${sample.progress.toFixed(4)}.png`)
    await screenshotCanvas(page, mode === 'reference' ? '#canvas' : mode.startsWith('2d') ? '#two' : '#three canvas', crop, image)
    frames.push({
      progress: sample.progress,
      sample: sample.sample,
      phase: normalizePhase(measurement.raw.phase),
      image,
      imageSha256: sha256(await readFile(image)),
      structural: summarize(measurement.raw, final),
      raster: measurement.raster,
      observations: {
        source: measurement.raw.source,
        baseColor: measurement.raw.baseColor,
        strokes: measurement.raw.strokes.map((stroke) => ({
          pieceId: stroke.id,
          address: stroke.address,
          sourceStrokeId: stroke.sourceStrokeId,
          renderRole: stroke.renderRole,
          role: stroke.role,
          lineage: stroke.lineage,
          copyIndex: stroke.copyIndex,
          rendererOnly: stroke.rendererOnly,
          junctions: [stroke.junctionA, stroke.junctionB] as const,
          destinations: [stroke.destinationJunctionA, stroke.destinationJunctionB] as const,
          points: [
            [round(stroke.a[0]), round(stroke.a[1])] as const,
            [round(stroke.b[0]), round(stroke.b[1])] as const,
          ] as const,
          color: stroke.color,
          raster: {
            screenLength: round(stroke.raster.screenLength),
            matchingPixels: stroke.raster.matchingPixels,
            bestColorDistance: round(Number.isFinite(stroke.raster.bestColorDistance)
              ? stroke.raster.bestColorDistance
              : 999),
          },
        })),
      },
      ...(measurement.twoD === undefined ? {} : { twoD: measurement.twoD }),
      ...(measurement.threeD === undefined ? {} : { threeD: measurement.threeD }),
    })
  }
  return {
    sourceDimensions: dimensions,
    backingDimensions: measured[0]!.backingDimensions,
    crop,
    frames,
  }
}

async function main(): Promise<void> {
  const output = outputFromArgs()
  await stat(REFERENCE_PATH).catch(() => { throw new Error(`corrected Lambda reference is missing: ${REFERENCE_PATH}`) })
  await rm(output, { recursive: true, force: true })
  await mkdir(resolve(output, 'contact'), { recursive: true })
  const referenceBytes = await readFile(REFERENCE_PATH)
  const appCommit = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: ROOT, encoding: 'utf8' }).trim()
  const appSourceHash = await sourceHash()
  let browser: Browser | null = null
  let server: ViteDevServer | null = null
  try {
    const harness = await startHarnessServer()
    server = harness.server
    browser = await chromium.launch({ headless: true })
    const context = await browser.newContext({ viewport: VIEWPORT, deviceScaleFactor: 1 })
    // tsx preserves callback names with this harmless helper; Playwright
    // serializes callbacks into an isolated browser world that does not inherit
    // the Node-side helper.
    await context.addInitScript('globalThis.__name = (target) => target')
    const referencePage = await context.newPage()
    await referencePage.goto(pathToFileURL(REFERENCE_PATH).href)
    await referencePage.waitForFunction(() => '__lambdaDemo' in window)
    const appPage = await context.newPage()
    await appPage.goto(harness.url)
    await appPage.waitForFunction(() => '__lambdaComparison' in window)
    const sheetPage = await context.newPage()
    const examples = []
    for (const example of EXAMPLES) {
      const reference = await referenceLoad(referencePage, example.source)
      if (reference.copyCount !== example.copies) throw new Error(`${example.key}: corrected reference copy count ${reference.copyCount} != ${example.copies}`)
      await validateReferenceSchedule(referencePage, example.boundaries, example.copies)
      const app = await appLoad(appPage, example.source)
      if (app.copyCount !== example.copies) throw new Error(`${example.key}: application copy count ${app.copyCount} != ${example.copies}`)
      const expectedTimes = example.copies === 0
        ? { split: 0.15, liftEnd: 0.38, spaceEnd: 0.64, dockEnd: 0.64, stemEnd: 0.64, barEnd: 0.93 }
        : { split: 0.15, liftEnd: 0.34, spaceEnd: 0.54, dockEnd: 0.82, stemEnd: 0.91, barEnd: 0.965 }
      if (JSON.stringify(app.times) !== JSON.stringify(expectedTimes)) throw new Error(`${example.key}: application stage timing disagrees with the corrected reference`)
      const modes = {} as Record<ModeName, Awaited<ReturnType<typeof captureMode>> & { contactSheet: string; contactSheetSha256: string }>
      for (const mode of MODES) {
        const page = mode === 'reference' ? referencePage : appPage
        const captured = await captureMode(page, output, example, mode)
        const contact = resolve(output, 'contact', `${example.key}-${mode}.png`)
        await contactSheet(sheetPage, `${example.key} · ${mode}`, captured.frames, contact)
        modes[mode] = { ...captured, contactSheet: contact, contactSheetSha256: sha256(await readFile(contact)) }
      }
      const overview = resolve(output, 'contact', `${example.key}-overview.png`)
      await overviewSheet(sheetPage, example.key, modes, overview)
      examples.push({
        key: example.key,
        source: example.source,
        copyCount: example.copies,
        boundaries: [...example.boundaries],
        correspondence: {
          argumentStrokeAddresses: reference.argumentStrokeAddresses,
          argumentRootJunction: reference.argumentRootJunction,
        },
        overview,
        overviewSha256: sha256(await readFile(overview)),
        modes,
      })
      process.stdout.write(`captured ${example.key}: ${samplePoints(example.boundaries).length} frames × ${MODES.length} modes\n`)
    }
    const manifest = {
      schema: 1,
      generatedAt: new Date().toISOString(),
      outputDirectory: output,
      reference: { path: REFERENCE_PATH, sha256: sha256(referenceBytes) },
      application: { commit: appCommit, sourceHash: appSourceHash },
      palette: PALETTE,
      examples,
    }
    await writeFile(resolve(output, 'manifest.json'), `${JSON.stringify(manifest, null, 2)}\n`)
    process.stdout.write(`manifest: ${resolve(output, 'manifest.json')}\n`)
    process.stdout.write(`images: ${examples.reduce((sum, example) => sum + Object.values(example.modes).reduce((modeSum, mode) => modeSum + mode.frames.length, 0), 0)}\n`)
  } finally {
    await browser?.close()
    await server?.close()
  }
}

if (process.argv[1] !== undefined && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  main().catch((error: unknown) => {
    process.stderr.write(`${error instanceof Error ? error.stack ?? error.message : String(error)}\n`)
    process.exitCode = 1
  })
}
