import { applyStepAt, type PathSeg, type ReductionStep } from '../kernel/term/reduce'
import { application, bound, free, lambda, termEq, type Term } from '../kernel/term/term'
import { bendMaps, GAP_ANGLE } from './bend'
import { trompGrid, type TrompGrid } from './tromp'
import type { Vec2 } from './vec'
import { polar } from './vec'

export const REDEX_COLOR = '#f06aa7'
export const ARGUMENT_COLOR = '#f0bd55'
export const COPY_HUES = Object.freeze([
  '#58ddcf',
  '#6da8ff',
  '#c084fc',
  '#fb7185',
  '#34d399',
] as const)

export type LambdaPhase =
  | 'identify'
  | 'duplicate'
  | 'discard'
  | 'make-space'
  | 'substitute'
  | 'cleanup'
  | 'settle'

export type LambdaStrokeLineage = 'persistent' | 'redex' | 'argument' | 'copy'

export type LambdaStrokeRole =
  | 'lambda'
  | 'application'
  | 'variable'
  | 'fn-connector'
  | 'argument-connector'
  | 'free-drop'
  | 'free-rail'
  | 'free-port'
  | 'term-output'
  | 'output-arc'
  | 'output-line'

export type LambdaStrokePoint = Vec2 & {
  /** Stable source-junction identity used by both renderers. */
  readonly junction: string
}

export type LambdaStrokeGeometry =
  | { readonly kind: 'arc'; readonly r: number; readonly a0: number; readonly a1: number }
  | { readonly kind: 'segment'; readonly from: Vec2; readonly to: Vec2 }

export type LambdaStroke = {
  readonly id: string
  /** The corresponding source-argument stroke, or the stroke's own stable id. */
  readonly originId: string
  readonly ownerId: string | null
  readonly role: LambdaStrokeRole
  readonly lineage: LambdaStrokeLineage
  readonly copyIndex: number | null
  readonly color: string
  readonly points: readonly [LambdaStrokePoint, LambdaStrokePoint]
  readonly geometry: LambdaStrokeGeometry
}

export type LambdaSocket = {
  readonly copyIndex: number
  readonly sourceOccurrenceId: string
  readonly point: Vec2
  readonly amount: number
}

export type LambdaStrokeFrame = {
  readonly phase: LambdaPhase
  readonly strokes: readonly LambdaStroke[]
  readonly sockets: readonly LambdaSocket[]
}

export type LambdaStageTimes = {
  readonly split: number
  readonly liftEnd: number
  readonly spaceEnd: number
  readonly dockEnd: number
  readonly stemEnd: number
  readonly barEnd: number
}

export type LambdaJunctionCorrespondence = {
  readonly sourceId: string
  readonly source: Vec2
  readonly target: Vec2
}

export type LambdaMotionPlan = {
  readonly source: Term
  readonly target: Term
  readonly step: ReductionStep
  readonly copyCount: number
  readonly times: LambdaStageTimes
  readonly persistentJunctions: readonly LambdaJunctionCorrespondence[]
  /** Internal structural authority retained for deterministic resampling. */
  readonly model: MotionModel
}

type AnnotatedNode = {
  readonly kind: Term['kind']
  readonly id: string
  readonly originSourceId: string | null
  readonly copyIndex: number | null
  readonly slot?: number
  readonly bindingId?: string
  readonly body?: AnnotatedNode
  readonly fn?: AnnotatedNode
  readonly argument?: AnnotatedNode
}

type GridCoord = { readonly kind: 'grid'; readonly col: number; readonly row: number }
type MotionCoord = GridCoord | { readonly kind: 'gap'; readonly row: number } | { readonly kind: 'port' }

type PointModel = {
  readonly id: string
  readonly originId: string
  readonly coord: MotionCoord
}

type StrokeDrawKind = 'horizontal' | 'vertical' | 'output-arc' | 'output-line'

type StrokeModel = {
  readonly id: string
  readonly originId: string
  readonly ownerId: string | null
  readonly originOwnerId: string | null
  readonly role: LambdaStrokeRole
  readonly copyIndex: number | null
  readonly drawKind: StrokeDrawKind
  readonly a: PointModel
  readonly b: PointModel
}

type NodeBox = {
  readonly left: number
  readonly right: number
  readonly top: number
  readonly bottom: number
}

type StrokeModelSet = {
  readonly root: AnnotatedNode
  readonly grid: TrompGrid
  readonly points: ReadonlyMap<string, PointModel>
  readonly pointsByOrigin: ReadonlyMap<string, PointModel>
  readonly strokes: readonly StrokeModel[]
  readonly strokeById: ReadonlyMap<string, StrokeModel>
  readonly nodeBoxes: ReadonlyMap<string, NodeBox>
  readonly nodeIds: ReadonlySet<string>
  readonly nodeOut: (node: AnnotatedNode) => string
}

type ViewFrame = {
  readonly cols: number
  readonly rows: number
  readonly railRows: number
  readonly sourceOffset: number
  readonly targetOffset: number
}

type StrokePair = { readonly source: StrokeModel; readonly target: StrokeModel }
type OccurrenceCopy = {
  readonly sourceVarId: string
  readonly copyIndex: number
  readonly targetRootId: string
}

type CopyStage = { readonly targetRoot: GridCoord; readonly stageRoot: GridCoord }

type MotionModel = {
  readonly source: StrokeModelSet
  readonly target: StrokeModelSet
  readonly view: ViewFrame
  readonly pairs: readonly StrokePair[]
  readonly sourceArgument: readonly StrokeModel[]
  readonly redexScaffolding: readonly StrokeModel[]
  readonly lambdaStroke: StrokeModel
  readonly boundStrokes: readonly StrokeModel[]
  readonly reflowed: readonly StrokeModel[]
  readonly targetCopies: ReadonlyMap<number, readonly StrokeModel[]>
  readonly targetOfSource: ReadonlyMap<string, MotionCoord>
  readonly sourceArgumentPointByOrigin: ReadonlyMap<string, PointModel>
  readonly copies: readonly OccurrenceCopy[]
  readonly copyStages: ReadonlyMap<number, CopyStage>
  readonly sourceBodyOut: GridCoord
  readonly sourceArgumentRoot: GridCoord
  readonly sourceLambdaA: GridCoord
  readonly sourceLambdaB: GridCoord
  readonly targetBinderRow: number
  readonly targetBinderLeft: number
  readonly targetBinderRight: number
}

const gridCoord = (col: number, row: number): GridCoord => ({ kind: 'grid', col, row })
const pathId = (path: readonly PathSeg[]): string => path.length === 0 ? 'root' : `root/${path.join('/')}`
const clamp = (value: number): number => Math.max(0, Math.min(1, value))
const smooth = (value: number): number => {
  const p = clamp(value)
  return p * p * (3 - 2 * p)
}
const stageProgress = (progress: number, start: number, end: number): number => (
  end === start ? 1 : smooth((progress - start) / (end - start))
)
const mix = (from: number, to: number, progress: number): number => from + (to - from) * progress

function mixColor(from: string, to: string, progress: number): string {
  const parse = (color: string): readonly [number, number, number] => {
    const match = /^#([0-9a-f]{6})$/i.exec(color)
    if (match === null) throw new Error(`Lambda motion requires a six-digit hex base color, got '${color}'`)
    const value = Number.parseInt(match[1]!, 16)
    return [value >> 16, (value >> 8) & 255, value & 255]
  }
  const a = parse(from), b = parse(to), p = clamp(progress)
  const channels = a.map((channel, index) => Math.round(mix(channel, b[index]!, p)))
  return `#${channels.map((channel) => channel.toString(16).padStart(2, '0')).join('')}`
}

function annotate(term: Term, path: readonly PathSeg[] = [], binders: readonly string[] = []): AnnotatedNode {
  const id = pathId(path)
  switch (term.kind) {
    case 'bound': {
      const bindingId = binders[term.index]
      if (bindingId === undefined) throw new Error(`unbound index ${term.index} while planning Lambda motion`)
      return { kind: 'bound', id, originSourceId: null, copyIndex: null, bindingId }
    }
    case 'free':
      return { kind: 'free', id, originSourceId: null, copyIndex: null, slot: term.slot }
    case 'lambda':
      return {
        kind: 'lambda', id, originSourceId: null, copyIndex: null,
        body: annotate(term.body, [...path, 'body'], [id, ...binders]),
      }
    case 'application':
      return {
        kind: 'application', id, originSourceId: null, copyIndex: null,
        fn: annotate(term.fn, [...path, 'fn'], binders),
        argument: annotate(term.argument, [...path, 'argument'], binders),
      }
  }
}

function child(node: AnnotatedNode, segment: PathSeg): AnnotatedNode {
  if (segment === 'body' && node.kind === 'lambda') return node.body!
  if (segment === 'fn' && node.kind === 'application') return node.fn!
  if (segment === 'argument' && node.kind === 'application') return node.argument!
  throw new Error(`invalid path segment '${segment}' into '${node.kind}' while planning Lambda motion`)
}

function annotatedAt(root: AnnotatedNode, path: readonly PathSeg[]): AnnotatedNode {
  let current = root
  for (const segment of path) current = child(current, segment)
  return current
}

function walkAnnotated(
  node: AnnotatedNode,
  visit: (node: AnnotatedNode, path: readonly PathSeg[]) => void,
  path: readonly PathSeg[] = [],
): void {
  visit(node, path)
  if (node.kind === 'lambda') walkAnnotated(node.body!, visit, [...path, 'body'])
  if (node.kind === 'application') {
    walkAnnotated(node.fn!, visit, [...path, 'fn'])
    walkAnnotated(node.argument!, visit, [...path, 'argument'])
  }
}

function annotatedById(root: AnnotatedNode, id: string): AnnotatedNode {
  let found: AnnotatedNode | undefined
  walkAnnotated(root, (node) => { if (node.id === id) found = node })
  if (found === undefined) throw new Error(`motion model has no semantic node '${id}'`)
  return found
}

function cloneArgument(
  node: AnnotatedNode,
  copyIndex: number,
  binders: ReadonlyMap<string, string> = new Map(),
): AnnotatedNode {
  const id = `copy:${copyIndex}:${node.id}`
  const common = { id, originSourceId: node.id, copyIndex } as const
  switch (node.kind) {
    case 'bound':
      return { kind: 'bound', ...common, bindingId: binders.get(node.bindingId!) ?? node.bindingId! }
    case 'free':
      return { kind: 'free', ...common, slot: node.slot! }
    case 'lambda': {
      const nextBinders = new Map(binders)
      nextBinders.set(node.id, id)
      return { kind: 'lambda', ...common, body: cloneArgument(node.body!, copyIndex, nextBinders) }
    }
    case 'application':
      return {
        kind: 'application', ...common,
        fn: cloneArgument(node.fn!, copyIndex, binders),
        argument: cloneArgument(node.argument!, copyIndex, binders),
      }
  }
}

function substituteAnnotated(
  node: AnnotatedNode,
  binderId: string,
  argument: AnnotatedNode,
  copies: OccurrenceCopy[],
): AnnotatedNode {
  if (node.kind === 'bound' && node.bindingId === binderId) {
    const copyIndex = copies.length
    const copy = cloneArgument(argument, copyIndex)
    copies.push({ sourceVarId: node.id, copyIndex, targetRootId: copy.id })
    return copy
  }
  if (node.kind === 'lambda') {
    return { ...node, body: substituteAnnotated(node.body!, binderId, argument, copies) }
  }
  if (node.kind === 'application') {
    return {
      ...node,
      fn: substituteAnnotated(node.fn!, binderId, argument, copies),
      argument: substituteAnnotated(node.argument!, binderId, argument, copies),
    }
  }
  return node
}

function replaceAnnotated(root: AnnotatedNode, path: readonly PathSeg[], replacement: AnnotatedNode): AnnotatedNode {
  if (path.length === 0) return replacement
  const [segment, ...rest] = path
  if (segment === 'body' && root.kind === 'lambda') {
    return { ...root, body: replaceAnnotated(root.body!, rest, replacement) }
  }
  if (segment === 'fn' && root.kind === 'application') {
    return { ...root, fn: replaceAnnotated(root.fn!, rest, replacement) }
  }
  if (segment === 'argument' && root.kind === 'application') {
    return { ...root, argument: replaceAnnotated(root.argument!, rest, replacement) }
  }
  throw new Error(`invalid beta replacement path [${path.join(', ')}]`)
}

function plainTerm(root: AnnotatedNode): Term {
  const convert = (node: AnnotatedNode, binders: readonly string[]): Term => {
    switch (node.kind) {
      case 'bound': {
        const index = binders.indexOf(node.bindingId!)
        if (index < 0) throw new Error(`motion target lost binder '${node.bindingId}'`)
        return bound(index)
      }
      case 'free': return free(node.slot!)
      case 'lambda': return lambda(convert(node.body!, [node.id, ...binders]))
      case 'application': return application(convert(node.fn!, binders), convert(node.argument!, binders))
    }
  }
  return convert(root, [])
}

function nodeOriginId(node: AnnotatedNode): string {
  return node.originSourceId ?? node.id
}

function nodeOutId(node: AnnotatedNode): string {
  if (node.kind === 'lambda') return nodeOutId(node.body!)
  return `${node.id}:out`
}

function nodeOutOriginId(node: AnnotatedNode): string {
  if (node.kind === 'lambda') return nodeOutOriginId(node.body!)
  return `${nodeOriginId(node)}:out`
}

function buildStrokeModel(root: AnnotatedNode): StrokeModelSet {
  const rendered = plainTerm(root)
  const grid = trompGrid(rendered)
  const nodesByPath = new Map<string, AnnotatedNode>()
  const pathsByNode = new Map<string, readonly PathSeg[]>()
  const nodeIds = new Set<string>()
  walkAnnotated(root, (node, path) => {
    nodesByPath.set(path.join('/'), node)
    pathsByNode.set(node.id, path)
    nodeIds.add(node.id)
  })
  const atPath = (path: readonly PathSeg[]): AnnotatedNode => {
    const node = nodesByPath.get(path.join('/'))
    if (node === undefined) throw new Error(`motion model has no semantic node at [${path.join(', ')}]`)
    return node
  }

  const points = new Map<string, PointModel>()
  const pointsByOrigin = new Map<string, PointModel>()
  const addPoint = (id: string, originId: string, coord: MotionCoord): PointModel => {
    const existing = points.get(id)
    if (existing !== undefined) {
      if (existing.coord.kind !== coord.kind) throw new Error(`junction '${id}' changed coordinate kind`)
      if (coord.kind === 'grid' && existing.coord.kind === 'grid') {
        if (Math.hypot(existing.coord.col - coord.col, existing.coord.row - coord.row) > 1e-9) {
          throw new Error(`junction '${id}' has incompatible grid positions`)
        }
      }
      return existing
    }
    const point = { id, originId, coord }
    points.set(id, point)
    if (!pointsByOrigin.has(originId)) pointsByOrigin.set(originId, point)
    return point
  }

  const strokes: StrokeModel[] = []
  const addStroke = (
    owner: AnnotatedNode | null,
    role: LambdaStrokeRole,
    drawKind: StrokeDrawKind,
    a: PointModel,
    b: PointModel,
    interfaceId?: string,
  ): void => {
    const id = owner === null ? interfaceId! : `${owner.id}:${role}`
    const originId = owner === null ? id : `${nodeOriginId(owner)}:${role}`
    strokes.push({
      id, originId,
      ownerId: owner?.id ?? null,
      originOwnerId: owner === null ? null : nodeOriginId(owner),
      role, copyIndex: owner?.copyIndex ?? null, drawKind, a, b,
    })
  }

  const freeBySlotAndCol = new Map<string, AnnotatedNode>()
  for (const occurrence of grid.occurrences) {
    const node = atPath(occurrence.path)
    if (node.kind === 'free') freeBySlotAndCol.set(`${node.slot}:${occurrence.colStart}`, node)
  }

  for (let index = 0; index < grid.bars.length; index++) {
    const bar = grid.bars[index]!
    const ownerPath = grid.barOwners[index]
    if (ownerPath === undefined) throw new Error(`bar ${index} has no structural owner entry`)
    if (ownerPath === null) {
      const rail = grid.rails.find((candidate) => candidate.row === bar.row)
      if (rail === undefined) throw new Error(`unowned bar at row ${bar.row} is not a free rail`)
      const prefix = `interface:free:${rail.slot}:rail`
      addStroke(
        null, 'free-rail', 'horizontal',
        addPoint(`${prefix}:left`, `${prefix}:left`, gridCoord(bar.colStart, bar.row)),
        addPoint(`${prefix}:right`, `${prefix}:right`, gridCoord(bar.colEnd, bar.row)),
        prefix,
      )
      continue
    }
    const owner = atPath(ownerPath)
    if (bar.kind === 'lam') {
      addStroke(
        owner, 'lambda', 'horizontal',
        addPoint(`${owner.id}:lambda:left`, `${nodeOriginId(owner)}:lambda:left`, gridCoord(bar.colStart, bar.row)),
        addPoint(`${owner.id}:lambda:right`, `${nodeOriginId(owner)}:lambda:right`, gridCoord(bar.colEnd, bar.row)),
      )
    } else if (bar.kind === 'app') {
      addStroke(
        owner, 'application', 'horizontal',
        addPoint(nodeOutId(owner), nodeOutOriginId(owner), gridCoord(bar.colStart, bar.row)),
        addPoint(`${owner.id}:application:right`, `${nodeOriginId(owner)}:application:right`, gridCoord(bar.colEnd, bar.row)),
      )
    } else {
      throw new Error(`owned rail '${owner.id}' is not a Lambda node stroke`)
    }
  }

  const finalOutputIndex = grid.stems.length - 1
  for (let index = 0; index < grid.stems.length; index++) {
    const stem = grid.stems[index]!
    const ownerPath = grid.stemOwners[index]
    if (ownerPath === undefined) throw new Error(`stem ${index} has no structural owner entry`)
    if (stem.kind === 'output' && index === finalOutputIndex) {
      const output = nodeOutId(root), origin = nodeOutOriginId(root)
      addStroke(
        null, 'term-output', 'vertical',
        addPoint(output, origin, gridCoord(stem.col, stem.rowTop)),
        addPoint('interface:output:inner', 'interface:output:inner', gridCoord(stem.col, stem.rowBottom)),
        'interface:output:stem',
      )
      continue
    }
    if (ownerPath === null) {
      if (stem.kind !== 'port' || stem.portSlot === undefined) {
        throw new Error(`unowned '${stem.kind}' stem is not a free-slot drop`)
      }
      const owner = freeBySlotAndCol.get(`${stem.portSlot}:${stem.col}`)
      if (owner === undefined) throw new Error(`free-slot drop ${stem.portSlot}@${stem.col} has no semantic occurrence`)
      const ownerPathForDepth = pathsByNode.get(owner.id)!
      const occurrence = grid.occurrences.find((candidate) => (
        candidate.path.length === ownerPathForDepth.length
        && candidate.path.every((segment, part) => segment === ownerPathForDepth[part])
      ))!
      const bottomId = occurrence.layoutDepth === 0 ? nodeOutId(owner) : `${owner.id}:bind`
      const bottomOrigin = occurrence.layoutDepth === 0 ? nodeOutOriginId(owner) : `${nodeOriginId(owner)}:bind`
      addStroke(
        owner, 'free-drop', 'vertical',
        addPoint(`${owner.id}:free-rail`, `${nodeOriginId(owner)}:free-rail`, gridCoord(stem.col, stem.rowTop)),
        addPoint(bottomId, bottomOrigin, gridCoord(stem.col, stem.rowBottom)),
      )
      continue
    }
    const owner = atPath(ownerPath)
    if (stem.kind === 'var' || stem.kind === 'port') {
      addStroke(
        owner, 'variable', 'vertical',
        addPoint(`${owner.id}:bind`, `${nodeOriginId(owner)}:bind`, gridCoord(stem.col, stem.rowTop)),
        addPoint(nodeOutId(owner), nodeOutOriginId(owner), gridCoord(stem.col, stem.rowBottom)),
      )
      continue
    }
    if (stem.kind === 'output') {
      const parentPath = ownerPath.slice(0, -1)
      const side = ownerPath[ownerPath.length - 1]
      const parent = atPath(parentPath)
      if (parent.kind !== 'application' || (side !== 'fn' && side !== 'argument')) {
        throw new Error(`output connector [${ownerPath.join(', ')}] has no application parent`)
      }
      const role = side === 'fn' ? 'fn-connector' : 'argument-connector'
      const bottomId = side === 'fn' ? nodeOutId(parent) : `${parent.id}:application:right`
      const bottomOrigin = side === 'fn' ? nodeOutOriginId(parent) : `${nodeOriginId(parent)}:application:right`
      addStroke(
        parent, role, 'vertical',
        addPoint(nodeOutId(owner), nodeOutOriginId(owner), gridCoord(stem.col, stem.rowTop)),
        addPoint(bottomId, bottomOrigin, gridCoord(stem.col, stem.rowBottom)),
      )
      continue
    }
    throw new Error(`unclassified '${stem.kind}' stem in Lambda motion model`)
  }

  for (const rail of grid.rails) {
    const prefix = `interface:free:${rail.slot}`
    addStroke(
      null, 'free-port', 'vertical',
      addPoint(`${prefix}:rail:left`, `${prefix}:rail:left`, gridCoord(rail.stemCol, rail.row)),
      addPoint(`${prefix}:port`, `${prefix}:port`, gridCoord(rail.stemCol, -grid.railRows - 1)),
      `${prefix}:port-stem`,
    )
  }

  addStroke(
    null, 'output-arc', 'output-arc',
    addPoint('interface:output:elbow', 'interface:output:elbow', { kind: 'gap', row: grid.rows }),
    addPoint('interface:output:inner', 'interface:output:inner', gridCoord(grid.outputCol, grid.rows)),
    'interface:output:arc',
  )
  addStroke(
    null, 'output-line', 'output-line',
    addPoint('interface:output:elbow', 'interface:output:elbow', { kind: 'gap', row: grid.rows }),
    addPoint('interface:output:port', 'interface:output:port', { kind: 'port' }),
    'interface:output:line',
  )

  const nodeBoxes = new Map<string, NodeBox>()
  for (const occurrence of grid.occurrences) {
    const node = atPath(occurrence.path)
    nodeBoxes.set(node.id, {
      left: occurrence.colStart,
      right: occurrence.colEnd,
      top: occurrence.layoutDepth,
      bottom: occurrence.bottom,
    })
  }
  return {
    root, grid, points, pointsByOrigin, strokes,
    strokeById: new Map(strokes.map((stroke) => [stroke.id, stroke])),
    nodeBoxes, nodeIds,
    nodeOut: nodeOutId,
  }
}

function shifted(coord: MotionCoord, offset: number): MotionCoord {
  return coord.kind === 'grid' ? gridCoord(coord.col + offset, coord.row) : coord
}

function asGrid(coord: MotionCoord, context: string): GridCoord {
  if (coord.kind !== 'grid') throw new Error(`${context} is not a grid junction`)
  return coord
}

function sameCoord(left: MotionCoord, right: MotionCoord): boolean {
  if (left.kind !== right.kind) return false
  if (left.kind === 'port') return true
  if (left.kind === 'gap' && right.kind === 'gap') return Math.abs(left.row - right.row) <= 1e-9
  return left.kind === 'grid' && right.kind === 'grid'
    && Math.hypot(left.col - right.col, left.row - right.row) <= 1e-9
}

function interpolateCoord(from: MotionCoord, to: MotionCoord, progress: number): MotionCoord {
  if (from.kind !== to.kind) throw new Error(`cannot interpolate ${from.kind} junction to ${to.kind}`)
  if (from.kind === 'port') return from
  if (from.kind === 'gap' && to.kind === 'gap') return { kind: 'gap', row: mix(from.row, to.row, progress) }
  if (from.kind === 'grid' && to.kind === 'grid') {
    return gridCoord(mix(from.col, to.col, progress), mix(from.row, to.row, progress))
  }
  throw new Error('incompatible Lambda motion junctions')
}

function mapCoord(coord: MotionCoord, view: ViewFrame): Vec2 {
  const maps = bendMaps(view.cols, view.rows, view.railRows)
  if (coord.kind === 'port') return polar(0, maps.pierceR)
  if (coord.kind === 'gap') return polar(GAP_ANGLE / 2, maps.radius(coord.row))
  return polar(maps.theta(coord.col), maps.radius(coord.row))
}

function strokeFrame(
  stroke: StrokeModel,
  a: MotionCoord,
  b: MotionCoord,
  view: ViewFrame,
  color: string,
  lineage: LambdaStrokeLineage,
): LambdaStroke {
  const from = mapCoord(a, view), to = mapCoord(b, view)
  let geometry: LambdaStrokeGeometry
  if (stroke.drawKind === 'horizontal' || stroke.drawKind === 'output-arc') {
    const rowA = a.kind === 'grid' || a.kind === 'gap' ? a.row : null
    const rowB = b.kind === 'grid' || b.kind === 'gap' ? b.row : null
    if (rowA === null || rowB === null || Math.abs(rowA - rowB) > 1e-7) {
      throw new Error(`horizontal incidence violated by ${stroke.id}`)
    }
    const angle = (coord: MotionCoord): number => {
      if (coord.kind === 'gap') return GAP_ANGLE / 2
      if (coord.kind === 'grid') return bendMaps(view.cols, view.rows, view.railRows).theta(coord.col)
      throw new Error(`arc '${stroke.id}' reaches the output port directly`)
    }
    const first = angle(a), second = angle(b)
    geometry = {
      kind: 'arc',
      r: bendMaps(view.cols, view.rows, view.railRows).radius(rowA),
      a0: Math.min(first, second), a1: Math.max(first, second),
    }
  } else {
    if (stroke.drawKind === 'vertical' && a.kind === 'grid' && b.kind === 'grid' && Math.abs(a.col - b.col) > 1e-7) {
      throw new Error(`vertical incidence violated by ${stroke.id}`)
    }
    geometry = { kind: 'segment', from, to }
  }
  return {
    id: stroke.id,
    originId: stroke.originId,
    ownerId: stroke.ownerId,
    role: stroke.role,
    lineage,
    copyIndex: stroke.copyIndex,
    color,
    points: [
      { ...from, junction: stroke.a.id },
      { ...to, junction: stroke.b.id },
    ],
    geometry,
  }
}

function copyHue(copyIndex: number): string {
  return COPY_HUES[copyIndex % COPY_HUES.length]!
}

function phaseAt(copyCount: number, times: LambdaStageTimes, progress: number): LambdaPhase {
  if (progress < times.split) return 'identify'
  if (progress < times.liftEnd) return copyCount > 0 ? 'duplicate' : 'discard'
  if (progress < times.spaceEnd) return 'make-space'
  if (progress < times.dockEnd) return 'substitute'
  if (progress < times.barEnd) return 'cleanup'
  return 'settle'
}

function createMotionModel(
  sourceRoot: AnnotatedNode,
  targetRoot: AnnotatedNode,
  redex: AnnotatedNode,
  binder: AnnotatedNode,
  body: AnnotatedNode,
  argument: AnnotatedNode,
  targetReduct: AnnotatedNode,
  copies: readonly OccurrenceCopy[],
): { readonly motion: MotionModel; readonly persistentJunctions: readonly LambdaJunctionCorrespondence[] } {
  const source = buildStrokeModel(sourceRoot), target = buildStrokeModel(targetRoot)
  const view: ViewFrame = {
    cols: Math.max(source.grid.cols, target.grid.cols),
    rows: Math.max(source.grid.rows, target.grid.rows),
    railRows: Math.max(source.grid.railRows, target.grid.railRows),
    sourceOffset: (Math.max(source.grid.cols, target.grid.cols) - source.grid.cols) / 2,
    targetOffset: (Math.max(source.grid.cols, target.grid.cols) - target.grid.cols) / 2,
  }
  const sourceCoord = (point: PointModel): MotionCoord => shifted(point.coord, view.sourceOffset)
  const targetCoord = (point: PointModel): MotionCoord => shifted(point.coord, view.targetOffset)

  const pairs: StrokePair[] = [], removed: StrokeModel[] = []
  for (const stroke of source.strokes) {
    const targetStroke = target.strokeById.get(stroke.id)
    if (targetStroke === undefined) removed.push(stroke)
    else pairs.push({ source: stroke, target: targetStroke })
  }
  const argumentIds = new Set<string>()
  const argumentSlots = new Set<number>()
  walkAnnotated(argument, (node) => {
    argumentIds.add(node.id)
    if (node.kind === 'free') argumentSlots.add(node.slot!)
  })
  const introduced = target.strokes.filter((stroke) => !source.strokeById.has(stroke.id))
  for (const stroke of introduced) {
    if (stroke.copyIndex === null || stroke.originOwnerId === null || !argumentIds.has(stroke.originOwnerId)) {
      throw new Error(`beta transition introduced non-copy stroke ${stroke.id}`)
    }
  }
  const targetCopies = new Map<number, StrokeModel[]>()
  for (const introducedStroke of introduced) {
    const depthSplitOrigin = introducedStroke.originOwnerId === null
      ? introducedStroke.originId
      : `${introducedStroke.originOwnerId}:free-drop`
    const stroke = introducedStroke.role === 'variable'
      && !source.strokeById.has(introducedStroke.originId)
      && source.strokeById.has(depthSplitOrigin)
      ? { ...introducedStroke, originId: depthSplitOrigin }
      : introducedStroke
    const group = targetCopies.get(stroke.copyIndex!) ?? []
    group.push(stroke)
    targetCopies.set(stroke.copyIndex!, group)
  }

  const targetOfSource = new Map<string, MotionCoord>()
  const offer = (sourcePointId: string, destination: MotionCoord, reason: string): void => {
    if (!source.points.has(sourcePointId)) throw new Error(`missing source junction ${sourcePointId}`)
    const existing = targetOfSource.get(sourcePointId)
    if (existing !== undefined && !sameCoord(existing, destination)) {
      throw new Error(`source junction ${sourcePointId} has incompatible targets (${reason})`)
    }
    targetOfSource.set(sourcePointId, destination)
  }
  for (const pair of pairs) {
    offer(pair.source.a.id, targetCoord(pair.target.a), pair.source.id)
    offer(pair.source.b.id, targetCoord(pair.target.b), pair.source.id)
  }
  const sourceRootOut = source.nodeOut(sourceRoot), targetRootOut = target.nodeOut(targetRoot)
  offer(sourceRootOut, targetCoord(target.points.get(targetRootOut)!), 'term output')
  const targetReductOut = target.nodeOut(targetReduct)
  const targetReductCoord = targetCoord(target.points.get(targetReductOut)!)
  offer(source.nodeOut(redex), targetReductCoord, 'redex output')
  offer(source.nodeOut(body), targetReductCoord, 'function-body output')

  const socketByCopy = new Map<number, { readonly targetPoint: GridCoord; readonly sourceVarId: string }>()
  for (const occurrence of copies) {
    const targetRootOutId = target.nodeOut(annotatedById(targetRoot, occurrence.targetRootId))
    const targetPoint = asGrid(targetCoord(target.points.get(targetRootOutId)!), `copy ${occurrence.copyIndex} root`)
    offer(`${occurrence.sourceVarId}:out`, targetPoint, `substitution socket ${occurrence.copyIndex}`)
    socketByCopy.set(occurrence.copyIndex, { targetPoint, sourceVarId: occurrence.sourceVarId })
  }

  const occurrenceIds = new Set(copies.map(({ sourceVarId }) => sourceVarId))
  const sourceArgument = removed.filter((stroke) => {
    if (stroke.ownerId !== null) return argumentIds.has(stroke.ownerId)
    if (stroke.role !== 'free-rail' && stroke.role !== 'free-port') return false
    const slot = /^interface:free:(\d+):/.exec(stroke.id)?.[1]
    return slot !== undefined && argumentSlots.has(Number(slot))
  })
  const lambdaStroke = removed.find((stroke) => stroke.ownerId === binder.id && stroke.role === 'lambda')
  const boundStrokes = removed.filter((stroke) => (
    stroke.ownerId !== null && occurrenceIds.has(stroke.ownerId) && stroke.role === 'variable'
  ))
  const redexScaffolding = removed.filter((stroke) => stroke.ownerId === redex.id)
  if (lambdaStroke === undefined) throw new Error('beta transition has no consumed lambda bar')
  if (boundStrokes.length !== copies.length) {
    throw new Error(`beta transition expected ${copies.length} bound-variable stems, found ${boundStrokes.length}`)
  }
  const classified = new Set([
    ...sourceArgument, ...boundStrokes, ...redexScaffolding, lambdaStroke,
  ].map(({ id }) => id))
  const reflowed = removed.filter((stroke) => (
    !classified.has(stroke.id) && stroke.ownerId !== null && target.nodeIds.has(stroke.ownerId)
  ))
  for (const stroke of reflowed) classified.add(stroke.id)
  const unknown = removed.filter((stroke) => !classified.has(stroke.id))
  if (unknown.length > 0) throw new Error(`unclassified consumed strokes: ${unknown.map(({ id }) => id).join(', ')}`)

  const expectedOrigins = sourceArgument.map(({ id }) => id).sort()
  for (let copyIndex = 0; copyIndex < copies.length; copyIndex++) {
    const actualOrigins = [...new Set((targetCopies.get(copyIndex) ?? []).map(({ originId }) => originId))].sort()
    if (actualOrigins.length !== expectedOrigins.length || actualOrigins.some((origin, index) => origin !== expectedOrigins[index])) {
      throw new Error(
        `beta transition copy ${copyIndex} is not a complete argument stroke set`
        + ` (source: ${expectedOrigins.join(', ')}; copy: ${actualOrigins.join(', ')})`,
      )
    }
  }

  const sourceArgumentPointByOrigin = new Map<string, PointModel>()
  for (const stroke of sourceArgument) {
    for (const point of [stroke.a, stroke.b]) sourceArgumentPointByOrigin.set(point.originId, point)
  }
  const sourceArgumentRoot = asGrid(
    sourceCoord(source.points.get(source.nodeOut(argument))!),
    'source argument root',
  )
  const sourceArgumentPoints = [...sourceArgumentPointByOrigin.values()]
    .map((point) => asGrid(sourceCoord(point), `argument junction ${point.id}`))
  const minArgumentRelativeRow = Math.min(...sourceArgumentPoints.map((point) => point.row - sourceArgumentRoot.row))
  const copyCenter = (Math.max(1, copies.length) - 1) / 2
  const copyStages = new Map<number, CopyStage>()
  for (const occurrence of copies) {
    const targetRoot = socketByCopy.get(occurrence.copyIndex)!.targetPoint
    copyStages.set(occurrence.copyIndex, {
      targetRoot,
      stageRoot: gridCoord(
        targetRoot.col,
        -view.railRows - 1 + 0.35 - minArgumentRelativeRow
          + Math.abs(occurrence.copyIndex - copyCenter) * 0.55,
      ),
    })
  }

  const targetBox = target.nodeBoxes.get(targetReduct.id)
  if (targetBox === undefined) throw new Error(`target reduct '${targetReduct.id}' has no layout box`)
  const socketPoints = [...socketByCopy.values()].map(({ targetPoint }) => targetPoint)
  const targetBinderRow = Math.min(targetBox.top, ...socketPoints.map(({ row }) => row)) - 0.72
  const targetBinderLeft = Math.min(targetBox.left + view.targetOffset, ...socketPoints.map(({ col }) => col))
  const targetBinderRight = Math.max(targetBox.right + view.targetOffset, ...socketPoints.map(({ col }) => col))

  const persistentPointIds = new Set(pairs.flatMap((pair) => [pair.source.a.id, pair.source.b.id]))
  const persistentJunctions = [...persistentPointIds].map((sourceId): LambdaJunctionCorrespondence => {
    const sourcePoint = source.points.get(sourceId)!
    const destination = targetOfSource.get(sourceId)
    if (destination === undefined) throw new Error(`persistent junction '${sourceId}' has no destination`)
    return {
      sourceId,
      source: mapCoord(sourceCoord(sourcePoint), view),
      target: mapCoord(destination, view),
    }
  })

  return {
    motion: {
      source, target, view, pairs, sourceArgument, redexScaffolding, lambdaStroke,
      boundStrokes, reflowed, targetCopies, targetOfSource,
      sourceArgumentPointByOrigin, copies, copyStages,
      sourceBodyOut: asGrid(sourceCoord(source.points.get(source.nodeOut(body))!), 'source body output'),
      sourceArgumentRoot,
      sourceLambdaA: asGrid(sourceCoord(lambdaStroke.a), 'source lambda start'),
      sourceLambdaB: asGrid(sourceCoord(lambdaStroke.b), 'source lambda end'),
      targetBinderRow, targetBinderLeft, targetBinderRight,
    },
    persistentJunctions,
  }
}

export function planBetaMotion(source: Term, step: ReductionStep): LambdaMotionPlan {
  if (step.kind !== 'beta') throw new Error(`Lambda beta motion cannot plan a '${step.kind}' step`)
  const sourceRoot = annotate(source)
  const redex = annotatedAt(sourceRoot, step.path)
  if (redex.kind !== 'application' || redex.fn!.kind !== 'lambda') {
    throw new Error(`no beta redex at path [${step.path.join(', ')}]`)
  }
  const binder = redex.fn!, body = binder.body!, argument = redex.argument!
  const copies: OccurrenceCopy[] = []
  const targetReduct = substituteAnnotated(body, binder.id, argument, copies)
  const targetRoot = replaceAnnotated(sourceRoot, step.path, targetReduct)
  const target = plainTerm(targetRoot)
  const kernelTarget = applyStepAt(source, step)
  if (!termEq(target, kernelTarget)) throw new Error('motion correspondence disagrees with kernel beta substitution')
  const { motion, persistentJunctions } = createMotionModel(
    sourceRoot, targetRoot, redex, binder, body, argument, targetReduct, copies,
  )
  const times: LambdaStageTimes = copies.length > 0
    ? { split: 0.15, liftEnd: 0.34, spaceEnd: 0.54, dockEnd: 0.82, stemEnd: 0.91, barEnd: 0.965 }
    : { split: 0.15, liftEnd: 0.38, spaceEnd: 0.64, dockEnd: 0.64, stemEnd: 0.64, barEnd: 0.93 }
  return {
    source, target, step: { kind: step.kind, path: [...step.path] },
    copyCount: copies.length, times, persistentJunctions, model: motion,
  }
}

export function sampleBetaMotion(
  plan: LambdaMotionPlan,
  progress: number,
  baseColor: string,
): LambdaStrokeFrame {
  if (!Number.isFinite(progress)) throw new Error(`Lambda motion progress must be finite, got ${progress}`)
  const p = clamp(progress), { times, copyCount } = plan, model = plan.model
  if (p === 0) {
    const argumentIds = new Set(model.sourceArgument.map(({ id }) => id))
    const redexIds = new Set([
      model.lambdaStroke,
      ...model.boundStrokes,
      ...model.redexScaffolding,
    ].map(({ id }) => id))
    return {
      phase: 'identify',
      strokes: model.source.strokes.map((stroke) => strokeFrame(
        stroke,
        shifted(stroke.a.coord, model.view.sourceOffset),
        shifted(stroke.b.coord, model.view.sourceOffset),
        model.view,
        baseColor,
        argumentIds.has(stroke.id) ? 'argument' : redexIds.has(stroke.id) ? 'redex' : 'persistent',
      )),
      sockets: [],
    }
  }
  const identify = stageProgress(p, 0, times.split)
  const lift = stageProgress(p, times.split, times.liftEnd)
  const space = stageProgress(p, times.liftEnd, times.spaceEnd)
  const dock = stageProgress(p, times.spaceEnd, times.dockEnd)
  const stem = stageProgress(p, times.dockEnd, times.stemEnd)
  const bar = stageProgress(p, times.stemEnd, times.barEnd)
  const neutral = stageProgress(p, times.barEnd, 1)
  const sourceCoord = (point: PointModel): MotionCoord => shifted(point.coord, model.view.sourceOffset)
  const targetCoord = (point: PointModel): MotionCoord => shifted(point.coord, model.view.targetOffset)
  const movingSource = (point: PointModel, amount: number): MotionCoord => {
    const destination = model.targetOfSource.get(point.id)
    return destination === undefined ? sourceCoord(point) : interpolateCoord(sourceCoord(point), destination, amount)
  }
  const strokes: LambdaStroke[] = []
  const push = (
    source: StrokeModel,
    a: MotionCoord,
    b: MotionCoord,
    color: string,
    lineage: LambdaStrokeLineage,
  ): void => { strokes.push(strokeFrame(source, a, b, model.view, color, lineage)) }

  for (const pair of model.pairs) {
    push(pair.source, movingSource(pair.source.a, space), movingSource(pair.source.b, space), baseColor, 'persistent')
  }

  const binderRow = mix(model.sourceLambdaA.row, model.targetBinderRow, space)
  const binderLeft = mix(model.sourceLambdaA.col, model.targetBinderLeft, space)
  const binderRight = mix(model.sourceLambdaB.col, model.targetBinderRight, space)
  const binderCenter = (binderLeft + binderRight) / 2
  if (bar < 0.9999) {
    push(
      model.lambdaStroke,
      gridCoord(mix(binderLeft, binderCenter, bar), binderRow),
      gridCoord(mix(binderRight, binderCenter, bar), binderRow),
      mixColor(baseColor, REDEX_COLOR, identify),
      'redex',
    )
  }

  const sockets: LambdaSocket[] = []
  for (const occurrence of model.copies) {
    const sourcePoint = model.source.points.get(`${occurrence.sourceVarId}:out`)!
    const socketCoord = asGrid(movingSource(sourcePoint, space), `socket ${occurrence.copyIndex}`)
    const top = gridCoord(socketCoord.col, binderRow)
    const bottom = gridCoord(mix(socketCoord.col, top.col, stem), mix(socketCoord.row, top.row, stem))
    const boundStroke = model.boundStrokes.find(({ ownerId }) => ownerId === occurrence.sourceVarId)
    if (boundStroke === undefined) throw new Error(`missing bound-variable stem ${occurrence.sourceVarId}`)
    if (stem < 0.9999) push(boundStroke, top, bottom, REDEX_COLOR, 'redex')
    sockets.push({
      copyIndex: occurrence.copyIndex,
      sourceOccurrenceId: occurrence.sourceVarId,
      point: mapCoord(socketCoord, model.view),
      amount: (1 - dock) * 0.72 + (1 - stem) * 0.18,
    })
  }

  const collapseToBody = (coord: MotionCoord): MotionCoord => {
    const point = asGrid(coord, 'consumed stroke point')
    return gridCoord(
      model.sourceBodyOut.col + (point.col - model.sourceBodyOut.col) * (1 - lift),
      model.sourceBodyOut.row + (point.row - model.sourceBodyOut.row) * (1 - lift),
    )
  }
  if (p < times.split) {
    const scaffoldColor = mixColor(baseColor, REDEX_COLOR, identify)
    for (const stroke of model.redexScaffolding) {
      push(stroke, sourceCoord(stroke.a), sourceCoord(stroke.b), scaffoldColor, 'redex')
    }
    const argumentColor = mixColor(baseColor, ARGUMENT_COLOR, identify)
    for (const stroke of model.sourceArgument) {
      push(stroke, sourceCoord(stroke.a), sourceCoord(stroke.b), argumentColor, 'argument')
    }
  } else {
    if (lift < 0.9999) {
      for (const stroke of model.redexScaffolding) {
        push(stroke, collapseToBody(sourceCoord(stroke.a)), collapseToBody(sourceCoord(stroke.b)), REDEX_COLOR, 'redex')
      }
      if (copyCount === 0) {
        const color = mixColor(ARGUMENT_COLOR, REDEX_COLOR, lift)
        for (const stroke of model.sourceArgument) {
          push(stroke, collapseToBody(sourceCoord(stroke.a)), collapseToBody(sourceCoord(stroke.b)), color, 'argument')
        }
      }
    }
  }

  if (space < 0.9999) {
    for (const stroke of model.reflowed) {
      push(
        stroke,
        interpolateCoord(sourceCoord(stroke.a), gridCoord(model.sourceBodyOut.col, model.sourceBodyOut.row), space),
        interpolateCoord(sourceCoord(stroke.b), gridCoord(model.sourceBodyOut.col, model.sourceBodyOut.row), space),
        baseColor,
        'persistent',
      )
    }
  }

  if (copyCount > 0 && p >= times.split) {
    for (let copyIndex = 0; copyIndex < copyCount; copyIndex++) {
      const stage = model.copyStages.get(copyIndex)!
      const hue = mixColor(copyHue(copyIndex), baseColor, neutral)
      const pointAt = (targetPoint: PointModel): MotionCoord => {
        const target = asGrid(targetCoord(targetPoint), `target copy junction ${targetPoint.id}`)
        const sourcePoint = model.sourceArgumentPointByOrigin.get(targetPoint.originId)
          ?? model.source.pointsByOrigin.get(targetPoint.originId)
          ?? (targetPoint.originId.endsWith(':bind')
            ? model.source.pointsByOrigin.get(`${targetPoint.originId.slice(0, -':bind'.length)}:out`)
            : undefined)
        if (sourcePoint === undefined) {
          throw new Error(`copy junction ${targetPoint.id} has no source junction ${targetPoint.originId}`)
        }
        const start = asGrid(sourceCoord(sourcePoint), `copy source junction ${sourcePoint.id}`)
        const sourceRelative = gridCoord(start.col - model.sourceArgumentRoot.col, start.row - model.sourceArgumentRoot.row)
        const targetRelative = gridCoord(target.col - stage.targetRoot.col, target.row - stage.targetRoot.row)
        if (p < times.liftEnd) {
          return gridCoord(
            start.col + (stage.stageRoot.col - model.sourceArgumentRoot.col) * lift,
            start.row + (stage.stageRoot.row - model.sourceArgumentRoot.row) * lift,
          )
        }
        if (p < times.spaceEnd) {
          return gridCoord(
            stage.stageRoot.col + mix(sourceRelative.col, targetRelative.col, space),
            stage.stageRoot.row + mix(sourceRelative.row, targetRelative.row, space),
          )
        }
        return gridCoord(
          mix(stage.stageRoot.col, stage.targetRoot.col, dock) + targetRelative.col,
          mix(stage.stageRoot.row, stage.targetRoot.row, dock) + targetRelative.row,
        )
      }
      const color = p < times.liftEnd ? mixColor(ARGUMENT_COLOR, copyHue(copyIndex), lift) : hue
      for (const stroke of model.targetCopies.get(copyIndex) ?? []) {
        push(stroke, pointAt(stroke.a), pointAt(stroke.b), color, 'copy')
      }
    }
  }

  return { phase: phaseAt(copyCount, times, p), strokes, sockets }
}
