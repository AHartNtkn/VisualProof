import { createHash } from 'node:crypto'
import { existsSync, readdirSync, readFileSync, statSync } from 'node:fs'
import { resolve, relative } from 'node:path'
import { describe, expect, it } from 'vitest'

type Point = readonly [number, number]

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
    readonly bounds: { readonly x: number; readonly y: number; readonly width: number; readonly height: number }
  }>>
}

type StrokeRaster = {
  readonly screenPoints: readonly Point[]
  readonly lineWidth: number
  readonly screenLength: number
  readonly matchingPixels: number
  readonly bestColorDistance: number
  readonly eligiblePixels: number
  readonly requiredMatchingPixels: number
  readonly groupId: string
  readonly groupMemberIds: readonly string[]
  readonly topPieceId: string
  readonly targetColor: string
  readonly coverageByMember: Readonly<Record<string, number>>
  readonly occludedByPieceIds: readonly string[]
  readonly occlusionCoverage: number
}

type StrokeCurve = {
  readonly normalizedPoints: readonly Point[]
  readonly normalizedLength: number
  readonly normalizedExtent: number
  readonly rawPointCount: number
}

type ReferencePaint = {
  readonly source: 'live-canvas-context'
  readonly commands: readonly { readonly kind?: string }[]
  readonly devicePoints: readonly Point[]
  readonly cssPoints: readonly Point[]
  readonly lineWidth: number
  readonly lineCap: string
  readonly lineJoin: string
  readonly transform: readonly [number, number, number, number, number, number]
}

type StrokeObservation = {
  readonly pieceId: string
  readonly address: string
  readonly sourceStrokeId: string
  readonly renderRole: string
  readonly role: string
  readonly lineage: 'persistent' | 'redex' | 'argument' | 'copy'
  readonly copyIndex: number | null
  readonly rendererOnly: boolean
  readonly junctions: readonly [string, string]
  readonly destinations: readonly [string | null, string | null]
  readonly points: readonly [Point, Point]
  readonly color: string
  readonly curve: StrokeCurve
  readonly paint: ReferencePaint | null
  readonly raster: StrokeRaster
}

type FrameObservations = {
  readonly source: 'live-reference-transition' | 'application-2d-paint' | 'presented-webgl-entities'
  readonly baseColor: string
  readonly strokes: readonly StrokeObservation[]
}

type FrameEvidence = {
  readonly progress: number
  readonly sample: 'boundary' | 'midpoint'
  readonly phase: string
  readonly image: string
  readonly imageSha256: string
  readonly structural: StructuralFrame
  readonly raster: RasterFrame
  readonly observations: FrameObservations
  readonly twoD?: TwoDFrame
  readonly threeD?: ThreeDFrame
}

type ModeEvidence = {
  readonly sourceDimensions: { readonly width: number; readonly height: number }
  readonly backingDimensions: { readonly width: number; readonly height: number }
  readonly crop: { readonly x: number; readonly y: number; readonly width: number; readonly height: number }
  readonly contactSheet: string
  readonly contactSheetSha256: string
  readonly frames: readonly FrameEvidence[]
}

type Manifest = {
  readonly schema: 1
  readonly outputDirectory: string
  readonly reference: { readonly path: string; readonly sha256: string }
  readonly application: { readonly commit: string; readonly sourceHash: string }
  readonly palette: {
    readonly redex: string
    readonly argument: string
    readonly copies: readonly string[]
    readonly referenceBase: string
    readonly lightBase: string
    readonly darkBase: string
  }
  readonly rendererLayering: Readonly<Record<'light' | 'dark', {
    readonly lambdaPixel: readonly number[]
    readonly pipPixel: readonly number[]
    readonly combinedPixel: readonly number[]
    readonly pipDistance: number
    readonly lambdaDistance: number
  }>>
  readonly examples: readonly {
    readonly key: string
    readonly source: string
    readonly copyCount: number
    readonly boundaries: readonly number[]
    readonly correspondence: {
      readonly argumentStrokeAddresses: readonly string[]
      readonly argumentRootJunction: string
    }
    readonly modes: Readonly<Record<'reference' | '2d-light' | '3d-light' | '3d-dark', ModeEvidence>>
  }[]
}

const OUTPUT = resolve(process.env['VPA_LAMBDA_COMPARISON_DIR'] ?? '/tmp/vpa-lambda-comparison')
const MANIFEST_PATH = resolve(OUTPUT, 'manifest.json')
const ROOT = resolve(import.meta.dirname, '../..')
const EXPECTED = [
  { key: 'one-use', copies: 1, boundaries: [0, 0.15, 0.34, 0.54, 0.82, 0.91, 0.965, 1] },
  { key: 'duplication', copies: 2, boundaries: [0, 0.15, 0.34, 0.54, 0.82, 0.91, 0.965, 1] },
  { key: 'deletion', copies: 0, boundaries: [0, 0.15, 0.38, 0.64, 0.93, 1] },
  { key: 'nested-binder', copies: 1, boundaries: [0, 0.15, 0.34, 0.54, 0.82, 0.91, 0.965, 1] },
  { key: 'capture-avoidance', copies: 1, boundaries: [0, 0.15, 0.34, 0.54, 0.82, 0.91, 0.965, 1] },
] as const
const MODES = ['reference', '2d-light', '3d-light', '3d-dark'] as const

const sha256 = (bytes: Buffer): string => createHash('sha256').update(bytes).digest('hex')
const close = (actual: number, expected: number, tolerance = 1e-10): boolean =>
  Math.abs(actual - expected) <= tolerance

function sourceHash(): string {
  const files: string[] = []
  const visit = (directory: string): void => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const path = resolve(directory, entry.name)
      if (entry.isDirectory()) visit(path)
      else if (entry.isFile()) files.push(path)
    }
  }
  for (const directory of ['src', 'app']) visit(resolve(ROOT, directory))
  for (const file of ['package.json', 'package-lock.json']) files.push(resolve(ROOT, file))
  const digest = createHash('sha256')
  for (const file of files.sort()) {
    digest.update(relative(ROOT, file)).update('\0').update(sha256(readFileSync(file))).update('\n')
  }
  return digest.digest('hex')
}

function currentGitHead(): string {
  const dotGit = resolve(ROOT, '.git')
  const marker = statSync(dotGit).isDirectory() ? '' : readFileSync(dotGit, 'utf8').trim()
  const gitDirectory = marker.startsWith('gitdir:') ? resolve(ROOT, marker.slice('gitdir:'.length).trim()) : dotGit
  const commonMarker = resolve(gitDirectory, 'commondir')
  const commonDirectory = existsSync(commonMarker)
    ? resolve(gitDirectory, readFileSync(commonMarker, 'utf8').trim())
    : gitDirectory
  const head = readFileSync(resolve(gitDirectory, 'HEAD'), 'utf8').trim()
  if (!head.startsWith('ref:')) return head
  const reference = head.slice('ref:'.length).trim()
  for (const base of [gitDirectory, commonDirectory]) {
    const loose = resolve(base, reference)
    if (existsSync(loose)) return readFileSync(loose, 'utf8').trim()
  }
  const packed = resolve(commonDirectory, 'packed-refs')
  if (existsSync(packed)) {
    const match = readFileSync(packed, 'utf8').split('\n').find((line) => line.endsWith(` ${reference}`))
    if (match !== undefined) return match.slice(0, match.indexOf(' '))
  }
  throw new Error(`cannot resolve ${reference} from repository metadata`)
}

function samples(boundaries: readonly number[]): readonly { progress: number; sample: 'boundary' | 'midpoint' }[] {
  return boundaries.flatMap((progress, index) => index === boundaries.length - 1
    ? [{ progress, sample: 'boundary' as const }]
    : [
        { progress, sample: 'boundary' as const },
        { progress: (progress + boundaries[index + 1]!) / 2, sample: 'midpoint' as const },
      ])
}

function at(frames: readonly FrameEvidence[], progress: number): FrameEvidence {
  const frame = frames.find((candidate) => close(candidate.progress, progress))
  if (frame === undefined) throw new Error(`missing frame at ${progress}`)
  return frame
}

function expectedPhase(copyCount: number, boundaries: readonly number[], progress: number): string {
  if (copyCount === 0) {
    if (progress < boundaries[1]!) return 'identify'
    if (progress < boundaries[2]!) return 'discard'
    if (progress < boundaries[3]!) return 'make-space'
    if (progress < boundaries[4]!) return 'cleanup'
    return 'settle'
  }
  if (progress < boundaries[1]!) return 'identify'
  if (progress < boundaries[2]!) return 'duplicate'
  if (progress < boundaries[3]!) return 'make-space'
  if (progress < boundaries[4]!) return 'substitute'
  if (progress < boundaries[6]!) return 'cleanup'
  return 'settle'
}

function minCentroidSeparation(copies: StructuralFrame['copies']): number {
  let minimum = Infinity
  for (let left = 0; left < copies.length; left += 1) {
    for (let right = left + 1; right < copies.length; right += 1) {
      minimum = Math.min(minimum, Math.hypot(
        copies[left]!.centroid[0] - copies[right]!.centroid[0],
        copies[left]!.centroid[1] - copies[right]!.centroid[1],
      ))
    }
  }
  return minimum
}

const semanticStrokes = (frame: FrameEvidence): readonly StrokeObservation[] =>
  frame.observations.strokes.filter(({ rendererOnly }) => !rendererOnly)

function groupsOf(frame: FrameEvidence): Map<string, StrokeObservation[]> {
  const groups = new Map<string, StrokeObservation[]>()
  for (const stroke of semanticStrokes(frame)) {
    const group = groups.get(stroke.address) ?? []
    group.push(stroke)
    groups.set(stroke.address, group)
  }
  return groups
}

function junctionPositions(strokes: readonly StrokeObservation[]): Map<string, Point> {
  const positions = new Map<string, Point>()
  for (const stroke of strokes) {
    stroke.junctions.forEach((junction, index) => {
      const point = stroke.points[index]!
      const previous = positions.get(junction)
      if (previous !== undefined) {
        expect(pointDistance(previous, point), `junction ${junction} split inside one rendered frame`).toBeLessThan(1e-6)
      } else positions.set(junction, point)
    })
  }
  return positions
}

function junctionDestinations(strokes: readonly StrokeObservation[]): Map<string, string> {
  const destinations = new Map<string, string>()
  for (const stroke of strokes) stroke.junctions.forEach((junction, index) => {
    const destination = stroke.destinations[index]
    if (destination === null || destination === undefined) {
      throw new Error(`persistent/copy junction ${junction} has no destination correspondence`)
    }
    const previous = destinations.get(junction)
    if (previous !== undefined) expect(destination, `junction ${junction} has conflicting destinations`).toBe(previous)
    else destinations.set(junction, destination)
  })
  return destinations
}

function pointDistance(left: Point, right: Point): number {
  return Math.hypot(left[0] - right[0], left[1] - right[1])
}

function polylineLength(points: readonly Point[]): number {
  return points.slice(1).reduce((sum, point, index) => sum + pointDistance(points[index]!, point), 0)
}

function resamplePolyline(points: readonly Point[], count: number): Point[] {
  if (points.length === 0) return []
  if (points.length === 1) return Array.from({ length: count }, () => points[0]!)
  const cumulative = [0]
  for (let index = 1; index < points.length; index += 1) {
    cumulative.push(cumulative[index - 1]! + pointDistance(points[index - 1]!, points[index]!))
  }
  const total = cumulative.at(-1)!
  if (total < 1e-9) return Array.from({ length: count }, () => points[0]!)
  let segment = 1
  return Array.from({ length: count }, (_, sample): Point => {
    const target = total * sample / (count - 1)
    while (segment < points.length - 1 && cumulative[segment]! < target) segment += 1
    const span = cumulative[segment]! - cumulative[segment - 1]!
    const amount = span === 0 ? 0 : (target - cumulative[segment - 1]!) / span
    return [
      points[segment - 1]![0] + (points[segment]![0] - points[segment - 1]![0]) * amount,
      points[segment - 1]![1] + (points[segment]![1] - points[segment - 1]![1]) * amount,
    ]
  })
}

function framePixelsPerSemanticUnit(frame: FrameEvidence): number {
  const ratios = semanticStrokes(frame).flatMap((stroke) => {
    const semanticSpan = pointDistance(stroke.points[0], stroke.points[1])
    const screenPoints = stroke.raster.screenPoints
    const screenSpan = screenPoints.length < 2 ? 0 : pointDistance(screenPoints[0]!, screenPoints.at(-1)!)
    return semanticSpan > 1e-7 && screenSpan > 1e-7 ? [screenSpan / semanticSpan] : []
  }).sort((left, right) => left - right)
  if (ratios.length === 0) throw new Error(`frame ${frame.progress} has no semantic scale witness`)
  return ratios[Math.floor(ratios.length / 2)]!
}

function semanticComponentPath(
  screenPoints: readonly Point[],
  semanticFrom: Point,
  semanticTo: Point,
  pixelsPerSemanticUnit: number,
): Point[] {
  const source = resamplePolyline(screenPoints, 33)
  if (source.length === 0) return []
  const screenFrom = source[0]!, screenTo = source.at(-1)!
  const semanticSpan = pointDistance(semanticFrom, semanticTo)
  const screenSpan = pointDistance(screenFrom, screenTo)
  if (semanticSpan > 1e-7 && screenSpan > 1e-7) {
    const screenX: Point = [(screenTo[0] - screenFrom[0]) / screenSpan, (screenTo[1] - screenFrom[1]) / screenSpan]
    const semanticX: Point = [
      (semanticTo[0] - semanticFrom[0]) / semanticSpan,
      (semanticTo[1] - semanticFrom[1]) / semanticSpan,
    ]
    return source.map((point): Point => {
      const delta: Point = [point[0] - screenFrom[0], point[1] - screenFrom[1]]
      const parallel = (delta[0] * screenX[0] + delta[1] * screenX[1]) * semanticSpan / screenSpan
      const perpendicular = (-delta[0] * screenX[1] + delta[1] * screenX[0]) * semanticSpan / screenSpan
      return [
        semanticFrom[0] + parallel * semanticX[0] - perpendicular * semanticX[1],
        semanticFrom[1] + parallel * semanticX[1] + perpendicular * semanticX[0],
      ]
    })
  }
  const next = source.find((point) => pointDistance(point, screenFrom) > 1e-7) ?? screenFrom
  const angle = Math.atan2(next[1] - screenFrom[1], next[0] - screenFrom[0])
  const cosine = Math.cos(angle), sine = Math.sin(angle)
  return source.map((point): Point => {
    const x = point[0] - screenFrom[0], y = point[1] - screenFrom[1]
    return [(x * cosine + y * sine) / pixelsPerSemanticUnit, (-x * sine + y * cosine) / pixelsPerSemanticUnit]
  })
}

function canonicalSemanticCurve(frame: FrameEvidence, strokes: readonly StrokeObservation[]): Point[] {
  const pixelsPerSemanticUnit = framePixelsPerSemanticUnit(frame)
  const byRasterGroup = new Map<string, StrokeObservation[]>()
  for (const stroke of strokes) {
    const members = byRasterGroup.get(stroke.raster.groupId) ?? []
    members.push(stroke)
    byRasterGroup.set(stroke.raster.groupId, members)
  }
  const components = [...byRasterGroup.values()].flatMap((members) => {
    const topPieceId = members[0]!.raster.topPieceId
    const top = frame.observations.strokes.find(({ pieceId }) => pieceId === topPieceId) ?? members[0]!
    if (top.raster.screenLength < 1e-7) return []
    const degree = new Map<string, number>(), positions = new Map<string, Point>()
    for (const member of members) member.junctions.forEach((junction, endpoint) => {
      degree.set(junction, (degree.get(junction) ?? 0) + 1)
      positions.set(junction, member.points[endpoint]!)
    })
    const terminals = [...degree].filter(([, count]) => count % 2 === 1).map(([junction]) => junction).sort()
    const from = terminals[0] ?? members[0]!.junctions[0]
    const to = terminals[1] ?? members[0]!.junctions[1]
    return [{
      junctions: [from, to] as const,
      points: semanticComponentPath(top.raster.screenPoints, positions.get(from)!, positions.get(to)!, pixelsPerSemanticUnit),
    }]
  })
  if (components.length === 0) return []
  const degree = new Map<string, number>()
  for (const component of components) for (const junction of component.junctions) {
    degree.set(junction, (degree.get(junction) ?? 0) + 1)
  }
  const terminals = [...degree].filter(([, count]) => count % 2 === 1).map(([junction]) => junction).sort()
  let junction = terminals[0] ?? components[0]!.junctions[0]
  const unused = new Set(components.map((_, index) => index)), composed: Point[] = []
  while (unused.size > 0) {
    const index = [...unused].find((candidate) => components[candidate]!.junctions.includes(junction))
    if (index === undefined) return []
    unused.delete(index)
    const component = components[index]!
    const reverse = component.junctions[1] === junction
    const points = reverse ? [...component.points].reverse() : component.points
    composed.push(...(composed.length === 0 ? points : points.slice(1)))
    junction = reverse ? component.junctions[0] : component.junctions[1]
  }
  if (composed.length < 2) return composed
  const first = composed[0]!, last = composed.at(-1)!, span = pointDistance(first, last)
  const direction = span > 1e-7
    ? [((last[0] - first[0]) / span), ((last[1] - first[1]) / span)] as const
    : (() => {
        const next = composed.find((point) => pointDistance(point, first) > 1e-7) ?? first
        const distance = Math.max(pointDistance(first, next), 1e-7)
        return [(next[0] - first[0]) / distance, (next[1] - first[1]) / distance] as const
      })()
  return composed.map((point): Point => {
    const x = point[0] - first[0], y = point[1] - first[1], scale = span > 1e-7 ? span : 1
    return [(x * direction[0] + y * direction[1]) / scale, (-x * direction[1] + y * direction[0]) / scale]
  })
}

function curveExtent(points: readonly Point[]): number {
  if (points.length === 0) return 0
  const xs = points.map(([x]) => x), ys = points.map(([, y]) => y)
  return Math.hypot(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys))
}

function composedCurveError(reference: readonly Point[], actual: readonly Point[]): number {
  const left = resamplePolyline(reference, 65), right = resamplePolyline(actual, 65)
  if (left.length === 0 || right.length === 0) return Infinity
  const variants = [right, [...right].reverse()].flatMap((candidate) => [
    candidate,
    candidate.map(([x, y]): Point => [x, -y]),
  ])
  return Math.min(...variants.map((candidate) => Math.max(...left.map((point, index) => (
    pointDistance(point, candidate[index]!)
  )))))
}

type CurveAcceptance = {
  readonly accepted: boolean
  readonly serializedLengthRatio: number
  readonly serializedExtentRatio: number
  readonly semanticLengthRatio: number
  readonly semanticExtentRatio: number
  readonly semanticShapeError: number
}

function correspondenceCurveAcceptance(
  referenceFrame: FrameEvidence,
  referenceGroup: readonly StrokeObservation[],
  actualFrame: FrameEvidence,
  actualGroup: readonly StrokeObservation[],
  mode: '2d-light' | '3d-light' | '3d-dark',
): CurveAcceptance {
  const referenceLength = referenceGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedLength, 0)
  const actualLength = actualGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedLength, 0)
  const referenceExtent = referenceGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedExtent, 0)
  const actualExtent = actualGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedExtent, 0)
  const referenceCurve = canonicalSemanticCurve(referenceFrame, referenceGroup)
  const actualCurve = canonicalSemanticCurve(actualFrame, actualGroup)
  const referenceSemanticLength = polylineLength(referenceCurve), actualSemanticLength = polylineLength(actualCurve)
  const referenceSemanticExtent = curveExtent(referenceCurve), actualSemanticExtent = curveExtent(actualCurve)
  if (referenceLength < 1e-6 || referenceSemanticLength < 1e-6) return {
    accepted: actualLength < 1e-6 && actualSemanticLength < 1e-6,
    serializedLengthRatio: actualLength / Math.max(referenceLength, 1e-12),
    serializedExtentRatio: actualExtent / Math.max(referenceExtent, 1e-12),
    semanticLengthRatio: actualSemanticLength / Math.max(referenceSemanticLength, 1e-12),
    semanticExtentRatio: actualSemanticExtent / Math.max(referenceSemanticExtent, 1e-12),
    semanticShapeError: actualSemanticLength < 1e-6 ? 0 : Infinity,
  }
  const serializedLengthRatio = actualLength / referenceLength
  const serializedExtentRatio = actualExtent / referenceExtent
  const semanticLengthRatio = actualSemanticLength / referenceSemanticLength
  const semanticExtentRatio = actualSemanticExtent / referenceSemanticExtent
  const semanticShapeError = composedCurveError(referenceCurve, actualCurve)
  // Current correct live/application evidence occupies 0.689–2.142 in the
  // producer's renderer-local serialized scale. This narrow corroborating
  // envelope has 6% headroom and rejects the cited 0.259 collapsed mutation.
  const serialized = serializedLengthRatio >= 0.65 && serializedLengthRatio <= 2.25
    && serializedExtentRatio >= 0.65 && serializedExtentRatio <= 2.25
  // Semantic junction-frame normalization removes layout scale/orientation.
  // Current 2D evidence is 0.818–1.006 length, 0.950–1.001 extent, <=0.166
  // interior error; projected 3D is 0.750–1.021, 0.928–1.006, <=0.292.
  const limits = mode === '2d-light'
    ? { length: [0.78, 1.05], extent: [0.92, 1.03], shape: 0.20 }
    : { length: [0.70, 1.08], extent: [0.89, 1.04], shape: 0.34 }
  return {
    accepted: serialized
      && semanticLengthRatio >= limits.length[0]! && semanticLengthRatio <= limits.length[1]!
      && semanticExtentRatio >= limits.extent[0]! && semanticExtentRatio <= limits.extent[1]!
      && semanticShapeError <= limits.shape,
    serializedLengthRatio,
    serializedExtentRatio,
    semanticLengthRatio,
    semanticExtentRatio,
    semanticShapeError,
  }
}

function pointSegmentDistance(point: Point, from: Point, to: Point): number {
  const dx = to[0] - from[0], dy = to[1] - from[1], squared = dx * dx + dy * dy
  const amount = squared === 0 ? 0 : Math.max(0, Math.min(1,
    ((point[0] - from[0]) * dx + (point[1] - from[1]) * dy) / squared))
  return pointDistance(point, [from[0] + dx * amount, from[1] + dy * amount])
}

function pathDistance(point: Point, path: readonly Point[]): number {
  if (path.length < 2) return path.length === 0 ? Infinity : pointDistance(point, path[0]!)
  return Math.min(...path.slice(1).map((to, index) => pointSegmentDistance(point, path[index]!, to)))
}

function unionPathCoverage(
  source: readonly Point[],
  targets: readonly { readonly path: readonly Point[]; readonly radius: number }[],
  sourceRadius = 0,
): number {
  if (source.length === 0 || targets.length === 0) return 0
  const centerline = resamplePolyline(source, Math.max(2, Math.ceil(polylineLength(source) / 0.5) + 1))
  const samples = centerline.flatMap((center) => [center, ...[0.5, 1].flatMap((radial) => (
    Array.from({ length: 16 }, (_, index): Point => {
      const angle = index * Math.PI * 2 / 16
      return [center[0] + Math.cos(angle) * sourceRadius * radial, center[1] + Math.sin(angle) * sourceRadius * radial]
    })
  ))])
  return samples.filter((point) => targets.some((target) => pathDistance(point, target.path) <= target.radius + 1e-6)).length
    / samples.length
}

function rasterGroups(frame: FrameEvidence): Map<string, StrokeObservation[]> {
  const groups = new Map<string, StrokeObservation[]>()
  for (const stroke of frame.observations.strokes) {
    const group = groups.get(stroke.raster.groupId) ?? []
    group.push(stroke)
    groups.set(stroke.raster.groupId, group)
  }
  return groups
}

function topologyTerminals(strokes: readonly StrokeObservation[]): string[] {
  const degree = new Map<string, number>()
  for (const { junctions: [left, right] } of strokes) {
    if (left === right) continue
    degree.set(left, (degree.get(left) ?? 0) + 1)
    degree.set(right, (degree.get(right) ?? 0) + 1)
  }
  return [...degree].filter(([, count]) => count % 2 === 1).map(([junction]) => junction).sort()
}

function componentCount(strokes: readonly StrokeObservation[]): number {
  const endpoints = strokes.flatMap((stroke, strokeIndex) => stroke.junctions.map((junction, endpointIndex) => ({
    id: `${strokeIndex}:${endpointIndex}`,
    junction,
    point: stroke.points[endpointIndex]!,
  })))
  const parent = new Map(endpoints.map(({ id }) => [id, id]))
  const root = (value: string): string => {
    const current = parent.get(value)
    if (current === undefined) throw new Error(`unknown topology endpoint ${value}`)
    if (current === value) return value
    const resolved = root(current)
    parent.set(value, resolved)
    return resolved
  }
  const union = (left: string, right: string): void => {
    const leftRoot = root(left), rightRoot = root(right)
    if (leftRoot !== rightRoot) parent.set(rightRoot, leftRoot)
  }
  for (let strokeIndex = 0; strokeIndex < strokes.length; strokeIndex += 1) {
    union(`${strokeIndex}:0`, `${strokeIndex}:1`)
  }
  for (let left = 0; left < endpoints.length; left += 1) for (let right = left + 1; right < endpoints.length; right += 1) {
    const a = endpoints[left]!, b = endpoints[right]!
    if (pointDistance(a.point, b.point) < 1e-6) union(a.id, b.id)
  }
  return new Set([...parent.keys()].map(root)).size
}

const colorRgb = (hex: string): readonly [number, number, number] => {
  const value = Number.parseInt(hex.slice(1), 16)
  return [value >> 16, (value >> 8) & 255, value & 255]
}

const smoothStage = (value: number): number => {
  const amount = Math.max(0, Math.min(1, value))
  return amount * amount * (3 - 2 * amount)
}

function mixColor(from: string, to: string, amount: number): string {
  const left = colorRgb(from), right = colorRgb(to), progress = Math.max(0, Math.min(1, amount))
  const channels = left.map((channel, index) => Math.round(channel + (right[index]! - channel) * progress))
  return `#${channels.map((channel) => channel.toString(16).padStart(2, '0')).join('')}`
}

function singleColor(group: readonly StrokeObservation[], context: string): string {
  const colors = [...new Set(group.map(({ color }) => color.toLowerCase()))]
  expect(colors, `${context} has inconsistent per-piece colors`).toHaveLength(1)
  return colors[0]!
}

const copyPrefix = (copyIndex: number): string => `copy:${copyIndex}:`

function copyRoot(frame: FrameEvidence, copyIndex: number, argumentRootJunction: string): Point {
  const position = junctionPositions(
    semanticStrokes(frame).filter(({ copyIndex: index }) => index === copyIndex),
  ).get(`${copyPrefix(copyIndex)}${argumentRootJunction}`)
  if (position === undefined) throw new Error(`copy ${copyIndex} has no correspondence-addressable root`)
  return position
}

function normalizedStageFraction(point: Point, start: Point, end: Point): { readonly amount: number; readonly offAxis: number } {
  const delta: Point = [end[0] - start[0], end[1] - start[1]]
  const norm = delta[0] * delta[0] + delta[1] * delta[1]
  if (norm < 1e-10) throw new Error('stage endpoints do not move')
  const relative: Point = [point[0] - start[0], point[1] - start[1]]
  const amount = (relative[0] * delta[0] + relative[1] * delta[1]) / norm
  const projected: Point = [start[0] + amount * delta[0], start[1] + amount * delta[1]]
  return { amount, offAxis: pointDistance(point, projected) / Math.sqrt(norm) }
}

function explicitSubdivisionJunctions(
  reference: readonly StrokeObservation[],
  actual: readonly StrokeObservation[],
  context: string,
): void {
  const referenceJunctions = new Set(reference.flatMap(({ junctions }) => junctions))
  const occurrences = new Map<string, { readonly point: Point; readonly address: string }[]>()
  for (const stroke of actual) stroke.junctions.forEach((junction, index) => {
    if (referenceJunctions.has(junction)) return
    const values = occurrences.get(junction) ?? []
    values.push({ point: stroke.points[index]!, address: stroke.address })
    occurrences.set(junction, values)
  })
  for (const [junction, values] of occurrences) {
    expect(values, `${context} has an unmatched non-degree-two junction ${junction}`).toHaveLength(2)
    expect(new Set(values.map(({ address }) => address)).size, `${context} subdivision crosses semantic strokes`).toBe(1)
    expect(values[0]!.address.endsWith(':free-drop'), `${context} has an unrecognized subdivision ${junction}`).toBe(true)
    expect(junction, `${context} has an unrecognized subdivision identity`).toBe(
      values[0]!.address.replace(/:free-drop$/u, ':bind'),
    )
    expect(pointDistance(values[0]!.point, values[1]!.point), `${context} subdivision ${junction} is split`).toBeLessThan(1e-6)
  }
}

function expectedStrokeColor(
  frame: FrameEvidence,
  stroke: StrokeObservation,
  boundaries: readonly number[],
  palette: Manifest['palette'],
): string {
  const [start, split, liftEnd] = boundaries
  const barEnd = boundaries.at(-2)!
  const progress = frame.progress
  const base = frame.observations.baseColor.toLowerCase()
  if (progress === 0) return base
  if (stroke.lineage === 'persistent') return base
  if (progress < split!) {
    const accent = stroke.lineage === 'redex' ? palette.redex : palette.argument
    if (stroke.lineage === 'redex' && (stroke.role === 'lambda' || stroke.role === 'variable')) return accent
    return mixColor(base, accent, smoothStage((progress - start!) / (split! - start!)))
  }
  if (stroke.lineage === 'redex') return palette.redex
  const lift = smoothStage((progress - split!) / (liftEnd! - split!))
  if (stroke.lineage === 'argument') return mixColor(palette.argument, palette.redex, lift)
  const copyHue = palette.copies[stroke.copyIndex!]!
  if (progress < liftEnd!) return mixColor(palette.argument, copyHue, lift)
  return mixColor(copyHue, base, smoothStage((progress - barEnd) / (1 - barEnd)))
}

function assertEvidenceFile(path: string, expectedHash: string): void {
  expect(resolve(path).startsWith(`${OUTPUT}/`), `${path} is outside the evidence directory`).toBe(true)
  expect(statSync(path).size, `${path} is empty`).toBeGreaterThan(0)
  expect(sha256(readFileSync(path)), `${path} changed after capture`).toBe(expectedHash)
}

describe('rendered Lambda comparison', () => {
  const manifest = JSON.parse(readFileSync(MANIFEST_PATH, 'utf8')) as Manifest

  it('rejects the reviewer collapsed-copy-bar manifest mutation', () => {
    const example = manifest.examples.find(({ key }) => key === 'duplication')!
    const reference = at(example.modes.reference.frames, 0.54)
    const actual = structuredClone(at(example.modes['2d-light'].frames, 0.54))
    const address = 'copy:0:root/argument:lambda'
    const referenceGroup = groupsOf(reference).get(address)!
    const actualGroup = groupsOf(actual).get(address)!
    for (const stroke of actualGroup) {
      const mutable = stroke.curve as unknown as { normalizedPoints: Point[]; normalizedLength: number; normalizedExtent: number }
      mutable.normalizedPoints = mutable.normalizedPoints.map(([x, y]) => [x * 0.17, y * 0.17])
      mutable.normalizedLength *= 0.17
      mutable.normalizedExtent *= 0.17
    }
    expect(correspondenceCurveAcceptance(reference, referenceGroup, actual, actualGroup, '2d-light').accepted).toBe(false)
  })

  it('rejects a deformed interior in a multi-piece correspondence group', () => {
    const example = manifest.examples.find(({ key }) => key === 'capture-avoidance')!
    const reference = at(example.modes.reference.frames, 0.15)
    const actual = structuredClone(at(example.modes['2d-light'].frames, 0.15))
    const address = 'copy:0:root/argument:free-drop'
    const referenceGroup = groupsOf(reference).get(address)!
    const actualGroup = groupsOf(actual).get(address)!
    for (const stroke of actualGroup) {
      const points = stroke.raster.screenPoints
      const first = points[0]!, last = points.at(-1)!
      ;(stroke.raster as unknown as { screenPoints: Point[] }).screenPoints = [
        first,
        [(first[0] + last[0]) / 2 + 40, (first[1] + last[1]) / 2 - 40],
        last,
      ]
    }
    expect(correspondenceCurveAcceptance(reference, referenceGroup, actual, actualGroup, '2d-light').accepted).toBe(false)
  })

  it('rejects narrower and offset later strokes as full-tube occluders', () => {
    const source: readonly Point[] = [[0, 0], [20, 0]]
    expect(unionPathCoverage(source, [{ path: source, radius: 1.75 }], 3.75)).toBeLessThan(0.98)
    expect(unionPathCoverage(source, [{ path: [[0, 0.75], [20, 0.75]], radius: 3.75 }], 3.75)).toBeLessThan(0.98)
  })

  it('keeps coincident identity pips above Lambda strokes in both WebGL themes', () => {
    const layering = manifest.rendererLayering
    expect(layering, 'capture omitted the coincident Lambda/pip renderer probe').toBeDefined()
    for (const theme of ['light', 'dark'] as const) {
      expect(layering?.[theme].pipDistance, `${theme} combined pixel did not preserve the pip`).toBeLessThanOrEqual(3)
      expect(layering?.[theme].lambdaDistance, `${theme} combined pixel still matches the Lambda stroke`).toBeGreaterThan(24)
    }
  })

  it('is current, complete evidence from the live authority and current application', () => {
    expect(manifest.schema).toBe(1)
    expect(resolve(manifest.outputDirectory)).toBe(OUTPUT)
    expect(manifest.reference.path).toBe('/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html')
    expect(sha256(readFileSync(manifest.reference.path))).toBe(manifest.reference.sha256)
    expect(currentGitHead()).toBe(manifest.application.commit)
    expect(sourceHash()).toBe(manifest.application.sourceHash)
    expect(manifest.examples.map(({ key }) => key)).toEqual(EXPECTED.map(({ key }) => key))
  })

  for (const expected of EXPECTED) {
    describe(expected.key, () => {
      const example = manifest.examples.find(({ key }) => key === expected.key)!
      const requiredSamples = samples(expected.boundaries)

      it('contains every boundary, midpoint, renderer, and immutable raster', () => {
        expect(example.copyCount).toBe(expected.copies)
        expect(example.boundaries).toEqual(expected.boundaries)
        expect(Object.keys(example.modes).sort()).toEqual([...MODES].sort())
        for (const modeName of MODES) {
          const mode = example.modes[modeName]
          expect(mode.sourceDimensions.width).toBeGreaterThan(0)
          expect(mode.sourceDimensions.height).toBeGreaterThan(0)
          expect(mode.crop.width).toBeGreaterThan(0)
          expect(mode.crop.height).toBeGreaterThan(0)
          expect(mode.frames.map(({ progress, sample }) => ({ progress, sample }))).toEqual(requiredSamples)
          assertEvidenceFile(mode.contactSheet, mode.contactSheetSha256)
          for (const frame of mode.frames) {
            assertEvidenceFile(frame.image, frame.imageSha256)
            expect(frame.phase).toBe(expectedPhase(expected.copies, expected.boundaries, frame.progress))
            expect(frame.structural.copyCount).toBe(expected.copies)
            expect(frame.structural.opaque).toBe(true)
            expect(frame.raster.nonBackgroundPixels).toBeGreaterThan(40)
          }
        }
      })

      it('derives every reference-visible tube from the live Painter canvas path', () => {
        const mode = example.modes.reference
        for (const frame of mode.frames) for (const stroke of semanticStrokes(frame)) {
          if (stroke.curve.normalizedLength < 1e-8) continue
          expect(stroke.paint, `${stroke.pieceId} has no live Canvas paint record`).not.toBeNull()
          const paint = stroke.paint!
          expect(paint.source).toBe('live-canvas-context')
          expect(paint.commands.length).toBeGreaterThan(0)
          expect(paint.devicePoints.length).toBe(stroke.curve.rawPointCount)
          expect(paint.cssPoints).toHaveLength(paint.devicePoints.length)
          expect(paint.lineWidth).toBeGreaterThan(0)
          expect(paint.lineCap).toBe('round')
          expect(paint.lineJoin).toBe('round')
          paint.devicePoints.forEach((point, index) => {
            expect(paint.cssPoints[index]![0]).toBeCloseTo(
              point[0] * mode.sourceDimensions.width / mode.backingDimensions.width,
              7,
            )
            expect(paint.cssPoints[index]![1]).toBeCloseTo(
              point[1] * mode.sourceDimensions.height / mode.backingDimensions.height,
              7,
            )
          })
          if (stroke.role === 'lambda') {
            expect(paint.commands.some(({ kind }) => kind === 'arc')).toBe(true)
          }
        }
      })

      it('matches phase identity and structural event order across the reference, 2D, and 3D', () => {
        for (const sample of requiredSamples) {
          const frames = MODES.map((mode) => at(example.modes[mode].frames, sample.progress))
          expect(new Set(frames.map(({ phase }) => phase)).size).toBe(1)
          const flags = frames.map(({ structural }) => ({
            binder: structural.binderPresent,
            stems: structural.stemCount > 0,
            argument: structural.argumentCount > 0,
            copies: structural.copies.length,
          }))
          expect(flags.slice(1)).toEqual([flags[0], flags[0], flags[0]])
        }
      })

      it('retains complete correspondence-addressable topology from each actual renderer witness', () => {
        for (const sample of requiredSamples) {
          const reference = at(example.modes.reference.frames, sample.progress)
          expect(reference.observations.source).toBe('live-reference-transition')
          const referenceGroups = groupsOf(reference)
          expect(referenceGroups.size).toBeGreaterThan(0)
          for (const modeName of ['2d-light', '3d-light', '3d-dark'] as const) {
            const actual = at(example.modes[modeName].frames, sample.progress)
            expect(actual.observations.source).toBe(modeName === '2d-light'
              ? 'application-2d-paint'
              : 'presented-webgl-entities')
            expect(new Set(actual.observations.strokes.map(({ pieceId }) => pieceId)).size)
              .toBe(actual.observations.strokes.length)
            const rendererOnly = actual.observations.strokes.filter(({ rendererOnly }) => rendererOnly)
            expect(rendererOnly.every(({ pieceId, sourceStrokeId, renderRole }) => (
              (sourceStrokeId.startsWith('interface:')
                && ['free-rail', 'free-port', 'term-output', 'output-arc', 'output-line'].includes(renderRole))
              || (pieceId.startsWith('3d:socket:') && renderRole === 'argument-connector')
            ))).toBe(true)
            const actualGroups = groupsOf(actual)
            expect([...actualGroups.keys()].sort()).toEqual([...referenceGroups.keys()].sort())
            for (const [address, referenceGroup] of referenceGroups) {
              const actualGroup = actualGroups.get(address)!
              expect(new Set(actualGroup.map(({ role }) => role))).toEqual(new Set(referenceGroup.map(({ role }) => role)))
              expect(new Set(actualGroup.map(({ lineage }) => lineage))).toEqual(new Set(referenceGroup.map(({ lineage }) => lineage)))
              expect(new Set(actualGroup.map(({ copyIndex }) => copyIndex))).toEqual(new Set(referenceGroup.map(({ copyIndex }) => copyIndex)))
              explicitSubdivisionJunctions(referenceGroup, actualGroup, `${modeName} ${address}`)
              expect(componentCount(actualGroup), `${modeName} ${address} is disconnected`).toBe(1)
              expect(topologyTerminals(actualGroup), `${modeName} ${address} has a wrong destination`)
                .toEqual(topologyTerminals(referenceGroup))
            }
            const referencePersistentStrokes = semanticStrokes(reference).filter(({ lineage }) => lineage === 'persistent')
            const actualPersistentStrokes = semanticStrokes(actual).filter(({ lineage }) => lineage === 'persistent')
            const referencePersistent = junctionPositions(referencePersistentStrokes)
            const actualPersistent = junctionPositions(actualPersistentStrokes)
            explicitSubdivisionJunctions(
              referencePersistentStrokes,
              actualPersistentStrokes,
              `${modeName} persistent frame ${sample.progress}`,
            )
            const referenceStartStrokes = semanticStrokes(at(example.modes.reference.frames, 0))
              .filter(({ lineage }) => lineage === 'persistent')
            const actualStartStrokes = semanticStrokes(at(example.modes[modeName].frames, 0))
              .filter(({ lineage }) => lineage === 'persistent')
            const referenceStart = junctionPositions(referenceStartStrokes)
            const referenceDestinations = junctionDestinations(referenceStartStrokes)
            const referenceEnd = junctionPositions(semanticStrokes(at(example.modes.reference.frames, 1))
              .filter(({ lineage }) => lineage === 'persistent'))
            const actualStart = junctionPositions(actualStartStrokes)
            const actualDestinations = junctionDestinations(actualStartStrokes)
            const actualEnd = junctionPositions(semanticStrokes(at(example.modes[modeName].frames, 1))
              .filter(({ lineage }) => lineage === 'persistent'))
            expect([...referenceDestinations.keys()].every((junction) => actualDestinations.has(junction)),
              `${modeName} dropped a persistent source correspondence`).toBe(true)
            for (const [junction, destination] of referenceDestinations) {
              expect(actualDestinations.get(junction), `${modeName} ${junction} has a wrong semantic destination`).toBe(destination)
              const currentIdentity = sample.progress === 1 ? destination : junction
              const expectedPoint = referencePersistent.get(currentIdentity)
              const actualPoint = actualPersistent.get(currentIdentity)
              const referenceFrom = referenceStart.get(junction), referenceTo = referenceEnd.get(destination)
              const actualFrom = actualStart.get(junction), actualTo = actualEnd.get(destination)
              expect(referenceFrom, `reference source is missing persistent junction ${junction}`).toBeDefined()
              expect(referenceTo, `reference target is missing destination ${destination}`).toBeDefined()
              expect(actualFrom, `${modeName} source is missing persistent junction ${junction}`).toBeDefined()
              expect(actualTo, `${modeName} target is missing destination ${destination}`).toBeDefined()
              expect(expectedPoint, `reference frame ${sample.progress} is missing ${currentIdentity}`).toBeDefined()
              expect(actualPoint, `${modeName} frame ${sample.progress} is missing ${currentIdentity}`).toBeDefined()
              if (referenceFrom === undefined || referenceTo === undefined || actualFrom === undefined
                || actualTo === undefined || expectedPoint === undefined || actualPoint === undefined) {
                throw new Error(`incomplete trajectory for ${junction} -> ${destination}`)
              }
              const referenceSpan = pointDistance(referenceFrom, referenceTo)
              const actualSpan = pointDistance(actualFrom, actualTo)
              if (referenceSpan < 1e-8) {
                expect(pointDistance(expectedPoint, referenceFrom), `reference ${junction} unexpectedly moved`).toBeLessThan(1e-6)
                expect(actualSpan, `${modeName} ${junction} has a destination absent from the reference`).toBeLessThan(1e-8)
                expect(pointDistance(actualPoint, actualFrom), `${modeName} ${junction} unexpectedly moved`).toBeLessThan(1e-6)
              } else {
                expect(actualSpan, `${modeName} ${junction} never moved toward its destination`).toBeGreaterThan(1e-8)
                const expectedMotion = normalizedStageFraction(expectedPoint, referenceFrom, referenceTo)
                const actualMotion = normalizedStageFraction(actualPoint, actualFrom, actualTo)
                expect(expectedMotion.offAxis, `reference ${junction} left its endpoint trajectory`).toBeLessThan(1e-6)
                expect(actualMotion.offAxis, `${modeName} ${junction} left its endpoint trajectory`).toBeLessThan(1e-6)
                expect(actualMotion.amount, `${modeName} ${junction} snapped or moved at the wrong rate`)
                  .toBeCloseTo(expectedMotion.amount, 6)
              }
            }
          }
        }
      })

      it('matches every reference-visible correspondence curve by extent, arc length, and sampled interior shape', () => {
        for (const sample of requiredSamples) {
          const reference = at(example.modes.reference.frames, sample.progress)
          const referenceGroups = groupsOf(reference)
          for (const modeName of ['2d-light', '3d-light', '3d-dark'] as const) {
            const actualGroups = groupsOf(at(example.modes[modeName].frames, sample.progress))
            expect([...actualGroups.keys()].sort()).toEqual([...referenceGroups.keys()].sort())
            for (const [address, referenceGroup] of referenceGroups) {
              const actualGroup = actualGroups.get(address)!
              expect(actualGroup.every(({ curve }) => curve.rawPointCount >= 2), `${modeName} ${address} has no complete polyline`).toBe(true)
              const acceptance = correspondenceCurveAcceptance(reference, referenceGroup,
                at(example.modes[modeName].frames, sample.progress), actualGroup, modeName)
              expect(acceptance.accepted,
                `${modeName} ${address} violates semantic-frame full-curve bounds: ${JSON.stringify(acceptance)}`).toBe(true)
            }
          }
        }
      })

      it('matches complete copy shapes and reference-derived lift/dock trajectories without snaps', () => {
        if (expected.copies === 0) return
        const [, split, liftEnd, spaceEnd, dockEnd] = expected.boundaries
        for (const modeName of MODES) {
          const frames = example.modes[modeName].frames
          for (const sample of requiredSamples.filter(({ progress }) => progress >= split!)) {
            const frame = at(frames, sample.progress)
            for (let copyIndex = 0; copyIndex < expected.copies; copyIndex += 1) {
              const copyStrokes = semanticStrokes(frame).filter(({ copyIndex: index }) => index === copyIndex)
              const origins = [...new Set(copyStrokes.map(({ address }) => address.slice(copyPrefix(copyIndex).length)))].sort()
              expect(origins).toEqual([...example.correspondence.argumentStrokeAddresses].sort())
              expect(componentCount(copyStrokes)).toBe(1)
              if (modeName === 'reference') continue
              const reference = at(example.modes.reference.frames, sample.progress)
              const referencePositions = junctionPositions(semanticStrokes(reference).filter(({ copyIndex: index }) => index === copyIndex))
              const actualPositions = junctionPositions(copyStrokes)
              const referenceRoot = copyRoot(reference, copyIndex, example.correspondence.argumentRootJunction)
              const actualRoot = copyRoot(frame, copyIndex, example.correspondence.argumentRootJunction)
              for (const [junction, expectedPoint] of referencePositions) {
                const actualPoint = actualPositions.get(junction)
                expect(actualPoint, `${modeName} dropped copy junction ${junction}`).toBeDefined()
                if (actualPoint === undefined) throw new Error(`${modeName} dropped copy junction ${junction}`)
                expect(pointDistance(
                  [actualPoint[0] - actualRoot[0], actualPoint[1] - actualRoot[1]],
                  [expectedPoint[0] - referenceRoot[0], expectedPoint[1] - referenceRoot[1]],
                ), `${modeName} ${junction} changed the complete copy shape`).toBeLessThan(1e-6)
              }
            }
          }

          for (let copyIndex = 0; copyIndex < expected.copies; copyIndex += 1) {
            for (const [startProgress, midpoint, endProgress] of [
              [split!, (split! + liftEnd!) / 2, liftEnd!],
              [spaceEnd!, (spaceEnd! + dockEnd!) / 2, dockEnd!],
            ] as const) {
              const referenceStage = [startProgress, midpoint, endProgress].map((progress) => (
                copyRoot(at(example.modes.reference.frames, progress), copyIndex, example.correspondence.argumentRootJunction)
              ))
              const actualStage = [startProgress, midpoint, endProgress].map((progress) => (
                copyRoot(at(frames, progress), copyIndex, example.correspondence.argumentRootJunction)
              ))
              const expectedFraction = normalizedStageFraction(referenceStage[1]!, referenceStage[0]!, referenceStage[2]!)
              const actualFraction = normalizedStageFraction(actualStage[1]!, actualStage[0]!, actualStage[2]!)
              expect(actualFraction.amount).toBeCloseTo(expectedFraction.amount, 6)
              expect(actualFraction.offAxis).toBeLessThan(1e-6)
            }
          }
        }
      })

      it('matches every lineage color and samples pixels only on Lambda-authored strokes', () => {
        const liftEnd = expected.boundaries[2]!
        for (const sample of requiredSamples) {
          const reference = at(example.modes.reference.frames, sample.progress)
          const referenceGroups = groupsOf(reference)
          for (const modeName of MODES) {
            const frame = at(example.modes[modeName].frames, sample.progress)
            const groups = groupsOf(frame)
            for (const [address, referenceGroup] of referenceGroups) {
              const actualGroup = groups.get(address)
              expect(actualGroup, `${modeName} is missing semantic stroke group ${address}`).toBeDefined()
              if (actualGroup === undefined) throw new Error(`${modeName} is missing semantic stroke group ${address}`)
              const referenceColor = singleColor(referenceGroup, `reference ${address}`)
              const actualColor = singleColor(actualGroup, `${modeName} ${address}`)
              expect(referenceColor, `reference ${address} has a wrong stage color`).toBe(
                expectedStrokeColor(reference, referenceGroup[0]!, expected.boundaries, manifest.palette),
              )
              expect(actualColor, `${modeName} ${address} has a wrong stage color`).toBe(
                expectedStrokeColor(frame, actualGroup[0]!, expected.boundaries, manifest.palette),
              )
            }
            const observations = new Map(frame.observations.strokes.map((stroke) => [stroke.pieceId, stroke]))
            const eligibleGroupIds = new Set(semanticStrokes(frame)
              .filter(({ raster }) => raster.requiredMatchingPixels > 0)
              .map(({ raster }) => raster.groupId))
            const allRasterGroups = rasterGroups(frame)
            for (const groupId of eligibleGroupIds) {
              const group = allRasterGroups.get(groupId)
              expect(group, `${modeName} omitted raster group ${groupId}`).toBeDefined()
              if (group === undefined) throw new Error(`${modeName} omitted raster group ${groupId}`)
              const topPieceId = group[0]!.raster.topPieceId
              const top = observations.get(topPieceId)
              expect(top, `${modeName} ${groupId} has no top painted member`).toBeDefined()
              if (top === undefined) throw new Error(`${modeName} ${groupId} has no top painted member`)
              const evidence = top.raster
              expect([...evidence.groupMemberIds].sort()).toEqual(group.map(({ pieceId }) => pieceId).sort())
              for (const member of group) {
                const { screenPoints: _points, lineWidth: _width, screenLength: _length,
                  requiredMatchingPixels: _required, ...shared } = member.raster
                const { screenPoints: _topPoints, lineWidth: _topWidth, screenLength: _topLength,
                  requiredMatchingPixels: _topRequired, ...topShared } = evidence
                expect(shared, `${modeName} ${groupId} has inconsistent shared raster evidence`).toEqual(topShared)
                expect(member.raster.screenLength, `${modeName} ${member.pieceId} lost its authored centerline`)
                  .toBeCloseTo(polylineLength(member.raster.screenPoints), 6)
                expect(member.raster.lineWidth, `${modeName} ${member.pieceId} lost its authored width`).toBeGreaterThan(0)
              }
              expect(top?.color).toBe(evidence.targetColor)
              expect(top?.rendererOnly, `${modeName} ${groupId} lets renderer-only incidence satisfy semantic color`).toBe(false)
              for (const member of group.filter(({ rendererOnly }) => rendererOnly)) {
                expect(member.sourceStrokeId.startsWith('interface:'),
                  `${modeName} ${groupId} contains unrelated renderer-only geometry`).toBe(true)
                expect(evidence.coverageByMember[member.pieceId],
                  `${modeName} ${groupId} does not fully overdraw its renderer-local subdivision tube`).toBeGreaterThanOrEqual(0.995)
              }
              if (group.length > 1) {
                for (const member of group) {
                  expect(evidence.coverageByMember[member.pieceId],
                    `${modeName} ${groupId} does not contain the full painted tube for ${member.pieceId}`).toBeGreaterThanOrEqual(0.995)
                }
              }
              if (evidence.occludedByPieceIds.length > 0) {
                expect(evidence.occlusionCoverage, `${modeName} ${groupId} has an incomplete occlusion witness`)
                  .toBeGreaterThanOrEqual(0.995)
                const occluders = evidence.occludedByPieceIds.map((pieceId) => observations.get(pieceId))
                expect(occluders.every((stroke) => stroke !== undefined),
                  `${modeName} ${groupId} attributes occlusion to missing geometry`).toBe(true)
                const topIndex = frame.observations.strokes.findIndex(({ pieceId }) => pieceId === evidence.topPieceId)
                expect(occluders.every((stroke) => frame.observations.strokes.indexOf(stroke!) > topIndex),
                  `${modeName} ${groupId} attributes occlusion to geometry below it in Painter order`).toBe(true)
                expect(occluders.filter((stroke) => stroke?.rendererOnly).every((stroke) => (
                  stroke!.sourceStrokeId.startsWith('interface:') || stroke!.renderRole === 'argument-connector'
                )), `${modeName} ${groupId} attributes occlusion to unrelated renderer-only geometry`).toBe(true)
                expect(occluders.every((stroke) => stroke !== undefined && stroke.raster.requiredMatchingPixels > 0),
                  `${modeName} ${groupId} is covered only by degenerate authored geometry`).toBe(true)
                for (const stroke of occluders) {
                  expect(stroke!.raster.eligiblePixels,
                    `${modeName} ${groupId} relies on an occluder with no independent raster tube`).toBeGreaterThanOrEqual(stroke!.raster.requiredMatchingPixels)
                  expect(stroke!.raster.matchingPixels,
                    `${modeName} ${groupId} relies on an occluder with no authored-color pixels`).toBeGreaterThanOrEqual(stroke!.raster.requiredMatchingPixels)
                  expect(stroke!.raster.bestColorDistance,
                    `${modeName} ${groupId} relies on an occluder missing its authored color`).toBeLessThanOrEqual(modeName.startsWith('3d') ? 72 : 48)
                }
                const paths = occluders.map((stroke) => ({
                  path: stroke!.raster.screenPoints,
                  radius: stroke!.raster.lineWidth / 2 + 0.75,
                }))
                const coverage = unionPathCoverage(evidence.screenPoints, paths, evidence.lineWidth / 2 + 0.75)
                expect(coverage, `${modeName} ${groupId} cannot reproduce its serialized semantic occlusion`)
                  .toBeGreaterThanOrEqual(0.995)
                for (let index = 0; index < paths.length; index += 1) {
                  expect(unionPathCoverage(evidence.screenPoints,
                    paths.filter((_, pathIndex) => pathIndex !== index), evidence.lineWidth / 2 + 0.75),
                  `${modeName} ${groupId} includes a non-minimal full-tube occluder`).toBeLessThan(0.995)
                }
                continue
              }
              expect(evidence.occlusionCoverage).toBe(0)
              expect(evidence.eligiblePixels, `${modeName} ${groupId} has no exclusive/group raster tube`)
                .toBeGreaterThanOrEqual(evidence.requiredMatchingPixels)
              expect(evidence.matchingPixels, `${modeName} ${groupId} lacks its own expected-color pixels`)
                .toBeGreaterThanOrEqual(evidence.requiredMatchingPixels)
              expect(evidence.bestColorDistance, `${modeName} ${groupId} misses its authored group color`)
                .toBeLessThanOrEqual(modeName.startsWith('3d') ? 72 : 48)
            }
          }
        }
        if (expected.copies > 0) {
          for (const modeName of MODES) {
            const frame = at(example.modes[modeName].frames, liftEnd)
            for (const group of groupsOf(frame).values()) if (group[0]!.lineage === 'copy') {
              expect(singleColor(group, `${modeName} lifted copy`)).toBe(manifest.palette.copies[group[0]!.copyIndex!]!)
            }
            const settled = at(example.modes[modeName].frames, 1)
            for (const group of groupsOf(settled).values()) if (group[0]!.lineage === 'copy') {
              expect(singleColor(group, `${modeName} settled copy`)).toBe(settled.observations.baseColor.toLowerCase())
            }
          }
        }
      })

      it('parks complete copies, reaches target geometry, docks, and cleans stems before the binder', () => {
        if (expected.copies === 0) return
        const [, split, liftEnd, spaceEnd, dockEnd, stemEnd, barEnd] = expected.boundaries
        for (const modeName of MODES) {
          const frames = example.modes[modeName].frames
          const parked = at(frames, liftEnd!)
          expect(parked.structural.copies).toHaveLength(expected.copies)
          expect(parked.structural.copies.every(({ strokeCount, components }) => strokeCount > 0 && components === 1)).toBe(true)
          expect(new Set(parked.structural.copies.map(({ strokeCount }) => strokeCount)).size).toBe(1)
          if (expected.copies > 1) expect(minCentroidSeparation(parked.structural.copies)).toBeGreaterThan(0.025)
          else expect(parked.structural.copies[0]!.distanceToTarget).toBeGreaterThan(0.025)
          expect(at(frames, spaceEnd!).structural.persistentTargetError).toBeLessThan(1e-7)
          expect(at(frames, dockEnd!).structural.copyTargetError).toBeLessThan(1e-7)
          expect(at(frames, stemEnd!).structural.stemCount).toBe(0)
          expect(at(frames, stemEnd!).structural.binderPresent).toBe(true)
          expect(at(frames, barEnd!).structural.binderPresent).toBe(false)
          expect(at(frames, 1).structural.endpointStaticError).toBeLessThan(1e-7)
          expect(at(frames, split!).structural.argumentCount).toBe(0)
        }
      })

      it('contracts an unused argument geometrically instead of fading it', () => {
        if (expected.copies !== 0) return
        const [, split, discardEnd, spaceEnd, barEnd] = expected.boundaries
        const midpoint = (split! + discardEnd!) / 2
        for (const modeName of MODES) {
          const frames = example.modes[modeName].frames
          const start = at(frames, split!)
          const middle = at(frames, midpoint)
          const finish = at(frames, discardEnd!)
          expect(start.structural.argumentCount).toBeGreaterThan(0)
          expect(middle.structural.argumentCount).toBeGreaterThan(0)
          expect(middle.structural.argumentSpan).toBeGreaterThan(0)
          expect(middle.structural.argumentSpan).toBeLessThan(start.structural.argumentSpan * 0.9)
          expect(finish.structural.argumentCount).toBe(0)
          expect(at(frames, spaceEnd!).structural.persistentTargetError).toBeLessThan(1e-7)
          expect(at(frames, discardEnd!).structural.binderPresent).toBe(true)
          expect(at(frames, barEnd!).structural.binderPresent).toBe(false)
          expect(at(frames, 1).structural.endpointStaticError).toBeLessThan(1e-7)
        }
      })

      it('keeps copy hues attached to lineage and proves their presence in real pixels', () => {
        if (expected.copies === 0) return
        const liftEnd = expected.boundaries[2]!
        const spaceEnd = expected.boundaries[3]!
        const dockEnd = expected.boundaries[4]!
        for (const modeName of MODES) {
          const mode = example.modes[modeName]
          const rasterMatches = Array.from({ length: expected.copies }, () => 0)
          for (const progress of [liftEnd, spaceEnd, dockEnd]) {
            const frame = at(mode.frames, progress)
            frame.structural.copies.forEach((copy) => {
              expect(copy.colors).toEqual([manifest.palette.copies[copy.index]!])
              rasterMatches[copy.index] = Math.max(
                rasterMatches[copy.index]!,
                frame.raster.paletteMatches[manifest.palette.copies[copy.index]!] ?? 0,
              )
              if (modeName === '2d-light') {
                const visibility = frame.twoD!.copyVisibility[manifest.palette.copies[copy.index]!]
                expect(visibility?.strokeCount).toBeGreaterThan(0)
                expect(visibility?.visibleStrokeCount).toBe(visibility?.strokeCount)
              }
            })
          }
          expect(rasterMatches.every((count) => count > 0)).toBe(true)
        }
      })

      it('renders the actual 3D Lambda frame as branch-normal stroke-only planar geometry in both themes', () => {
        for (const modeName of ['3d-light', '3d-dark'] as const) {
          const mode = example.modes[modeName]
          for (const frame of mode.frames) {
            expect(frame.threeD).toBeDefined()
            expect(frame.threeD!.strokeOnly).toBe(true)
            expect(frame.threeD!.planarFootprint).toBe(true)
            expect(frame.threeD!.maxPlanarityError).toBeLessThan(1e-8)
            expect(frame.threeD!.maxNormalError).toBeLessThan(1e-8)
            expect(frame.threeD!.maxAttachmentGap).toBeLessThan(1e-8)
            expect(frame.threeD!.entityColorMismatches).toBe(0)
            expect(frame.threeD!.lambdaFillRatio).toBeLessThan(0.3)
          }
          const base = modeName === '3d-light' ? manifest.palette.lightBase : manifest.palette.darkBase
          for (const progress of [0, 1]) {
            const frame = at(mode.frames, progress)
            expect(frame.raster.paletteMatches[base] ?? 0).toBeGreaterThan(0)
            expect(frame.threeD!.bestBasePixelDistance).toBeLessThanOrEqual(72)
          }
        }
      })

      it('keeps the actual 2D Lambda interface attached to every incident wire', () => {
        for (const frame of example.modes['2d-light'].frames) {
          expect(frame.twoD).toBeDefined()
          expect(frame.twoD!.maxAttachmentGap).toBeLessThan(1e-8)
          expect(frame.twoD!.frameHalf).toBeCloseTo(frame.twoD!.sourceFrameHalf, 10)
          expect(frame.twoD!.viewScale).toBeCloseTo(405 / frame.twoD!.frameHalf, 10)
        }
      })
    })
  }
})
