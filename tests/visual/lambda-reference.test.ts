import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readdirSync, readFileSync, statSync } from 'node:fs'
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

function normalizedCurveShape(curve: StrokeCurve): readonly Point[] {
  if (curve.normalizedLength < 1e-10) return curve.normalizedPoints
  return curve.normalizedPoints.map(([x, y]) => [x / curve.normalizedLength, Math.abs(y) / curve.normalizedLength])
}

function curveShapeError(reference: StrokeCurve, actual: StrokeCurve): number {
  const left = normalizedCurveShape(reference), right = normalizedCurveShape(actual)
  if (left.length !== right.length || left.length === 0) return Infinity
  return Math.max(...left.map((point, index) => pointDistance(point, right[index]!)))
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
): number {
  if (source.length === 0 || targets.length === 0) return 0
  const samples = source.slice(1).flatMap((to, index) => Array.from({ length: 9 }, (_, step): Point => {
    const from = source[index]!, amount = step / 8
    return [from[0] + (to[0] - from[0]) * amount, from[1] + (to[1] - from[1]) * amount]
  }))
  samples.push(source.at(-1)!)
  return samples.filter((point) => targets.some((target) => pathDistance(point, target.path) <= target.radius)).length
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

  it('is current, complete evidence from the live authority and current application', () => {
    expect(manifest.schema).toBe(1)
    expect(resolve(manifest.outputDirectory)).toBe(OUTPUT)
    expect(manifest.reference.path).toBe('/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html')
    expect(sha256(readFileSync(manifest.reference.path))).toBe(manifest.reference.sha256)
    expect(execFileSync('git', ['rev-parse', 'HEAD'], { cwd: ROOT, encoding: 'utf8' }).trim())
      .toBe(manifest.application.commit)
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
              const referenceLength = referenceGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedLength, 0)
              const actualLength = actualGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedLength, 0)
              const referenceExtent = referenceGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedExtent, 0)
              const actualExtent = actualGroup.reduce((sum, stroke) => sum + stroke.curve.normalizedExtent, 0)
              if (referenceLength < 1e-6) {
                expect(actualLength, `${modeName} painted absent reference curve ${address}`).toBeLessThan(1e-6)
                continue
              }
              expect(actualLength, `${modeName} dropped visible curve ${address}`).toBeGreaterThan(referenceLength * 0.25)
              expect(actualLength, `${modeName} exaggerated curve ${address}`).toBeLessThan(referenceLength * 4)
              expect(actualExtent, `${modeName} collapsed visible extent ${address}`).toBeGreaterThan(referenceExtent * 0.25)
              expect(actualExtent, `${modeName} exaggerated visible extent ${address}`).toBeLessThan(referenceExtent * 4)
              expect(actualGroup.every(({ curve }) => curve.rawPointCount >= 2), `${modeName} ${address} has no complete polyline`).toBe(true)
              if (referenceGroup.length === 1 && actualGroup.length === 1) {
                expect(curveShapeError(referenceGroup[0]!.curve, actualGroup[0]!.curve),
                  `${modeName} changed the sampled interior shape of ${address}`).toBeLessThan(0.18)
              }
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
              const evidence = group[0]!.raster
              expect([...evidence.groupMemberIds].sort()).toEqual(group.map(({ pieceId }) => pieceId).sort())
              expect(group.every(({ raster }) => JSON.stringify(raster) === JSON.stringify(evidence)),
                `${modeName} ${groupId} has inconsistent shared raster evidence`).toBe(true)
              const top = observations.get(evidence.topPieceId)
              expect(top, `${modeName} ${groupId} has no top painted member`).toBeDefined()
              expect(top?.color).toBe(evidence.targetColor)
              expect(top?.rendererOnly, `${modeName} ${groupId} lets renderer-only incidence satisfy semantic color`).toBe(false)
              for (const member of group.filter(({ rendererOnly }) => rendererOnly)) {
                expect(member.sourceStrokeId.startsWith('interface:'),
                  `${modeName} ${groupId} contains unrelated renderer-only geometry`).toBe(true)
                expect(evidence.coverageByMember[member.pieceId],
                  `${modeName} ${groupId} does not fully overdraw its renderer-local subdivision`).toBeGreaterThanOrEqual(0.98)
              }
              if (group.length > 1) {
                for (const member of group) {
                  expect(evidence.coverageByMember[member.pieceId],
                    `${modeName} ${groupId} is not a complete coincident-subpath group for ${member.pieceId}`).toBeGreaterThanOrEqual(0.98)
                }
              }
              if (evidence.occludedByPieceIds.length > 0) {
                expect(evidence.occlusionCoverage, `${modeName} ${groupId} has an incomplete occlusion witness`)
                  .toBeGreaterThanOrEqual(0.98)
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
                const coverage = unionPathCoverage(evidence.screenPoints, paths)
                expect(coverage, `${modeName} ${groupId} cannot reproduce its serialized semantic occlusion`)
                  .toBeGreaterThanOrEqual(0.98)
                for (let index = 0; index < paths.length; index += 1) {
                  expect(coverage - unionPathCoverage(evidence.screenPoints, paths.filter((_, pathIndex) => pathIndex !== index)),
                    `${modeName} ${groupId} includes a non-contributing occlusion path`).toBeGreaterThan(0.01)
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
