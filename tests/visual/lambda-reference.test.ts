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

type FrameEvidence = {
  readonly progress: number
  readonly sample: 'boundary' | 'midpoint'
  readonly phase: string
  readonly image: string
  readonly imageSha256: string
  readonly structural: StructuralFrame
  readonly raster: RasterFrame
  readonly twoD?: TwoDFrame
  readonly threeD?: ThreeDFrame
}

type ModeEvidence = {
  readonly sourceDimensions: { readonly width: number; readonly height: number }
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
    readonly lightBase: string
    readonly darkBase: string
  }
  readonly examples: readonly {
    readonly key: string
    readonly source: string
    readonly copyCount: number
    readonly boundaries: readonly number[]
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
