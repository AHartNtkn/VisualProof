import { existsSync, readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { inspectPngFile } from '../../scripts/assets/canonical-png'

const source = resolve('review/editor-loupe-study/isolated/candidate-a.png')
const output = resolve('assets/interface/generated/editor-loupe')
const files = {
  rim: resolve(output, 'rim-socket.png'),
  handle: resolve(output, 'handle-terminal.png'),
  optics: resolve(output, 'optical-edge.png'),
}

const alphaAt = (rgba: Buffer, width: number, x: number, y: number): number =>
  rgba[(y * width + x) * 4 + 3]!

describe('approved Candidate A production layers', () => {
  it('uses three full-size transparent semantic layers with a clear aperture', () => {
    for (const [kind, file] of Object.entries(files)) {
      expect(existsSync(file), `${kind} layer exists`).toBe(true)
      const png = inspectPngFile(file)
      expect([png.width, png.height]).toEqual([1400, 1400])
      expect(png.nonemptyAlpha).toBe(true)
      expect(alphaAt(png.rgba, png.width, 0, 0)).toBe(0)
      expect(alphaAt(png.rgba, png.width, 590, 700)).toBe(0)
    }
    expect(alphaAt(inspectPngFile(files.rim).rgba, 1400, 650, 180)).toBeGreaterThan(0)
    expect(alphaAt(inspectPngFile(files.optics).rgba, 1400, 1080, 650)).toBeGreaterThan(0)
    expect(alphaAt(inspectPngFile(files.handle).rgba, 1400, 1200, 1180)).toBeGreaterThan(0)
  })

  it('losslessly partitions approved source pixels instead of repainting them', () => {
    const approved = inspectPngFile(source)
    const layers = Object.values(files).map(inspectPngFile)
    const violations = { overlaps: 0, missing: 0, altered: 0, spurious: 0 }
    for (let pixel = 0; pixel < approved.width * approved.height; pixel++) {
      const offset = pixel * 4
      const owners = layers.filter((layer) => layer.rgba[offset + 3]! > 0)
      if (owners.length > 1) violations.overlaps++
      if (approved.rgba[offset + 3] === 0) {
        if (owners.length !== 0) violations.spurious++
        continue
      }
      if (owners.length !== 1) {
        violations.missing++
        continue
      }
      for (let channel = 0; channel < 4; channel++) {
        if (owners[0]!.rgba[offset + channel] !== approved.rgba[offset + channel]) {
          violations.altered++
          break
        }
      }
    }
    expect(violations).toEqual({ overlaps: 0, missing: 0, altered: 0, spurious: 0 })
  })

  it('is referenced by the production class and keeps optics pointer-transparent and edge-only', () => {
    const runtime = readFileSync(resolve('src/game/interface/construction-loupe.ts'), 'utf8')
    const css = readFileSync(resolve('src/game/interface/construction-loupe.css'), 'utf8')
    for (const name of ['rim-socket.png', 'handle-terminal.png', 'optical-edge.png']) expect(runtime).toContain(name)
    expect(css).toMatch(/construction-loupe__art[^}]*pointer-events:\s*none/s)
    expect(css).toMatch(/construction-loupe__art--optics[^}]*mix-blend-mode/s)
    expect(css).toMatch(/construction-loupe__canvas[^}]*clip-path:\s*circle/s)
  })
})
