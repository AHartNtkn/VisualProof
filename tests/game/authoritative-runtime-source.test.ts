import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

describe('authoritative renderer source boundary', () => {
  it('contains no prototype authority, renderer persistence fallback, app import, or obsolete asset consumer', () => {
    const mount = readFileSync('src/game/interface/mount.ts', 'utf8')
    const app = readFileSync('app/main.ts', 'utf8')
    const style = readFileSync('app/style.css', 'utf8')
    const combined = `${mount}\n${app}\n${style}`
    expect(mount).toContain('class CursebreakerRuntime')
    expect(mount).toContain('reduceGame')
    expect(mount).toContain('decodeGameSave')
    expect(combined).not.toMatch(/(?:\.\.\/)+app(?:\/|')|localStorage|ProofFrontViewport/)
    expect(combined).not.toMatch(/central-lens\/(?:frame|glass|shadow|lever-housing|lever-handle)\.png/)
    expect(style).not.toMatch(/curse-lens-(?:frame|glass|shadow|optics)/)
  })

  it('allows only runtime style attributes in addition to the restricted renderer policy', () => {
    const html = readFileSync('app/index.html', 'utf8')
    expect(html).toMatch(/style-src 'self'; style-src-attr 'unsafe-inline'/)
    expect(html).toMatch(/script-src 'self'/)
    expect(html).toMatch(/connect-src 'none'/)
    expect(html).toMatch(/object-src 'none'/)
    expect(html).toMatch(/frame-src 'none'/)
  })
})
