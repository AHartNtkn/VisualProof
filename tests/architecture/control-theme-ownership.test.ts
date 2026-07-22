import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

const css = readFileSync('app/style.css', 'utf8')
const shell = readFileSync('src/app/shell.ts', 'utf8')
const spawn = readFileSync('src/app/interact/spawn.ts', 'utf8')
const moves = readFileSync('src/app/interact/moves.ts', 'utf8')
const construct = readFileSync('src/app/interact/construct.ts', 'utf8')

describe('control theme ownership', () => {
  it('publishes the selected Theme at the document root', () => {
    expect(shell).toContain('applyControlTheme(canvas.ownerDocument, theme)')
    expect(shell).not.toContain('chrome.dataset.colorMode')
  })

  it('has no competing system-preference or chrome-scoped control palette', () => {
    expect(css).not.toContain('@media (prefers-color-scheme: dark)')
    expect(css).not.toContain('#chrome[data-color-mode="dark"]')
    expect(css).toContain(':root[data-color-mode="dark"]')
  })

  it('maps all browser button states to semantic control properties', () => {
    for (const property of [
      '--vpa-control-surface', '--vpa-control-foreground', '--vpa-control-border',
      '--vpa-control-hover-surface', '--vpa-control-active-surface',
      '--vpa-control-disabled-surface', '--vpa-control-focus-ring',
      '--vpa-control-primary-surface', '--vpa-control-primary-foreground',
    ]) expect(css).toContain(`var(${property})`)
  })

  it('keeps ephemeral control colors and states out of TypeScript', () => {
    for (const [name, source] of [['spawn', spawn], ['moves', moves], ['construct', construct]] as const) {
      expect(source, `${name} retains a light-only white control surface`).not.toMatch(/background:\s*#fff(?:;|`)/)
      expect(source, `${name} retains a JavaScript hover background mutation`).not.toMatch(/style\.background\s*=/)
    }
    expect(spawn).not.toContain("meta.style.color = '#a8a29e'")
    expect(moves).not.toMatch(/background:#fff|color:#78716c/)
    expect(construct).not.toMatch(/input\.style\.cssText\s*=.*(?:background|color|border)/)
  })
})
