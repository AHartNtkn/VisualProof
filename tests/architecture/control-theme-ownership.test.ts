import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

const css = readFileSync('app/style.css', 'utf8')
const shell = readFileSync('src/app/shell.ts', 'utf8')

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
})
