# Theme-Owned Button Color System Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace unreadable and light-only button colors with one accessible Manuscript/Slate control palette that visibly follows VisualProof's selected theme.

**Architecture:** Extend the existing `Theme` value with a required semantic control palette and publish it as CSS custom properties on the document root. CSS owns browser interaction states and component geometry; TypeScript owns palette values and removes every inline button/menu color path. Token tests prove contrast, architecture tests prove single ownership, and Playwright proves rendered mode changes across mount boundaries.

**Tech Stack:** TypeScript 5.5, CSS custom properties, Vitest 2, Playwright 1.60, Vite 5.

## Global Constraints

- Preserve the Light (Manuscript) and Dark (Slate) identity; do not redesign the canvas palette.
- Light controls use warm paper surfaces and dark brown ink; Dark controls use graphite surfaces and warm cream ink.
- Orange is reserved for focus, selection, and primary emphasis.
- Every enabled text-bearing role/state pair must reach 4.5:1 contrast.
- Disabled text, focus indicators, and control boundaries must reach 3:1 contrast.
- TypeScript theme values are the sole control-palette authority; CSS must not duplicate light/dark control literals.
- Publish the active palette and color mode on the document root so controls outside `#chrome` inherit it.
- Remove `prefers-color-scheme`, `#chrome[data-color-mode]`, inline button/menu colors, JavaScript hover color mutations, and all compatibility paths for the displaced model.
- Keep component layout and proof behavior unchanged.

## File Structure

- Create `src/app/control-theme.ts`: map `Theme.controls` to document-root CSS properties and the authoritative color-mode marker.
- Modify `src/view/paint.ts`: define `ControlPalette`, add `Theme.mode`, and provide complete accessible Light/Dark values.
- Modify `src/app/shell.ts`: publish the selected theme through `applyControlTheme` whenever the canvas backdrop changes.
- Modify `app/style.css`: consume semantic properties for default, primary, menu, disabled, hover, active, and focus states; retain component geometry.
- Modify `src/app/interact/spawn.ts`: replace inline light-only menu colors and hover mutations with semantic classes.
- Modify `src/app/interact/moves.ts`: replace inline proof-menu colors with semantic classes.
- Modify `src/app/interact/construct.ts`: move the bubble prompt's inline foreground/background/border colors into themed CSS.
- Modify `src/app/relation-workspace.ts`: replace the local primary marker with the shared semantic primary variant.
- Create `tests/app/control-theme.test.ts`: contrast and publication tests for the authoritative palette.
- Create `tests/architecture/control-theme-ownership.test.ts`: reject the displaced selector and inline-color ownership paths.
- Create `e2e/button-theme.spec.ts`: audit computed styles across both modes and representative mount boundaries.

---

### Task 1: Authoritative control palette and publisher

**Files:**
- Create: `src/app/control-theme.ts`
- Modify: `src/view/paint.ts:22-46,296-318`
- Create: `tests/app/control-theme.test.ts`

**Interfaces:**
- Consumes: existing `Theme`, `LIGHT`, and `DARK` exports from `src/view/paint.ts`.
- Produces: `ControlPalette`, `Theme.mode: 'light' | 'dark'`, `Theme.controls`, `CONTROL_THEME_PROPERTIES`, and `applyControlTheme(document: Document, theme: Theme): void`.

- [ ] **Step 1: Write the failing palette and publication tests**

Create `tests/app/control-theme.test.ts` with a hex contrast calculator, enabled-state checks, disabled/boundary checks, mode differentiation, and a fake document root that records CSS publication:

```ts
import { describe, expect, it } from 'vitest'
import { applyControlTheme, CONTROL_THEME_PROPERTIES } from '../../src/app/control-theme'
import { DARK, LIGHT, type ControlPalette, type Theme } from '../../src/view/paint'

function luminance(hex: string): number {
  expect(hex).toMatch(/^#[0-9a-f]{6}$/i)
  const channels = [1, 3, 5].map((start) => Number.parseInt(hex.slice(start, start + 2), 16) / 255)
  const [r, g, b] = channels.map((channel) => channel <= 0.04045
    ? channel / 12.92
    : ((channel + 0.055) / 1.055) ** 2.4)
  return 0.2126 * r! + 0.7152 * g! + 0.0722 * b!
}

function contrast(foreground: string, background: string): number {
  const a = luminance(foreground)
  const b = luminance(background)
  return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05)
}

const enabledPairs = (controls: ControlPalette): readonly (readonly [string, string])[] => [
  [controls.foreground, controls.surface],
  [controls.foreground, controls.hoverSurface],
  [controls.foreground, controls.activeSurface],
  [controls.primaryForeground, controls.primarySurface],
  [controls.primaryForeground, controls.primaryHoverSurface],
  [controls.primaryForeground, controls.primaryActiveSurface],
  [controls.mutedForeground, controls.menuSurface],
  [controls.mutedForeground, controls.menuHoverSurface],
]

describe.each([LIGHT, DARK])('$name control palette', (theme) => {
  it('keeps enabled small text at WCAG AA contrast', () => {
    for (const pair of enabledPairs(theme.controls)) expect(contrast(...pair)).toBeGreaterThanOrEqual(4.5)
  })

  it('keeps disabled text, borders, and focus indicators perceivable', () => {
    expect(contrast(theme.controls.disabledForeground, theme.controls.disabledSurface)).toBeGreaterThanOrEqual(3)
    expect(contrast(theme.controls.disabledBorder, theme.controls.disabledSurface)).toBeGreaterThanOrEqual(3)
    expect(contrast(theme.controls.border, theme.controls.surface)).toBeGreaterThanOrEqual(3)
    expect(contrast(theme.controls.primaryBorder, theme.controls.surface)).toBeGreaterThanOrEqual(3)
    expect(contrast(theme.controls.focusRing, theme.controls.surface)).toBeGreaterThanOrEqual(3)
  })
})

it('gives Light and Dark distinct semantic surfaces and foregrounds', () => {
  for (const property of ['surface', 'foreground', 'hoverSurface', 'primarySurface', 'menuSurface'] as const) {
    expect(LIGHT.controls[property]).not.toBe(DARK.controls[property])
  }
})

it('publishes every control property and the selected mode on the document root', () => {
  const declarations = new Map<string, string>()
  const root = {
    dataset: {} as DOMStringMap,
    style: {
      colorScheme: '',
      setProperty: (property: string, value: string) => declarations.set(property, value),
    },
  }
  applyControlTheme({ documentElement: root } as unknown as Document, DARK)
  expect(root.dataset.colorMode).toBe('dark')
  expect(root.style.colorScheme).toBe('dark')
  expect(CONTROL_THEME_PROPERTIES.map(([key]) => key).sort()).toEqual(Object.keys(DARK.controls).sort())
  expect(declarations).toEqual(new Map(CONTROL_THEME_PROPERTIES.map(
    ([key, property]) => [property, DARK.controls[key]],
  )))
})
```

- [ ] **Step 2: Run the new test and verify RED**

Run:

```bash
npx vitest run tests/app/control-theme.test.ts --config vitest.config.ts
```

Expected: FAIL because `src/app/control-theme.ts`, `ControlPalette`, `Theme.mode`, and `Theme.controls` do not exist.

- [ ] **Step 3: Add the semantic palette and publisher**

In `src/view/paint.ts`, add these types and values:

```ts
export type ControlPalette = {
  readonly surface: string
  readonly foreground: string
  readonly border: string
  readonly hoverSurface: string
  readonly activeSurface: string
  readonly primarySurface: string
  readonly primaryForeground: string
  readonly primaryBorder: string
  readonly primaryHoverSurface: string
  readonly primaryActiveSurface: string
  readonly disabledSurface: string
  readonly disabledForeground: string
  readonly disabledBorder: string
  readonly focusRing: string
  readonly menuSurface: string
  readonly menuHoverSurface: string
  readonly mutedForeground: string
}

readonly mode: 'light' | 'dark'
readonly controls: ControlPalette
```

Insert those two members into the existing `Theme` declaration without removing its canvas or interaction members.

Add these exact properties to `LIGHT`:

```ts
mode: 'light',
controls: {
  surface: '#fffdf6', foreground: '#2a2118', border: '#8a806f',
  hoverSurface: '#f1eadc', activeSurface: '#e4d8c5',
  primarySurface: '#8a3f0a', primaryForeground: '#fffaf0', primaryBorder: '#743306',
  primaryHoverSurface: '#743306', primaryActiveSurface: '#5f2905',
  disabledSurface: '#e8e0d2', disabledForeground: '#655e54', disabledBorder: '#857b6a',
  focusRing: '#a94f00', menuSurface: '#fffdf6', menuHoverSurface: '#f4e6cb',
  mutedForeground: '#665d51',
},
```

Add these exact properties to `DARK`:

```ts
mode: 'dark',
controls: {
  surface: '#282d33', foreground: '#f1eadf', border: '#737b85',
  hoverSurface: '#353c45', activeSurface: '#414a55',
  primarySurface: '#f0a43a', primaryForeground: '#1a1611', primaryBorder: '#ffc15c',
  primaryHoverSurface: '#ffc15c', primaryActiveSurface: '#d98a20',
  disabledSurface: '#25292e', disabledForeground: '#a9a39a', disabledBorder: '#737b85',
  focusRing: '#f3aa3d', menuSurface: '#1f242a', menuHoverSurface: '#343b43',
  mutedForeground: '#b8b0a5',
},
```

Create `src/app/control-theme.ts`:

```ts
import type { ControlPalette, Theme } from '../view/paint'

export const CONTROL_THEME_PROPERTIES = [
  ['surface', '--vpa-control-surface'],
  ['foreground', '--vpa-control-foreground'],
  ['border', '--vpa-control-border'],
  ['hoverSurface', '--vpa-control-hover-surface'],
  ['activeSurface', '--vpa-control-active-surface'],
  ['primarySurface', '--vpa-control-primary-surface'],
  ['primaryForeground', '--vpa-control-primary-foreground'],
  ['primaryBorder', '--vpa-control-primary-border'],
  ['primaryHoverSurface', '--vpa-control-primary-hover-surface'],
  ['primaryActiveSurface', '--vpa-control-primary-active-surface'],
  ['disabledSurface', '--vpa-control-disabled-surface'],
  ['disabledForeground', '--vpa-control-disabled-foreground'],
  ['disabledBorder', '--vpa-control-disabled-border'],
  ['focusRing', '--vpa-control-focus-ring'],
  ['menuSurface', '--vpa-control-menu-surface'],
  ['menuHoverSurface', '--vpa-control-menu-hover-surface'],
  ['mutedForeground', '--vpa-control-muted-foreground'],
] as const satisfies readonly (readonly [keyof ControlPalette, `--vpa-${string}`])[]

export function applyControlTheme(document: Document, theme: Theme): void {
  const root = document.documentElement
  root.dataset.colorMode = theme.mode
  root.style.colorScheme = theme.mode
  for (const [key, property] of CONTROL_THEME_PROPERTIES) {
    root.style.setProperty(property, theme.controls[key])
  }
}
```

- [ ] **Step 4: Run the unit test and type checker; verify GREEN**

Run:

```bash
npx vitest run tests/app/control-theme.test.ts tests/app/theme-selection.test.ts --config vitest.config.ts
npm run typecheck
```

Expected: both theme tests PASS and TypeScript exits 0.

- [ ] **Step 5: Commit the palette authority**

```bash
git add src/view/paint.ts src/app/control-theme.ts tests/app/control-theme.test.ts
git commit -m "feat: define accessible control themes"
```

### Task 2: Persistent controls and application-selected mode

**Files:**
- Modify: `src/app/shell.ts:19-20,261-266`
- Modify: `src/app/relation-workspace.ts:603-605`
- Modify: `app/style.css:1-127`
- Create: `tests/architecture/control-theme-ownership.test.ts`

**Interfaces:**
- Consumes: `applyControlTheme(document, theme)` and all `--vpa-control-*` properties from Task 1.
- Produces: root-selected theme behavior and shared default/primary/disabled/focus CSS for persistent controls.

- [ ] **Step 1: Write the failing ownership test for the displaced persistent paths**

Create `tests/architecture/control-theme-ownership.test.ts`:

```ts
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
```

- [ ] **Step 2: Run the ownership test and verify RED**

Run:

```bash
npx vitest run tests/architecture/control-theme-ownership.test.ts --config vitest.config.ts
```

Expected: FAIL because the shell still writes `chrome.dataset.colorMode`, the CSS still contains `prefers-color-scheme` and chrome-scoped dark selectors, and semantic CSS variables are absent.

- [ ] **Step 3: Publish the selected theme from the shell**

Import `applyControlTheme` in `src/app/shell.ts` and make `applyThemeBackdrop` exactly synchronize DOM controls with the canvas theme:

```ts
import { applyControlTheme } from './control-theme'

const applyThemeBackdrop = (): void => {
  canvas.style.background = theme.canvas
  canvas.ownerDocument.documentElement.style.background = theme.canvas
  canvas.ownerDocument.body.style.background = theme.canvas
  applyControlTheme(canvas.ownerDocument, theme)
}
```

Delete `chrome.dataset.colorMode = theme.name.startsWith('Dark') ? 'dark' : 'light'`.

- [ ] **Step 4: Replace persistent button colors with semantic CSS**

Replace the inherited global button rule with:

```css
button, input { font: inherit; }
button {
  border: 1px solid var(--vpa-control-border);
  background: var(--vpa-control-surface);
  color: var(--vpa-control-foreground);
  cursor: pointer;
}
button:hover:not(:disabled) { background: var(--vpa-control-hover-surface); }
button:active:not(:disabled) { background: var(--vpa-control-active-surface); }
button:focus-visible { outline: 2px solid var(--vpa-control-focus-ring); outline-offset: 2px; }
button:disabled {
  border-color: var(--vpa-control-disabled-border);
  background: var(--vpa-control-disabled-surface);
  color: var(--vpa-control-disabled-foreground);
  cursor: default;
  opacity: 1;
}
.vpa-control-primary {
  border-color: var(--vpa-control-primary-border);
  background: var(--vpa-control-primary-surface);
  color: var(--vpa-control-primary-foreground);
  font-weight: 700;
}
.vpa-control-primary:hover:not(:disabled) { background: var(--vpa-control-primary-hover-surface); }
.vpa-control-primary:active:not(:disabled) { background: var(--vpa-control-primary-active-surface); }
```

Keep the existing compass/temporal padding and radius rule but delete its border/background declarations. Replace local button color declarations for `.vpa-fixed-side-declare`, `.vpa-relation-actions button`, `.vpa-relation-actions .is-primary`, and `.vpa-relation-empty-marker` with geometry only or shared semantic properties. Change the relation finalization class in `src/app/relation-workspace.ts`:

```ts
this.#finalizeButton.classList.add('vpa-control-primary')
```

Replace every `#chrome[data-color-mode="dark"]`, `body:has(#chrome[data-color-mode="dark"])`, and `@media (prefers-color-scheme: dark)` presentation selector with the application-selected root boundary:

```css
:root[data-color-mode="dark"] .vpa-compass-north,
:root[data-color-mode="dark"] .vpa-compass-surface,
:root[data-color-mode="dark"] .vpa-temporal,
:root[data-color-mode="dark"] .vpa-menu {
  color-scheme: dark;
  background: rgba(28,32,38,.96);
  color: #e6e1d6;
  border-color: rgba(230,225,214,.24);
}
:root[data-color-mode="dark"] .vpa-status,
:root[data-color-mode="dark"] .vpa-temporal-copy,
:root[data-color-mode="dark"] .vpa-ledger > header small { color: #b8b3aa; }
:root[data-color-mode="dark"] .vpa-fixed-side-workspace,
:root[data-color-mode="dark"] .vpa-proof-front { background: #0e1013; }
:root[data-color-mode="dark"] .vpa-proof-front-status,
:root[data-color-mode="dark"] .vpa-fixed-side-declare {
  color-scheme: dark;
  border-color: var(--vpa-control-border);
  background: var(--vpa-control-surface);
  color: var(--vpa-control-foreground);
}
:root[data-color-mode="dark"] .vpa-relation-workspace,
:root[data-color-mode="dark"] .vpa-relation-canvas { background: #121719; }
:root[data-color-mode="dark"] .vpa-relation-title,
:root[data-color-mode="dark"] .vpa-relation-port-strip {
  background: rgba(26,32,35,.97);
  color: #f59e0b;
  border-color: rgba(238,233,223,.2);
}
```

Apply the same `:root[data-color-mode="dark"]` prefix to fixed-side and relation-workspace panel selectors. Do not define control foreground/background values inside those dark selectors.

- [ ] **Step 5: Run ownership, theme, and type checks; verify GREEN**

Run:

```bash
npx vitest run tests/architecture/control-theme-ownership.test.ts tests/app/control-theme.test.ts tests/app/theme-selection.test.ts --config vitest.config.ts
npm run typecheck
```

Expected: all selected tests PASS and TypeScript exits 0.

- [ ] **Step 6: Commit persistent control migration**

```bash
git add src/app/shell.ts src/app/relation-workspace.ts app/style.css tests/architecture/control-theme-ownership.test.ts
git commit -m "feat: theme persistent controls"
```

### Task 3: Ephemeral menus and prompts

**Files:**
- Modify: `src/app/interact/spawn.ts:247-307,350-403`
- Modify: `src/app/interact/moves.ts:503-518,613-623`
- Modify: `src/app/interact/construct.ts:317-333`
- Modify: `app/style.css`
- Modify: `tests/architecture/control-theme-ownership.test.ts`

**Interfaces:**
- Consumes: semantic menu, muted, border, foreground, focus, and primary CSS properties from Task 1.
- Produces: class-driven spawn/proof/prompt presentation with no inline foreground/background/border or JavaScript hover mutation.

- [ ] **Step 1: Extend the ownership test to fail on inline control colors**

Append this test to `tests/architecture/control-theme-ownership.test.ts`:

```ts
const spawn = readFileSync('src/app/interact/spawn.ts', 'utf8')
const moves = readFileSync('src/app/interact/moves.ts', 'utf8')
const construct = readFileSync('src/app/interact/construct.ts', 'utf8')

it('keeps ephemeral control colors and states out of TypeScript', () => {
  for (const [name, source] of [['spawn', spawn], ['moves', moves], ['construct', construct]] as const) {
    expect(source, `${name} retains a light-only white control surface`).not.toMatch(/background:\s*#fff(?:;|`)/)
    expect(source, `${name} retains a JavaScript hover background mutation`).not.toMatch(/style\.background\s*=/)
  }
  expect(spawn).not.toContain("meta.style.color = '#a8a29e'")
  expect(moves).not.toMatch(/background:#fff|color:#78716c/)
  expect(construct).not.toMatch(/input\.style\.cssText\s*=.*(?:background|color|border)/)
})
```

- [ ] **Step 2: Run the ownership test and verify RED**

Run:

```bash
npx vitest run tests/architecture/control-theme-ownership.test.ts --config vitest.config.ts
```

Expected: FAIL on the existing white surfaces, inline muted foreground, pointer hover mutations, and bubble-input color string.

- [ ] **Step 3: Convert spawn menu presentation to semantic classes**

In `src/app/interact/spawn.ts`:

- retain inline `left` and `top` positioning only;
- delete color/background/border/box-shadow declarations from `column`, `search`, `submenu`, rows, metadata, and headings;
- add `vpa-spawn-meta` to metadata spans;
- add `is-interactive` to namespace group rows;
- delete `pointerenter`/`pointerleave` handlers that mutate `style.background`;
- publish binder hue only through a dedicated custom property:

```ts
meta.className = 'vpa-spawn-meta'
groupRow.classList.add('is-interactive')
swatch.style.setProperty('--vpa-binder-swatch', this.#binderColor(entry.binder, entry.source))
```

Add the complete class-driven presentation to `app/style.css`:

```css
.vpa-spawn-column, .vpa-spawn-submenu {
  overflow: hidden;
  border: 1.5px solid var(--vpa-control-primary-border);
  border-radius: 8px;
  background: var(--vpa-control-menu-surface);
  color: var(--vpa-control-foreground);
  box-shadow: 0 4px 16px rgba(0,0,0,.2);
}
.vpa-spawn-column { width: 220px; }
.vpa-spawn-submenu { display: none; width: 190px; max-height: 300px; margin-left: 2px; overflow-y: auto; }
.vpa-spawn-search {
  width: 100%; box-sizing: border-box; padding: 7px 10px; border: 0;
  border-bottom: 1px solid var(--vpa-control-border);
  outline: 0; background: var(--vpa-control-menu-surface);
  color: var(--vpa-control-foreground); font: 13px system-ui,sans-serif;
}
.vpa-spawn-listing { max-height: 270px; overflow-y: auto; }
.vpa-spawn-row {
  display: flex; width: 100%; box-sizing: border-box; justify-content: space-between;
  gap: 6px; padding: 6px 10px; border: 0; background: var(--vpa-control-menu-surface);
  color: var(--vpa-control-foreground); text-align: left; font: 13px system-ui,sans-serif;
}
button.vpa-spawn-row, .vpa-spawn-row.is-interactive { cursor: pointer; }
button.vpa-spawn-row:hover, .vpa-spawn-row.is-interactive:hover { background: var(--vpa-control-menu-hover-surface); }
.vpa-spawn-meta, .vpa-spawn-heading { color: var(--vpa-control-muted-foreground); }
.vpa-spawn-heading { padding: 6px 10px 3px; font: 10px system-ui,sans-serif; letter-spacing: .08em; text-transform: uppercase; }
.vpa-spawn-binder-swatch { background-color: var(--vpa-binder-swatch); box-shadow: 0 0 0 1px rgba(0,0,0,.2); }
```

- [ ] **Step 4: Convert proof menus and bubble prompts to semantic classes**

In `src/app/interact/moves.ts`, retain only dynamic `left`/`top` inline positioning. Let `.vpa-proof-menu`, `.vpa-proof-action`, `.vpa-proof-heading`, and `.vpa-proof-prompt input` own all static presentation in CSS.

In `src/app/interact/construct.ts`, delete the input's inline color string and publish only the refusal value for the non-button validation message:

```ts
problem.style.setProperty('--vpa-field-problem', theme.interaction.refusal)
```

Add:

```css
.vpa-proof-menu {
  position: fixed; z-index: 31; width: 270px; max-height: 380px; overflow: auto;
  border: 1.5px solid var(--vpa-control-primary-border); border-radius: 8px;
  background: var(--vpa-control-menu-surface); color: var(--vpa-control-foreground);
  box-shadow: 0 4px 16px rgba(0,0,0,.2); font: 13px system-ui;
}
.vpa-proof-action, .vpa-proof-heading {
  display: block; width: 100%; box-sizing: border-box; padding: 6px 10px;
  border: 0; background: var(--vpa-control-menu-surface); text-align: left;
}
.vpa-proof-action { color: var(--vpa-control-foreground); cursor: pointer; }
.vpa-proof-action:hover { background: var(--vpa-control-menu-hover-surface); }
.vpa-proof-heading { color: var(--vpa-control-muted-foreground); font-size: 10px; text-transform: uppercase; }
.vpa-proof-prompt input, .vpa-bubble-arity {
  padding: 5px 8px; border: 1.5px solid var(--vpa-control-focus-ring); border-radius: 6px;
  background: var(--vpa-control-menu-surface); color: var(--vpa-control-foreground);
}
.vpa-bubble-arity { width: 9rem; }
.vpa-field-problem { max-width: 14rem; color: var(--vpa-field-problem); font: 11px system-ui; }
```

- [ ] **Step 5: Run focused interaction tests and type checking; verify GREEN**

Run:

```bash
npx vitest run tests/architecture/control-theme-ownership.test.ts tests/app/actions.test.ts tests/app/abstraction-interaction.test.ts tests/app/relation-workspace.test.ts --config vitest.config.ts
npm run typecheck
```

Expected: selected tests PASS and TypeScript exits 0.

- [ ] **Step 6: Commit ephemeral control migration**

```bash
git add src/app/interact/spawn.ts src/app/interact/moves.ts src/app/interact/construct.ts app/style.css tests/architecture/control-theme-ownership.test.ts
git commit -m "feat: theme ephemeral controls"
```

### Task 4: Rendered regression coverage and full verification

**Files:**
- Create: `e2e/button-theme.spec.ts`
- Modify: `app/test/relation-workspace.ts:1-38,64-99,225-270`
- Modify: `e2e/relation-workspace.spec.ts:23-32`
- Modify only when the browser test identifies a real ownership defect: files owned by Tasks 1-3
- Append: `/tmp/visualproof-button-accessibility-foundation-20260722-002.md`

**Interfaces:**
- Consumes: `applyControlTheme`, `LIGHT`, `DARK`, the real app theme control, and production control surfaces from Tasks 1-3.
- Produces: a fixture `setTheme(mode: 'light' | 'dark'): void` seam and browser evidence for chrome, spawn, proof, temporal, fixed-side, and relation-workspace controls.

- [ ] **Step 1: Write the rendered contrast audit**

Create `e2e/button-theme.spec.ts`:

```ts
import { expect, test, type Locator, type Page } from '@playwright/test'

type RenderedControl = { color: string; background: string; border: string; contrast: number }

async function rendered(locator: Locator): Promise<RenderedControl> {
  return locator.evaluate((element) => {
    const parse = (css: string): [number, number, number, number] => {
      const values = css.match(/[\d.]+/g)?.map(Number) ?? []
      return [values[0] ?? 0, values[1] ?? 0, values[2] ?? 0, values[3] ?? 1]
    }
    const over = (front: number[], back: number[]): [number, number, number, number] => {
      const alpha = front[3]! + back[3]! * (1 - front[3]!)
      const channels = [0, 1, 2].map((index) => (
        front[index]! * front[3]! + back[index]! * back[3]! * (1 - front[3]!)
      ) / alpha)
      return [channels[0]!, channels[1]!, channels[2]!, alpha]
    }
    let effectiveBackground: [number, number, number, number] = [0, 0, 0, 0]
    for (let node: Element | null = element; node !== null; node = node.parentElement) {
      effectiveBackground = over(effectiveBackground, parse(getComputedStyle(node).backgroundColor))
    }
    effectiveBackground = over(effectiveBackground, [255, 255, 255, 1])
    const foreground = parse(getComputedStyle(element).color)
    const luminance = (rgba: number[]) => {
      const channels = rgba.slice(0, 3).map((channel) => {
        const normalized = channel! / 255
        return normalized <= 0.04045 ? normalized / 12.92 : ((normalized + 0.055) / 1.055) ** 2.4
      })
      return 0.2126 * channels[0]! + 0.7152 * channels[1]! + 0.0722 * channels[2]!
    }
    const foregroundLuminance = luminance(foreground)
    const backgroundLuminance = luminance(effectiveBackground)
    const style = getComputedStyle(element)
    return {
      color: style.color,
      background: style.backgroundColor,
      border: style.borderColor,
      contrast: (Math.max(foregroundLuminance, backgroundLuminance) + 0.05)
        / (Math.min(foregroundLuminance, backgroundLuminance) + 0.05),
    }
  })
}

async function expectAccessible(locator: Locator, threshold = 4.5): Promise<RenderedControl> {
  const value = await rendered(locator)
  expect(value.contrast).toBeGreaterThanOrEqual(threshold)
  return value
}

async function expectNoInlineControlColors(locator: Locator): Promise<void> {
  expect(await locator.evaluate((element) => {
    const style = (element as HTMLElement).style
    return { color: style.color, background: style.background, backgroundColor: style.backgroundColor, borderColor: style.borderColor }
  })).toEqual({ color: '', background: '', backgroundColor: '', borderColor: '' })
}

async function expectHoverChange(locator: Locator): Promise<void> {
  const before = await rendered(locator)
  await locator.hover()
  const after = await rendered(locator)
  expect(after.background).not.toBe(before.background)
  expect(after.contrast).toBeGreaterThanOrEqual(4.5)
}

async function openMode(page: Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
}

async function openSpawn(page: Page): Promise<Locator> {
  const canvas = (await page.locator('#c').boundingBox())!
  await page.mouse.click(canvas.x + canvas.width * 0.5, canvas.y + canvas.height * 0.5, { button: 'right' })
  return page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true })
}

async function proofBodyPoint(page: Page): Promise<{ x: number; y: number }> {
  const canvas = (await page.locator('#c').boundingBox())!
  const local = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  return { x: canvas.x + local.x, y: canvas.y + local.y }
}

test('Manuscript and Slate render accessible, distinct controls across app mount boundaries', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const utilities = page.getByRole('button', { name: 'Utilities', exact: true })
  const lightNavigation = await expectAccessible(utilities)
  await utilities.click()
  const themeButton = page.getByRole('button', { name: /Theme:/ })
  await expectAccessible(themeButton)
  await themeButton.click()
  await expect(page.locator('html')).toHaveAttribute('data-color-mode', 'dark')
  const darkNavigation = await expectAccessible(utilities)
  expect(darkNavigation.color).not.toBe(lightNavigation.color)
  expect(darkNavigation.background).not.toBe(lightNavigation.background)
  await expectHoverChange(utilities)
  await expectNoInlineControlColors(utilities)

  await utilities.click()
  const spawnRow = await openSpawn(page)
  await expectAccessible(spawnRow)
  await expectHoverChange(spawnRow)
  await expectNoInlineControlColors(spawnRow)
  await spawnRow.click()
  await page.getByLabel('Lambda term to spawn').fill('\\x. x')
  await page.getByLabel('Lambda term to spawn').press('Enter')

  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await expectAccessible(page.locator('.vpa-temporal-undo'))
  await expectAccessible(page.locator('.vpa-temporal-redo'))
  const body = await proofBodyPoint(page)
  await page.mouse.click(body.x, body.y)
  await page.mouse.click(body.x, body.y, { button: 'right' })
  const proofAction = page.locator('.vpa-proof-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true })
  await expectAccessible(proofAction)
  await expectHoverChange(proofAction)
  await expectNoInlineControlColors(proofAction)
  await page.keyboard.press('Escape')

  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()
  const declare = page.locator('.vpa-fixed-side-declare')
  await expect(declare).toBeEnabled()
  await expectAccessible(declare)
  await expectNoInlineControlColors(declare)
})

test('relation workspace default, primary, and disabled controls follow both themes', async ({ page }) => {
  await page.goto('/test/relation-workspace.html')
  await page.waitForFunction(() => window.relationWorkspaceFixture !== undefined)
  await page.evaluate(() => {
    window.relationWorkspaceFixture.setTheme('light')
    window.relationWorkspaceFixture.mount('abstract')
  })
  const cancel = page.getByRole('button', { name: 'Cancel', exact: true })
  const primary = page.getByRole('button', { name: 'Abstract', exact: true })
  const lightCancel = await expectAccessible(cancel)
  const lightPrimary = await expectAccessible(primary)
  await page.evaluate(() => window.relationWorkspaceFixture.setTheme('dark'))
  const darkCancel = await expectAccessible(cancel)
  const darkPrimary = await expectAccessible(primary)
  expect(darkCancel.background).not.toBe(lightCancel.background)
  expect(darkPrimary.background).not.toBe(lightPrimary.background)
  await expectHoverChange(primary)
  await expectNoInlineControlColors(cancel)
  await expectNoInlineControlColors(primary)

  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('invalid-ports'))
  const disabled = page.getByRole('button', { name: 'Abstract', exact: true })
  await expect(disabled).toBeDisabled()
  await expectAccessible(disabled, 3)
  await expectNoInlineControlColors(disabled)
})
```

- [ ] **Step 2: Run the browser test and verify the fixture seam is RED**

Run:

```bash
npx playwright test e2e/button-theme.spec.ts --project=chromium
```

Expected: FAIL because `relationWorkspaceFixture.setTheme` does not exist. If an app surface also fails contrast, mode differentiation, hover, or inline ownership, record that failure before changing production code.

- [ ] **Step 3: Add explicit theme selection to the relation-workspace harness**

In `app/test/relation-workspace.ts`, import `applyControlTheme`, `DARK`, and `Theme`; replace both hard-coded `theme: () => LIGHT` callbacks with `theme: () => activeTheme`; and add:

```ts
import { applyControlTheme } from '../../src/app/control-theme'
import { DARK, LIGHT, type Shape, type Theme } from '../../src/view/paint'

let activeTheme: Theme = LIGHT
applyControlTheme(document, activeTheme)

function setTheme(mode: Theme['mode']): void {
  activeTheme = mode === 'dark' ? DARK : LIGHT
  applyControlTheme(document, activeTheme)
  workspace?.frame(performance.now())
}
```

Add `setTheme(mode: Theme['mode']): void` to the fixture's declared type and `setTheme` to `window.relationWorkspaceFixture`. Add the same method to the existing fixture declaration in `e2e/relation-workspace.spec.ts`:

```ts
setTheme(mode: 'light' | 'dark'): void
```

- [ ] **Step 4: Run the rendered audit and correct only observed ownership defects**

Run:

```bash
npx playwright test e2e/button-theme.spec.ts --project=chromium
```

Expected: PASS. For any failure, trace the computed style to its owning selector or inline assignment, remove that competing path, and map the component to an existing semantic property. Do not add fallback colors or component-local dark overrides. Re-run this command after each correction.

- [ ] **Step 5: Run complete validation**

Run fresh:

```bash
npm test
npm run typecheck
npx playwright test --project=chromium
git diff --check
git status --short
```

Expected: Vitest reports zero failures, TypeScript exits 0, all Chromium Playwright tests pass, `git diff --check` prints nothing, and status lists only task-owned uncommitted files before the final commit.

- [ ] **Step 6: Append foundation conformance evidence**

Append a `<conformance>` section to `/tmp/visualproof-button-accessibility-foundation-20260722-002.md` without modifying earlier sections. State the implemented owner (`Theme.controls`), publisher (`applyControlTheme`), every migrated surface, every deleted competing path, the exact Step 5 results, the lowest measured Light/Dark rendered contrast, and the repository searches proving inline and selector paths are absent.

- [ ] **Step 7: Commit the verified implementation**

```bash
git add e2e/button-theme.spec.ts e2e/relation-workspace.spec.ts app/test/relation-workspace.ts app/style.css src/app src/view/paint.ts tests/app/control-theme.test.ts tests/architecture/control-theme-ownership.test.ts
git commit -m "test: prove accessible themed controls"
```

- [ ] **Step 8: Verify the committed repository is clean**

Run:

```bash
git status --short
git log -4 --oneline
```

Expected: status is empty and the log contains the palette, persistent controls, ephemeral controls, and rendered-regression commits.
