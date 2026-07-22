import { describe, expect, it } from 'vitest'
import { applyControlTheme, CONTROL_THEME_PROPERTIES } from '../../src/app/control-theme'
import { DARK, LIGHT, type ControlPalette } from '../../src/view/paint'

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
