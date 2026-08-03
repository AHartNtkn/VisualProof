import { describe, expect, it } from 'vitest'
import { applyControlTheme, CONTROL_THEME_PROPERTIES } from '../../src/app/control-theme'
import { DARK, LIGHT, type ControlPalette } from '../../src/view/paint'

function luminance(hex: string): number {
  const channels = [1, 3, 5].map((start) => Number.parseInt(hex.slice(start, start + 2), 16) / 255)
  const [red, green, blue] = channels.map((channel) => channel <= 0.04045
    ? channel / 12.92
    : ((channel + 0.055) / 1.055) ** 2.4)
  return 0.2126 * red! + 0.7152 * green! + 0.0722 * blue!
}

function contrast(foreground: string, background: string): number {
  const [a, b] = [luminance(foreground), luminance(background)]
  return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05)
}

const readablePairs = (controls: ControlPalette): readonly (readonly [string, string])[] => [
  [controls.foreground, controls.surface],
  [controls.primaryForeground, controls.primarySurface],
  [controls.mutedForeground, controls.menuSurface],
]

describe.each([LIGHT, DARK])('$name controls', (theme) => {
  it('keeps the formula control text palette at WCAG AA contrast', () => {
    for (const pair of readablePairs(theme.controls)) expect(contrast(...pair)).toBeGreaterThanOrEqual(4.5)
    expect(contrast(theme.interaction.refusal, theme.controls.menuSurface)).toBeGreaterThanOrEqual(4.5)
  })
})

it('projects the selected palette, refusal color, and mode onto the document root', () => {
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
  const expected = new Map<string, string>()
  for (const [key, property] of CONTROL_THEME_PROPERTIES) expected.set(property, DARK.controls[key])
  expected.set('--vpa-formula-error', DARK.interaction.refusal)
  expect(declarations).toEqual(expected)
})
