import { Color } from 'three'

export type HeldColorViolation = {
  readonly property: string
  readonly value: string
  readonly color: string
}

const COLOR_PROPERTIES = new Set([
  'accent-color',
  'background',
  'background-color',
  'background-image',
  'backdrop-filter',
  'border',
  'border-block',
  'border-block-color',
  'border-block-end',
  'border-block-end-color',
  'border-block-start',
  'border-block-start-color',
  'border-bottom',
  'border-bottom-color',
  'border-color',
  'border-inline',
  'border-inline-color',
  'border-inline-end',
  'border-inline-end-color',
  'border-inline-start',
  'border-inline-start-color',
  'border-image',
  'border-image-source',
  'border-left',
  'border-left-color',
  'border-right',
  'border-right-color',
  'border-top',
  'border-top-color',
  'box-shadow',
  'caret-color',
  'color',
  'column-rule',
  'column-rule-color',
  'fill',
  'filter',
  'flood-color',
  'lighting-color',
  'list-style-image',
  'mask',
  'mask-border',
  'mask-image',
  'outline',
  'outline-color',
  'stop-color',
  'stroke',
  'text-decoration',
  'text-decoration-color',
  'text-emphasis',
  'text-emphasis-color',
  'text-shadow',
  '-webkit-mask',
  '-webkit-mask-image',
  '-webkit-text-fill-color',
  '-webkit-text-stroke',
  '-webkit-text-stroke-color',
])

const COLOR_FUNCTIONS = new Set([
  'color',
  'device-cmyk',
  'hsl',
  'hsla',
  'hwb',
  'lab',
  'lch',
  'oklab',
  'oklch',
  'rgb',
  'rgba',
])

const SYSTEM_COLORS = new Set([
  'accentcolor',
  'accentcolortext',
  'activetext',
  'buttonborder',
  'buttonface',
  'buttontext',
  'canvas',
  'canvastext',
  'field',
  'fieldtext',
  'graytext',
  'highlight',
  'highlighttext',
  'linktext',
  'mark',
  'marktext',
  'selecteditem',
  'selecteditemtext',
  'visitedtext',
])

const NEUTRAL_OR_STRUCTURAL_FUNCTIONS = new Set([
  'blur',
  'brightness',
  'calc',
  'clamp',
  'color-mix',
  'conic-gradient',
  'contrast',
  'drop-shadow',
  'grayscale',
  'light-dark',
  'linear-gradient',
  'max',
  'min',
  'opacity',
  'radial-gradient',
  'repeating-conic-gradient',
  'repeating-linear-gradient',
  'repeating-radial-gradient',
])

type ColorScan = {
  readonly colors: number
  readonly violations: readonly string[]
}

export function heldColorAuthorityViolations(stylesheet: string): readonly HeldColorViolation[] {
  const violations: HeldColorViolation[] = []

  for (const rule of cssRules(stylesheet)) {
    if (!rule.selector.includes('.held-tool-silhouette')) continue

    for (const declaration of declarations(rule.body)) {
      if (!colorBearingProperty(declaration.property)) continue

      const scan = scanColors(declaration.value)
      for (const color of scan.violations) {
        violations.push({ ...declaration, color })
      }

      if (requiresExplicitColor(declaration.property) && scan.colors === 0 && scan.violations.length === 0) {
        violations.push({ ...declaration, color: declaration.value })
      }
    }
  }

  return violations
}

function cssRules(stylesheet: string): readonly { selector: string; body: string }[] {
  const source = stylesheet.replace(/\/\*[\s\S]*?\*\//g, '')
  const rules: { selector: string; body: string }[] = []
  let cursor = 0

  while (cursor < source.length) {
    const open = source.indexOf('{', cursor)
    if (open < 0) break
    const close = matching(source, open, '{', '}')
    if (close < 0) break

    const selectorStart = Math.max(source.lastIndexOf('}', open - 1), 0)
    const selector = source.slice(selectorStart === 0 ? 0 : selectorStart + 1, open).trim()
    const body = source.slice(open + 1, close)
    if (selector.startsWith('@')) rules.push(...cssRules(body))
    else rules.push({ selector, body })
    cursor = close + 1
  }

  return rules
}

function declarations(body: string): readonly { property: string; value: string }[] {
  return splitTopLevel(body, ';').flatMap((source) => {
    const colon = topLevelIndex(source, ':')
    if (colon < 0) return []
    const property = source.slice(0, colon).trim().toLowerCase()
    const value = source.slice(colon + 1).trim()
    return property && value ? [{ property, value }] : []
  })
}

function scanColors(value: string): ColorScan {
  const violations: string[] = []
  let colors = 0
  let cursor = 0

  while (cursor < value.length) {
    if (value[cursor] === '#') {
      const match = value.slice(cursor).match(/^#(?:[0-9a-f]{8}|[0-9a-f]{6}|[0-9a-f]{4}|[0-9a-f]{3})(?![0-9a-f])/i)
      if (match) {
        colors += 1
        if (!neutralHex(match[0])) violations.push(match[0])
        cursor += match[0].length
        continue
      }
    }

    if (identifierStart(value[cursor])) {
      const start = cursor
      cursor += 1
      while (cursor < value.length && identifierPart(value[cursor])) cursor += 1
      const identifier = value.slice(start, cursor)
      const normalized = identifier.toLowerCase()
      let functionOpen = cursor
      while (/\s/.test(value[functionOpen] ?? '')) functionOpen += 1

      if (value[functionOpen] === '(') {
        const functionClose = matching(value, functionOpen, '(', ')')
        if (functionClose < 0) {
          violations.push(value.slice(start).trim())
          break
        }

        const literal = value.slice(start, functionClose + 1)
        const argumentsText = value.slice(functionOpen + 1, functionClose)
        if (COLOR_FUNCTIONS.has(normalized)) {
          colors += 1
          if (!neutralFunction(normalized, argumentsText)) violations.push(literal)
        } else if (normalized === 'var') {
          if (argumentsText.trim() !== '--held-size') violations.push(literal)
        } else if (NEUTRAL_OR_STRUCTURAL_FUNCTIONS.has(normalized)) {
          const nested = scanColors(argumentsText)
          colors += nested.colors
          violations.push(...nested.violations)
        } else {
          violations.push(literal)
        }
        cursor = functionClose + 1
        continue
      }

      if (normalized === 'currentcolor' || normalized === 'transparent') {
        colors += 1
      } else if (SYSTEM_COLORS.has(normalized)) {
        colors += 1
        violations.push(identifier)
      } else if (namedColor(normalized) !== undefined) {
        colors += 1
        if (!neutralRgbInteger(namedColor(normalized)!)) violations.push(identifier)
      }
      continue
    }

    cursor += 1
  }

  return { colors, violations }
}

function neutralFunction(name: string, source: string): boolean {
  if (name === 'device-cmyk') return false
  const channels = functionChannels(source)

  switch (name) {
    case 'rgb':
    case 'rgba': {
      const rgb = channels.slice(0, 3).map(rgbChannel)
      return rgb.length === 3 && rgb.every(isNumber) && equal(rgb[0]!, rgb[1]!) && equal(rgb[1]!, rgb[2]!)
    }
    case 'hsl':
    case 'hsla':
      return channels.length >= 3 && zero(channels[1]!)
    case 'hwb': {
      const whiteness = percentage(channels[1])
      const blackness = percentage(channels[2])
      return whiteness !== undefined && blackness !== undefined && whiteness + blackness >= 1
    }
    case 'lab':
    case 'oklab':
      return channels.length >= 3 && zero(channels[1]!) && zero(channels[2]!)
    case 'lch':
    case 'oklch':
      return channels.length >= 3 && zero(channels[1]!)
    case 'color': {
      const [space, ...components] = channels
      if (!['srgb', 'srgb-linear', 'display-p3', 'a98-rgb', 'prophoto-rgb', 'rec2020'].includes(space ?? '')) {
        return false
      }
      const rgb = components.slice(0, 3).map(unitChannel)
      return rgb.length === 3 && rgb.every(isNumber) && equal(rgb[0]!, rgb[1]!) && equal(rgb[1]!, rgb[2]!)
    }
  }

  return false
}

function functionChannels(source: string): readonly string[] {
  const beforeAlpha = splitTopLevel(source, '/')[0] ?? ''
  return beforeAlpha.split(/[\s,]+/).filter(Boolean).map((channel) => channel.toLowerCase())
}

function namedColor(name: string): number | undefined {
  return Color.NAMES[name as keyof typeof Color.NAMES]
}

function neutralRgbInteger(rgb: number): boolean {
  return ((rgb >> 16) & 0xff) === ((rgb >> 8) & 0xff) && ((rgb >> 8) & 0xff) === (rgb & 0xff)
}

function neutralHex(color: string): boolean {
  const digits = color.slice(1)
  const channels = digits.length <= 4
    ? [...digits.slice(0, 3)].map((digit) => Number.parseInt(`${digit}${digit}`, 16))
    : [digits.slice(0, 2), digits.slice(2, 4), digits.slice(4, 6)].map((pair) => Number.parseInt(pair, 16))
  return channels[0] === channels[1] && channels[1] === channels[2]
}

function rgbChannel(channel: string): number | undefined {
  const percent = percentage(channel)
  if (percent !== undefined) return percent
  const number = numeric(channel)
  return number === undefined ? undefined : number / 255
}

function unitChannel(channel: string): number | undefined {
  return percentage(channel) ?? numeric(channel)
}

function percentage(channel: string | undefined): number | undefined {
  if (!channel?.endsWith('%')) return undefined
  const value = numeric(channel.slice(0, -1))
  return value === undefined ? undefined : value / 100
}

function numeric(channel: string | undefined): number | undefined {
  if (!channel || !/^[+-]?(?:\d+\.?\d*|\.\d+)(?:e[+-]?\d+)?$/i.test(channel)) return undefined
  const value = Number(channel)
  return Number.isFinite(value) ? value : undefined
}

function zero(channel: string): boolean {
  const value = channel.endsWith('%') ? percentage(channel) : numeric(channel)
  return value !== undefined && equal(value, 0)
}

function equal(left: number, right: number): boolean {
  return Math.abs(left - right) < 1e-9
}

function isNumber(value: number | undefined): value is number {
  return value !== undefined
}

function requiresExplicitColor(property: string): boolean {
  return property === 'color' || property.endsWith('-color') || ['accent-color', 'caret-color', 'fill', 'stroke'].includes(property)
}

function colorBearingProperty(property: string): boolean {
  return COLOR_PROPERTIES.has(property) || property.endsWith('-color')
}

function splitTopLevel(source: string, separator: string): readonly string[] {
  const parts: string[] = []
  let start = 0
  let depth = 0
  for (let cursor = 0; cursor < source.length; cursor += 1) {
    if (source[cursor] === '(') depth += 1
    else if (source[cursor] === ')') depth -= 1
    else if (source[cursor] === separator && depth === 0) {
      parts.push(source.slice(start, cursor).trim())
      start = cursor + 1
    }
  }
  parts.push(source.slice(start).trim())
  return parts
}

function topLevelIndex(source: string, target: string): number {
  let depth = 0
  for (let cursor = 0; cursor < source.length; cursor += 1) {
    if (source[cursor] === '(') depth += 1
    else if (source[cursor] === ')') depth -= 1
    else if (source[cursor] === target && depth === 0) return cursor
  }
  return -1
}

function matching(source: string, open: number, left: string, right: string): number {
  let depth = 0
  for (let cursor = open; cursor < source.length; cursor += 1) {
    if (source[cursor] === left) depth += 1
    else if (source[cursor] === right) {
      depth -= 1
      if (depth === 0) return cursor
    }
  }
  return -1
}

function identifierStart(character: string | undefined): boolean {
  return character !== undefined && /[a-z_-]/i.test(character)
}

function identifierPart(character: string | undefined): boolean {
  return character !== undefined && /[a-z0-9_-]/i.test(character)
}
