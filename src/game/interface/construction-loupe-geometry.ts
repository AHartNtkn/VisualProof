import type { Vec2 } from '../../view/vec'

export type ViewportSize = { readonly width: number; readonly height: number }
export type LoupeGeometry = { readonly center: Vec2; readonly diameter: number }
export type LoupeRect = { readonly left: number; readonly top: number; readonly width: number; readonly height: number }
export type LoupeHit = 'outside' | 'aperture' | 'rim' | 'terminal'
export type LoupeResize = { readonly anchor: Vec2; readonly initial: LoupeGeometry }

export const LOUPE_PREFERRED_DIAMETER = 520
export const LOUPE_MIN_DIAMETER = 144
export const LOUPE_MAX_DIAMETER = 760

// Candidate A's handle ends southeast of the circular aperture. Keeping this
// point and its complete hit target on-screen is part of the semantic bounds.
const TERMINAL_AXIS_FACTOR = 0.64
const ANCHOR_AXIS_FACTOR = 0.5 / Math.SQRT2
const RESIZE_AXIS_SPAN = TERMINAL_AXIS_FACTOR + ANCHOR_AXIS_FACTOR
const RESIZE_PROJECTED_SPAN = RESIZE_AXIS_SPAN * Math.SQRT2

const finiteSize = (size: ViewportSize): ViewportSize => {
  if (!Number.isFinite(size.width) || !Number.isFinite(size.height) || size.width <= 0 || size.height <= 0) {
    throw new RangeError('loupe viewport dimensions must be finite and positive')
  }
  return size
}

const clamp = (value: number, min: number, max: number): number =>
  Math.max(min, Math.min(Math.max(min, max), value))

export const loupeTerminalRadius = (diameter: number): number => Math.max(9, diameter * 0.026)
export const loupeRimHitWidth = (diameter: number): number => Math.max(12, diameter * 0.04)

function reachableSpan(diameter: number): number {
  const rimExtent = diameter / 2 + loupeRimHitWidth(diameter)
  const positiveExtent = Math.max(
    rimExtent,
    TERMINAL_AXIS_FACTOR * diameter + loupeTerminalRadius(diameter),
  )
  return rimExtent + positiveExtent
}

function maximumReachableDiameter(viewport: ViewportSize): number {
  const size = finiteSize(viewport)
  const limit = Math.min(size.width, size.height)
  if (limit < reachableSpan(Number.EPSILON)) throw new RangeError('loupe viewport is too small to keep its controls reachable')
  let low = Number.EPSILON
  let high = LOUPE_MAX_DIAMETER
  for (let iteration = 0; iteration < 64; iteration++) {
    const candidate = (low + high) / 2
    if (reachableSpan(candidate) <= limit) low = candidate
    else high = candidate
  }
  return low
}

function supportedDiameter(requested: number, viewport: ViewportSize): number {
  if (!Number.isFinite(requested) || requested <= 0) throw new RangeError('loupe diameter must be finite and positive')
  const available = maximumReachableDiameter(viewport)
  return clamp(requested, Math.min(LOUPE_MIN_DIAMETER, available), available)
}

function clampGeometry(center: Vec2, requestedDiameter: number, viewport: ViewportSize): LoupeGeometry {
  const size = finiteSize(viewport)
  const diameter = supportedDiameter(requestedDiameter, size)
  const radius = diameter / 2
  const rimExtent = radius + loupeRimHitWidth(diameter)
  const terminalExtent = TERMINAL_AXIS_FACTOR * diameter + loupeTerminalRadius(diameter)
  const positiveExtent = Math.max(rimExtent, terminalExtent)
  return {
    center: {
      x: clamp(center.x, rimExtent, size.width - positiveExtent),
      y: clamp(center.y, rimExtent, size.height - positiveExtent),
    },
    diameter,
  }
}

export function placeConstructionLoupe(
  invocation: Vec2,
  viewport: ViewportSize,
  preferredDiameter = LOUPE_PREFERRED_DIAMETER,
): LoupeGeometry {
  const diameter = supportedDiameter(preferredDiameter, viewport)
  return clampGeometry({
    x: invocation.x + diameter * 0.1,
    y: invocation.y + diameter * 0.06,
  }, diameter, viewport)
}

export function loupeApertureRect(geometry: LoupeGeometry): LoupeRect {
  const radius = geometry.diameter / 2
  return {
    left: geometry.center.x - radius,
    top: geometry.center.y - radius,
    width: geometry.diameter,
    height: geometry.diameter,
  }
}

export function loupeTerminalPoint(geometry: LoupeGeometry): Vec2 {
  return {
    x: geometry.center.x + geometry.diameter * TERMINAL_AXIS_FACTOR,
    y: geometry.center.y + geometry.diameter * TERMINAL_AXIS_FACTOR,
  }
}

export function moveConstructionLoupe(
  geometry: LoupeGeometry,
  delta: Vec2,
  viewport: ViewportSize,
): LoupeGeometry {
  return clampGeometry({ x: geometry.center.x + delta.x, y: geometry.center.y + delta.y }, geometry.diameter, viewport)
}

export function beginLoupeResize(geometry: LoupeGeometry): LoupeResize {
  return {
    initial: geometry,
    anchor: {
      x: geometry.center.x - geometry.diameter * ANCHOR_AXIS_FACTOR,
      y: geometry.center.y - geometry.diameter * ANCHOR_AXIS_FACTOR,
    },
  }
}

export function resizeConstructionLoupe(
  drag: LoupeResize,
  terminal: Vec2,
  viewport: ViewportSize,
): LoupeGeometry {
  const alongDiagonal = ((terminal.x - drag.anchor.x) + (terminal.y - drag.anchor.y)) / Math.SQRT2
  const requested = alongDiagonal / RESIZE_PROJECTED_SPAN
  const diameter = supportedDiameter(Math.max(Number.EPSILON, requested), viewport)
  return clampGeometry({
    x: drag.anchor.x + diameter * ANCHOR_AXIS_FACTOR,
    y: drag.anchor.y + diameter * ANCHOR_AXIS_FACTOR,
  }, diameter, viewport)
}

export function hitConstructionLoupe(geometry: LoupeGeometry, client: Vec2): LoupeHit {
  const terminal = loupeTerminalPoint(geometry)
  if (Math.hypot(client.x - terminal.x, client.y - terminal.y) <= loupeTerminalRadius(geometry.diameter)) return 'terminal'
  const distance = Math.hypot(client.x - geometry.center.x, client.y - geometry.center.y)
  const radius = geometry.diameter / 2
  const rimWidth = loupeRimHitWidth(geometry.diameter)
  if (Math.abs(distance - radius) <= rimWidth) return 'rim'
  return distance < radius - rimWidth ? 'aperture' : 'outside'
}

export function clientToLoupeDraft(
  client: Vec2,
  canvasRect: LoupeRect,
  canvasPixels: ViewportSize,
  view: { readonly scale: number; readonly offsetX: number; readonly offsetY: number },
): { readonly screen: Vec2; readonly world: Vec2 } {
  if (canvasRect.width <= 0 || canvasRect.height <= 0 || view.scale <= 0 || !Number.isFinite(view.scale)) {
    throw new RangeError('loupe canvas rectangle and view scale must be positive')
  }
  const screen = {
    x: (client.x - canvasRect.left) * canvasPixels.width / canvasRect.width,
    y: (client.y - canvasRect.top) * canvasPixels.height / canvasRect.height,
  }
  return {
    screen,
    world: {
      x: (screen.x - view.offsetX) / view.scale,
      y: (screen.y - view.offsetY) / view.scale,
    },
  }
}
