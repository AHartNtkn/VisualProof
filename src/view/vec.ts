export type Vec2 = { readonly x: number; readonly y: number }

export function vec(x: number, y: number): Vec2 {
  return { x, y }
}

export function add(a: Vec2, b: Vec2): Vec2 {
  return { x: a.x + b.x, y: a.y + b.y }
}

export function sub(a: Vec2, b: Vec2): Vec2 {
  return { x: a.x - b.x, y: a.y - b.y }
}

export function scale(a: Vec2, k: number): Vec2 {
  return { x: a.x * k, y: a.y * k }
}

export function length(a: Vec2): number {
  return Math.hypot(a.x, a.y)
}

export function polar(angle: number, r: number): Vec2 {
  return { x: Math.cos(angle) * r, y: Math.sin(angle) * r }
}
