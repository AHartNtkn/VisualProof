import type { Diagram, RegionId } from '../../kernel/diagram/diagram'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import { legPaths, wireOwnedEnds } from '../../view/wires'

export function copyRegionAt(
  engine: Engine,
  diagram: Diagram,
  point: { readonly x: number; readonly y: number },
): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (
      Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)
    ) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

export function copyDestinationPreview(
  engine: Engine,
  region: RegionId,
  theme: Theme,
): readonly Shape[] {
  const geometry = engine.regions.get(region)
  if (geometry === undefined) return []
  const color = theme.interaction.valid
  return [{
    kind: 'circle',
    center: geometry.center,
    r: geometry.radius,
    fill: `${color}22`,
    stroke: color,
    width: 2.4,
    insetColor: null,
    glow: null,
  }]
}

export function copySelectionPreview(
  engine: Engine,
  selection: SubgraphSelection,
  theme: Theme,
): readonly Shape[] {
  const discs: Array<{
    readonly center: { readonly x: number; readonly y: number }
    readonly r: number
  }> = []
  for (const node of selection.nodes) {
    const body = engine.bodies.get(node)
    if (body !== undefined) {
      discs.push({ center: body.pos, r: body.discR * engine.scale + 2 })
    }
  }
  for (const region of selection.regions) {
    const geometry = engine.regions.get(region)
    if (geometry !== undefined) {
      discs.push({ center: geometry.center, r: geometry.radius + 2 })
    }
  }
  const wires = new Set(selection.wires)
  for (const path of legPaths(engine)) {
    if (wires.has(path.wid)) {
      for (const point of path.pts) discs.push({ center: point, r: 2 })
    }
  }
  for (const { wid, body } of wireOwnedEnds(engine)) {
    if (wires.has(wid)) {
      discs.push({ center: body.pos, r: body.discR * engine.scale + 2 })
    }
  }
  if (discs.length === 0) return []
  const left = Math.min(...discs.map((disc) => disc.center.x - disc.r))
  const right = Math.max(...discs.map((disc) => disc.center.x + disc.r))
  const top = Math.min(...discs.map((disc) => disc.center.y - disc.r))
  const bottom = Math.max(...discs.map((disc) => disc.center.y + disc.r))
  const center = { x: (left + right) / 2, y: (top + bottom) / 2 }
  const radius = Math.max(...discs.map((disc) =>
    Math.hypot(disc.center.x - center.x, disc.center.y - center.y) + disc.r))
  return [{
    kind: 'circle',
    center,
    r: radius,
    fill: null,
    stroke: theme.interaction.valid,
    width: 2.5,
    insetColor: null,
    glow: null,
  }]
}
