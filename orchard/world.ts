import type { WireId } from '../src/kernel/diagram/diagram'
import type { Entity, Scene3 } from '../src/view3d/scene'
import type { Vec3 } from '../src/view3d/vec3'

export type SavedTerrain = {
  readonly size: number
  readonly ground: string
  readonly sky: string
  readonly fogNear: number
  readonly fogFar: number
  readonly bounds: SavedBounds
}

export type SavedBounds = {
  readonly minX: number
  readonly maxX: number
  readonly minZ: number
  readonly maxZ: number
}

export type SavedPlayer = {
  readonly x: number
  readonly y: number
  readonly z: number
  readonly yaw: number
  readonly pitch: number
}

export type SavedTree = {
  readonly id: string
  readonly layout: string
  readonly x: number
  readonly z: number
  readonly yaw: number
}

export type SavedTreeLayout = {
  readonly label: string
  readonly bounds: { readonly center: Vec3; readonly radius: number }
  readonly lods: SavedTreeLods
  readonly hues: readonly (readonly [WireId, string])[]
  readonly palette: SavedTreePalette
  readonly widths: { readonly branch: number; readonly curve: number }
  readonly glow: { readonly color: string; readonly radius: number; readonly opacity: number; readonly bloom: number }
}

export type SavedTreeLods = {
  readonly full: Scene3
  readonly reduced: Scene3
  readonly marker: { readonly color: string; readonly size: number }
}

export type SavedTreePalette = {
  readonly branch: string
  readonly cutBranch: string
  readonly baseWire: string
}

export type OrchardWorldSave = {
  readonly version: 2
  readonly terrain: SavedTerrain
  readonly player: SavedPlayer
  readonly layouts: Readonly<Record<string, SavedTreeLayout>>
  readonly trees: readonly SavedTree[]
}

const isRecord = (value: unknown): value is Record<string, unknown> =>
  typeof value === 'object' && value !== null && !Array.isArray(value)

const finite = (value: unknown, field: string): number => {
  if (typeof value !== 'number' || !Number.isFinite(value)) throw new Error(`invalid orchard save: ${field}`)
  return value
}

const text = (value: unknown, field: string): string => {
  if (typeof value !== 'string' || value.length === 0) throw new Error(`invalid orchard save: ${field}`)
  return value
}

const vec3 = (value: unknown, field: string): { x: number; y: number; z: number } => {
  if (!isRecord(value)) throw new Error(`invalid orchard save: ${field}`)
  return {
    x: finite(value['x'], `${field}.x`),
    y: finite(value['y'], `${field}.y`),
    z: finite(value['z'], `${field}.z`),
  }
}

const entity = (value: unknown, field: string): Entity => {
  if (!isRecord(value)) throw new Error(`invalid orchard save: ${field}`)
  const kind = value['kind']
  const key = text(value['key'], `${field}.key`)
  if (kind === 'branch' || kind === 'ring' || kind === 'strand') {
    if (!Array.isArray(value['pts']) || value['pts'].length < 2) throw new Error(`invalid orchard save: ${field}.pts`)
    const pts = value['pts'].map((point, index) => vec3(point, `${field}.pts[${index}]`))
    if (kind === 'branch') {
      const polarity = value['polarity']
      if (polarity !== 0 && polarity !== 1) throw new Error(`invalid orchard save: ${field}.polarity`)
      return { kind, key, polarity, pts }
    }
    if (kind === 'ring') {
      const headWire = value['headWire']
      if (headWire !== null && typeof headWire !== 'string') throw new Error(`invalid orchard save: ${field}.headWire`)
      return { kind, key, node: text(value['node'], `${field}.node`), headWire, pts }
    }
    return { kind, key, wire: text(value['wire'], `${field}.wire`), pts }
  }
  if (kind === 'pip' || kind === 'label') {
    const pos = vec3(value['pos'], `${field}.pos`)
    const node = text(value['node'], `${field}.node`)
    if (kind === 'label') return { kind, key, node, text: text(value['text'], `${field}.text`), pos }
    const ownerWire = value['ownerWire']
    if (ownerWire !== null && typeof ownerWire !== 'string') throw new Error(`invalid orchard save: ${field}.ownerWire`)
    return { kind, key, node, ownerWire, pos }
  }
  throw new Error(`invalid orchard save: ${field}.kind`)
}

const positive = (value: unknown, field: string): number => {
  const number = finite(value, field)
  if (number <= 0) throw new Error(`invalid orchard save: ${field}`)
  return number
}

const nonnegative = (value: unknown, field: string): number => {
  const number = finite(value, field)
  if (number < 0) throw new Error(`invalid orchard save: ${field}`)
  return number
}

const scene = (value: unknown, field: string): Scene3 => {
  if (!isRecord(value) || !Array.isArray(value['entities'])) throw new Error(`invalid orchard save: ${field}`)
  return {
    center: vec3(value['center'], `${field}.center`),
    radius: positive(value['radius'], `${field}.radius`),
    entities: value['entities'].map((item, index) => entity(item, `${field}.entities[${index}]`)),
  }
}

export function parseWorldSave(value: unknown): OrchardWorldSave {
  if (!isRecord(value) || value['version'] !== 2) throw new Error('invalid orchard save: version')
  const terrainRaw = value['terrain'], playerRaw = value['player'], layoutsRaw = value['layouts']
  if (!isRecord(terrainRaw)) throw new Error('invalid orchard save: terrain')
  if (!isRecord(playerRaw)) throw new Error('invalid orchard save: player')
  if (!isRecord(layoutsRaw)) throw new Error('invalid orchard save: layouts')
  if (!isRecord(terrainRaw['bounds'])) throw new Error('invalid orchard save: terrain.bounds')
  if (!Array.isArray(value['trees'])) throw new Error('invalid orchard save: trees')

  const terrain: SavedTerrain = {
    size: finite(terrainRaw['size'], 'terrain.size'),
    ground: text(terrainRaw['ground'], 'terrain.ground'),
    sky: text(terrainRaw['sky'], 'terrain.sky'),
    fogNear: finite(terrainRaw['fogNear'], 'terrain.fogNear'),
    fogFar: finite(terrainRaw['fogFar'], 'terrain.fogFar'),
    bounds: {
      minX: finite(terrainRaw['bounds']['minX'], 'terrain.bounds.minX'),
      maxX: finite(terrainRaw['bounds']['maxX'], 'terrain.bounds.maxX'),
      minZ: finite(terrainRaw['bounds']['minZ'], 'terrain.bounds.minZ'),
      maxZ: finite(terrainRaw['bounds']['maxZ'], 'terrain.bounds.maxZ'),
    },
  }
  if (terrain.bounds.minX > terrain.bounds.maxX || terrain.bounds.minZ > terrain.bounds.maxZ) {
    throw new Error('invalid orchard save: terrain.bounds order')
  }
  const player: SavedPlayer = {
    x: finite(playerRaw['x'], 'player.x'),
    y: finite(playerRaw['y'], 'player.y'),
    z: finite(playerRaw['z'], 'player.z'),
    yaw: finite(playerRaw['yaw'], 'player.yaw'),
    pitch: finite(playerRaw['pitch'], 'player.pitch'),
  }
  const layouts: Record<string, SavedTreeLayout> = {}
  for (const [layoutId, raw] of Object.entries(layoutsRaw)) {
    if (!isRecord(raw) || !isRecord(raw['bounds']) || !isRecord(raw['lods']) || !Array.isArray(raw['hues']) || !isRecord(raw['palette']) || !isRecord(raw['widths']) || !isRecord(raw['glow'])) {
      throw new Error(`invalid orchard save: layouts.${layoutId}`)
    }
    if (!isRecord(raw['lods']['marker'])) throw new Error(`invalid orchard save: layouts.${layoutId}.lods.marker`)
    const hues = raw['hues'].map((entry, index): readonly [WireId, string] => {
      if (!Array.isArray(entry) || entry.length !== 2) throw new Error(`invalid orchard save: layouts.${layoutId}.hues[${index}]`)
      return [text(entry[0], `layouts.${layoutId}.hues[${index}][0]`), text(entry[1], `layouts.${layoutId}.hues[${index}][1]`)]
    })
    layouts[layoutId] = {
      label: text(raw['label'], `layouts.${layoutId}.label`),
      bounds: {
        center: vec3(raw['bounds']['center'], `layouts.${layoutId}.bounds.center`),
        radius: positive(raw['bounds']['radius'], `layouts.${layoutId}.bounds.radius`),
      },
      lods: {
        full: scene(raw['lods']['full'], `layouts.${layoutId}.lods.full`),
        reduced: scene(raw['lods']['reduced'], `layouts.${layoutId}.lods.reduced`),
        marker: {
          color: text(raw['lods']['marker']['color'], `layouts.${layoutId}.lods.marker.color`),
          size: positive(raw['lods']['marker']['size'], `layouts.${layoutId}.lods.marker.size`),
        },
      },
      hues,
      palette: {
        branch: text(raw['palette']['branch'], `layouts.${layoutId}.palette.branch`),
        cutBranch: text(raw['palette']['cutBranch'], `layouts.${layoutId}.palette.cutBranch`),
        baseWire: text(raw['palette']['baseWire'], `layouts.${layoutId}.palette.baseWire`),
      },
      widths: {
        branch: positive(raw['widths']['branch'], `layouts.${layoutId}.widths.branch`),
        curve: positive(raw['widths']['curve'], `layouts.${layoutId}.widths.curve`),
      },
      glow: {
        color: text(raw['glow']['color'], `layouts.${layoutId}.glow.color`),
        radius: nonnegative(raw['glow']['radius'], `layouts.${layoutId}.glow.radius`),
        opacity: nonnegative(raw['glow']['opacity'], `layouts.${layoutId}.glow.opacity`),
        bloom: nonnegative(raw['glow']['bloom'], `layouts.${layoutId}.glow.bloom`),
      },
    }
  }
  const ids = new Set<string>()
  const trees = value['trees'].map((raw, index): SavedTree => {
    if (!isRecord(raw)) throw new Error(`invalid orchard save: trees[${index}]`)
    const id = text(raw['id'], `trees[${index}].id`)
    const layout = text(raw['layout'], `trees[${index}].layout`)
    if (ids.has(id)) throw new Error(`invalid orchard save: duplicate tree id '${id}'`)
    if (layouts[layout] === undefined) throw new Error(`invalid orchard save: unknown layout '${layout}'`)
    ids.add(id)
    return {
      id,
      layout,
      x: finite(raw['x'], `trees[${index}].x`),
      z: finite(raw['z'], `trees[${index}].z`),
      yaw: finite(raw['yaw'], `trees[${index}].yaw`),
    }
  })
  return { version: 2, terrain, player, layouts, trees }
}

export async function loadWorldSave(): Promise<OrchardWorldSave> {
  const response = await fetch(new URL('./world.json', import.meta.url))
  if (!response.ok) throw new Error(`orchard save load failed (${response.status})`)
  return parseWorldSave(await response.json())
}
