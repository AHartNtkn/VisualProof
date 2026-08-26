export type SpatialBounds = {
  readonly minX: number
  readonly maxX: number
  readonly minZ: number
  readonly maxZ: number
}

type SpatialItem = { readonly id: string; readonly x: number; readonly z: number }

export function fixedCellCoordinate(value: number, cellSize: number): number {
  return Math.floor(value / cellSize)
}

export class SpatialIndex<T extends SpatialItem> {
  private readonly items = new Map<string, T>()
  private readonly cells = new Map<string, Set<string>>()

  public constructor(private readonly cellSize: number) {
    if (!(cellSize > 0) || !Number.isFinite(cellSize)) {
      throw new Error('spatial index cell size must be finite and positive')
    }
  }

  public insert(item: T): void {
    this.assertPosition(item.x, item.z)
    const existing = this.items.get(item.id)
    if (existing !== undefined) this.unlink(existing)
    this.items.set(item.id, item)
    this.link(item)
  }

  public move(id: string, x: number, z: number): void {
    this.assertPosition(x, z)
    const item = this.items.get(id)
    if (item === undefined) throw new Error(`cannot move unknown spatial item: ${id}`)
    this.unlink(item)
    const moved = { ...item, x, z } as T
    this.items.set(id, moved)
    this.link(moved)
  }

  public remove(id: string): boolean {
    const item = this.items.get(id)
    if (item === undefined) return false
    this.unlink(item)
    this.items.delete(id)
    return true
  }

  public query(bounds: SpatialBounds): T[] {
    if (bounds.minX > bounds.maxX || bounds.minZ > bounds.maxZ) return []

    const candidates = new Set<string>()
    const minCellX = fixedCellCoordinate(bounds.minX, this.cellSize)
    const maxCellX = fixedCellCoordinate(bounds.maxX, this.cellSize)
    const minCellZ = fixedCellCoordinate(bounds.minZ, this.cellSize)
    const maxCellZ = fixedCellCoordinate(bounds.maxZ, this.cellSize)
    for (let cellX = minCellX; cellX <= maxCellX; cellX++) {
      for (let cellZ = minCellZ; cellZ <= maxCellZ; cellZ++) {
        const ids = this.cells.get(this.cellKey(cellX, cellZ))
        if (ids === undefined) continue
        for (const id of ids) candidates.add(id)
      }
    }

    const result: T[] = []
    for (const id of candidates) {
      const item = this.items.get(id)
      if (item !== undefined && item.x >= bounds.minX && item.x <= bounds.maxX && item.z >= bounds.minZ && item.z <= bounds.maxZ) {
        result.push(item)
      }
    }
    return result
  }

  private link(item: T): void {
    const key = this.cellKeyFor(item.x, item.z)
    let ids = this.cells.get(key)
    if (ids === undefined) {
      ids = new Set<string>()
      this.cells.set(key, ids)
    }
    ids.add(item.id)
  }

  private unlink(item: T): void {
    const key = this.cellKeyFor(item.x, item.z)
    const ids = this.cells.get(key)
    if (ids === undefined) return
    ids.delete(item.id)
    if (ids.size === 0) this.cells.delete(key)
  }

  private cellKeyFor(x: number, z: number): string {
    return this.cellKey(fixedCellCoordinate(x, this.cellSize), fixedCellCoordinate(z, this.cellSize))
  }

  private cellKey(cellX: number, cellZ: number): string {
    return `${cellX},${cellZ}`
  }

  private assertPosition(x: number, z: number): void {
    if (!Number.isFinite(x) || !Number.isFinite(z)) {
      throw new Error('spatial item position must be finite')
    }
  }
}
