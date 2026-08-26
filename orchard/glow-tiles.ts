export type GlowContribution = {
  readonly id: string
  readonly x: number
  readonly z: number
  readonly radius: number
  readonly color: string
  readonly opacity: number
}

export type DirtyGlowTile = {
  readonly key: string
  readonly x: number
  readonly z: number
  readonly contributors: readonly GlowContribution[]
}

type Tile = { readonly x: number; readonly z: number }

export class GlowTilePlan {
  private readonly contributions = new Map<string, GlowContribution>()
  private readonly membersByTile = new Map<string, Set<string>>()
  private readonly tiles = new Map<string, Tile>()
  private readonly dirty = new Set<string>()

  public constructor(private readonly tileSize: number) {
    if (!Number.isFinite(tileSize) || tileSize <= 0) throw new Error('glow tile size must be finite and positive')
  }

  public set(contribution: GlowContribution): void {
    this.assertContribution(contribution)
    const previous = this.contributions.get(contribution.id)
    if (previous !== undefined) this.unlink(previous)
    const next = { ...contribution }
    this.contributions.set(next.id, next)
    this.link(next)
  }

  public move(id: string, x: number, z: number): void {
    if (!Number.isFinite(x) || !Number.isFinite(z)) throw new Error('glow contribution position must be finite')
    const previous = this.contributions.get(id)
    if (previous === undefined) throw new Error(`cannot move unknown glow contribution: ${id}`)
    this.set({ ...previous, x, z })
  }

  public remove(id: string): boolean {
    const contribution = this.contributions.get(id)
    if (contribution === undefined) return false
    this.unlink(contribution)
    this.contributions.delete(id)
    return true
  }

  public contributors(key: string): readonly GlowContribution[] {
    const members = this.membersByTile.get(key)
    if (members === undefined) return []
    return [...members]
      .sort()
      .map((id) => this.contributions.get(id))
      .filter((contribution): contribution is GlowContribution => contribution !== undefined)
  }

  public flushDirty(): DirtyGlowTile[] {
    const keys = [...this.dirty].sort()
    const records = keys
      .map((key) => {
        const tile = this.tiles.get(key)!
        return { key, x: tile.x, z: tile.z, contributors: this.contributors(key) }
      })
    this.dirty.clear()
    for (const key of keys) {
      if (!this.membersByTile.has(key)) this.tiles.delete(key)
    }
    return records
  }

  private link(contribution: GlowContribution): void {
    for (const tile of this.intersectedTiles(contribution)) {
      const key = this.key(tile)
      let members = this.membersByTile.get(key)
      if (members === undefined) {
        members = new Set()
        this.membersByTile.set(key, members)
        this.tiles.set(key, tile)
      }
      members.add(contribution.id)
      this.dirty.add(key)
    }
  }

  private unlink(contribution: GlowContribution): void {
    for (const tile of this.intersectedTiles(contribution)) {
      const key = this.key(tile)
      const members = this.membersByTile.get(key)
      if (members !== undefined) {
        members.delete(contribution.id)
        if (members.size === 0) this.membersByTile.delete(key)
      }
      this.dirty.add(key)
    }
  }

  private intersectedTiles(contribution: GlowContribution): Tile[] {
    const minX = Math.floor((contribution.x - contribution.radius) / this.tileSize)
    const maxX = Math.floor((contribution.x + contribution.radius) / this.tileSize)
    const minZ = Math.floor((contribution.z - contribution.radius) / this.tileSize)
    const maxZ = Math.floor((contribution.z + contribution.radius) / this.tileSize)
    const result: Tile[] = []
    for (let x = minX; x <= maxX; x++) {
      for (let z = minZ; z <= maxZ; z++) {
        if (this.intersectsTile(contribution, x, z)) result.push({ x, z })
      }
    }
    return result
  }

  private intersectsTile(contribution: GlowContribution, x: number, z: number): boolean {
    const minX = x * this.tileSize
    const maxX = minX + this.tileSize
    const minZ = z * this.tileSize
    const maxZ = minZ + this.tileSize
    const nearestX = Math.max(minX, Math.min(contribution.x, maxX))
    const nearestZ = Math.max(minZ, Math.min(contribution.z, maxZ))
    return (contribution.x - nearestX) ** 2 + (contribution.z - nearestZ) ** 2 <= contribution.radius ** 2
  }

  private key(tile: Tile): string {
    return `${tile.x}:${tile.z}`
  }

  private assertContribution(contribution: GlowContribution): void {
    if (contribution.id.length === 0) throw new Error('glow contribution id must not be empty')
    if (!Number.isFinite(contribution.x) || !Number.isFinite(contribution.z)) throw new Error('glow contribution position must be finite')
    if (!Number.isFinite(contribution.radius) || contribution.radius < 0) throw new Error('glow contribution radius must be finite and non-negative')
    if (!Number.isFinite(contribution.opacity) || contribution.opacity < 0) throw new Error('glow contribution opacity must be finite and non-negative')
  }
}
