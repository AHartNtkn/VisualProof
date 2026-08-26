import * as THREE from 'three'
import type { DirtyGlowTile, GlowContribution } from './glow-tiles'

const TILE_SIZE = 128
const TEXTURE_SIZE = 128

export type GlowRenderer = {
  sync(records: readonly DirtyGlowTile[]): void
  dispose(): void
}

type TileResource = {
  readonly canvas: HTMLCanvasElement
  readonly texture: THREE.CanvasTexture
  readonly material: THREE.MeshBasicMaterial
  readonly mesh: THREE.Mesh<THREE.PlaneGeometry, THREE.MeshBasicMaterial>
}

export function mountGlowRenderer(scene: THREE.Scene, groundY: number): GlowRenderer {
  const resources = new Map<string, TileResource>()

  const remove = (key: string): void => {
    const resource = resources.get(key)
    if (resource === undefined) return
    scene.remove(resource.mesh)
    resource.mesh.geometry.dispose()
    resource.material.dispose()
    resource.texture.dispose()
    resources.delete(key)
  }

  const create = (record: DirtyGlowTile): TileResource => {
    const canvas = document.createElement('canvas')
    canvas.width = canvas.height = TEXTURE_SIZE
    const texture = new THREE.CanvasTexture(canvas)
    texture.colorSpace = THREE.SRGBColorSpace
    const material = new THREE.MeshBasicMaterial({
      map: texture,
      transparent: true,
      opacity: 0.014,
      blending: THREE.AdditiveBlending,
      depthWrite: false,
      polygonOffset: true,
      polygonOffsetFactor: -1,
      polygonOffsetUnits: -1,
      toneMapped: false,
    })
    const mesh = new THREE.Mesh(new THREE.PlaneGeometry(TILE_SIZE, TILE_SIZE), material)
    mesh.rotation.x = -Math.PI / 2
    mesh.position.set((record.x + 0.5) * TILE_SIZE, groundY + 0.002, (record.z + 0.5) * TILE_SIZE)
    scene.add(mesh)
    const resource = { canvas, texture, material, mesh }
    resources.set(record.key, resource)
    return resource
  }

  const rasterize = (resource: TileResource, record: DirtyGlowTile): void => {
    const context = resource.canvas.getContext('2d')!
    context.clearRect(0, 0, TEXTURE_SIZE, TEXTURE_SIZE)
    context.globalCompositeOperation = 'lighter'
    for (const contribution of record.contributors) drawGlow(context, contribution, record.x, record.z)
    resource.texture.needsUpdate = true
  }

  return {
    sync(records) {
      for (const record of records) {
        if (record.contributors.length === 0) remove(record.key)
        else rasterize(resources.get(record.key) ?? create(record), record)
      }
    },
    dispose() {
      for (const key of [...resources.keys()]) remove(key)
    },
  }
}

function drawGlow(context: CanvasRenderingContext2D, contribution: GlowContribution, tileX: number, tileZ: number): void {
  const radius = contribution.radius * (TEXTURE_SIZE / TILE_SIZE)
  if (radius === 0) return
  const x = (contribution.x - tileX * TILE_SIZE) * (TEXTURE_SIZE / TILE_SIZE)
  const z = (contribution.z - tileZ * TILE_SIZE) * (TEXTURE_SIZE / TILE_SIZE)
  const color = new THREE.Color(contribution.color)
  const [red, green, blue] = [color.r, color.g, color.b].map((channel) => Math.round(channel * 255))
  const gradient = context.createRadialGradient(x, z, 0, x, z, radius)
  gradient.addColorStop(0, `rgb(${red} ${green} ${blue})`)
  gradient.addColorStop(1, `rgb(${red} ${green} ${blue} / 0%)`)
  context.globalAlpha = Math.min(1, contribution.opacity)
  context.fillStyle = gradient
  context.beginPath()
  context.arc(x, z, radius, 0, Math.PI * 2)
  context.fill()
  context.globalAlpha = 1
}
