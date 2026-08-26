import type { Diagram } from '../../kernel/diagram'
import { relationWireHues, type Theme } from '../../view/paint'
import { scene3 } from '../../view3d/scene'
import { deriveTreeLods } from './lod-assets'
import type { TreeRenderAsset } from './types'

export class TreeRenderAssetCache {
  private readonly assets = new Map<string, TreeRenderAsset>()

  public constructor(private readonly theme: Theme) {}

  public get(diagramJson: string, diagram: Diagram): TreeRenderAsset {
    const existing = this.assets.get(diagramJson)
    if (existing !== undefined) return existing

    const full = scene3(diagram)
    const asset: TreeRenderAsset = {
      bounds: { center: full.center, radius: full.radius },
      lods: deriveTreeLods(full),
      hues: [...relationWireHues(diagram, this.theme.relationHueLightness)],
      palette: {
        branch: this.theme.ink,
        cutBranch: this.theme.frame,
        baseWire: this.theme.wire,
      },
      widths: { branch: 0.10, curve: 0.05 },
      glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
    }
    this.assets.set(diagramJson, asset)
    return asset
  }
}
