import type { Scene3 } from '../../view3d/scene'
import type { TreeLodAssets } from './types'

export function deriveTreeLods(full: Scene3): TreeLodAssets {
  return {
    full,
    reduced: { ...full, entities: full.entities.filter((entity) => entity.kind === 'branch') },
    marker: { color: '#e6e1d6', size: 1.2 },
  }
}
