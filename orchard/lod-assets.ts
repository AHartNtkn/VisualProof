import type { Scene3 } from '../src/view3d/scene'
import type { SavedTreeLods } from './world'

export function deriveTreeLods(full: Scene3): SavedTreeLods {
  return {
    full,
    reduced: { ...full, entities: full.entities.filter((entity) => entity.kind === 'branch') },
    marker: { color: '#e6e1d6', size: 1.2 },
  }
}
