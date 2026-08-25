import { writeFileSync } from 'node:fs'
import { buildFregeTheory } from '../src/theories/frege'
import { verifyTheory } from '../src/kernel/proof/context'
import { mkReplay } from '../src/app/replay'
import { scene3 } from '../src/view3d/scene'
import { DARK, relationWireHues } from '../src/view/paint'
import { orchardPlacements } from '../orchard/placement'
import type { OrchardWorldSave } from '../orchard/world'

const LAYOUT_ID = 'zero-is-nat-20'
const diagram = mkReplay('zeroIsNat', verifyTheory(buildFregeTheory())).diagramAt(20)
const placements = orchardPlacements(2000, 34)
const save: OrchardWorldSave = {
  version: 1,
  terrain: {
    size: 4000,
    ground: '#181a1d',
    sky: '#000000',
    fogNear: 170,
    fogFar: 780,
    bounds: { minX: -2000, maxX: 2000, minZ: -2000, maxZ: 2000 },
  },
  player: { x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 },
  layouts: {
    [LAYOUT_ID]: {
      label: 'zeroIsNat · step 20',
      scene: scene3(diagram),
      hues: [...relationWireHues(diagram, DARK.relationHueLightness)],
      palette: { branch: DARK.ink, cutBranch: DARK.frame, baseWire: DARK.wire },
      glow: { color: '#ffffff', intensity: 1800, distance: 32, decay: 2, height: 13 },
    },
  },
  trees: placements.map(({ id, x, z, yaw }) => ({ id, layout: LAYOUT_ID, x, z, yaw })),
}

const target = new URL('../orchard/world.json', import.meta.url)
writeFileSync(target, `${JSON.stringify(save)}\n`)
console.log(`wrote ${save.trees.length} trees to ${target.pathname}`)
