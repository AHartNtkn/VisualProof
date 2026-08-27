import { spawnSync } from 'node:child_process'
import {
  mkdirSync,
  mkdtempSync,
  renameSync,
  rmSync,
} from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'
import { mkReplay } from '../src/app/replay'
import { diagramToJson } from '../src/kernel/diagram/json'
import { verifyTheory } from '../src/kernel/proof/context'
import { buildFregeTheory } from '../src/theories/frege'
import { orchardPlacements } from '../src/game/render/placement'

const counts = [1, 10, 50, 100, 250, 500, 1000, 2000] as const
const largeDiagram = mkReplay('zeroIsNat', verifyTheory(buildFregeTheory())).diagramAt(20)
const diagramJson = JSON.stringify(diagramToJson(largeDiagram))
const saves = counts.map((count) => {
  const slotId = count === 1 ? 'large-1' : `stress-${count}`
  return {
    slotId,
    filename: `${slotId}.sqlite3`,
    displayName: count === 1 ? 'Large Tree' : `Renderer Stress ${count}`,
    updatedAtMs: 0,
    camera: { x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 },
    trees: orchardPlacements(count, 34).map((placement) => ({ ...placement, diagramJson })),
  }
})

const repositoryRoot = dirname(dirname(fileURLToPath(import.meta.url)))
const outputDirectory = join(repositoryRoot, 'game', 'generated-saves')
const manifestPath = join(repositoryRoot, 'src-tauri', 'Cargo.toml')
mkdirSync(outputDirectory, { recursive: true })
const temporaryDirectory = mkdtempSync(join(outputDirectory, '.emit-'))

try {
  const emitted = spawnSync(
    'cargo',
    ['run', '--quiet', '--manifest-path', manifestPath, '--bin', 'emit_game_saves'],
    {
      input: JSON.stringify({ outputDirectory: temporaryDirectory, saves }),
      encoding: 'utf8',
    },
  )
  if (emitted.error !== undefined) throw emitted.error
  if (emitted.status !== 0) {
    throw new Error(`save emitter failed with status ${String(emitted.status)}:\n${emitted.stderr}`)
  }

  for (const { filename } of saves) {
    renameSync(join(temporaryDirectory, filename), join(outputDirectory, filename))
  }
  console.log(`emitted ${saves.length} ordinary saves`)
} finally {
  rmSync(temporaryDirectory, { recursive: true, force: true })
}
