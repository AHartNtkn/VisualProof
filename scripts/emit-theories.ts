import { mkdirSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import type { Theory } from '../src/kernel/proof/store'
import { theoryToJson } from '../src/kernel/proof/store'
import { buildFregeTheory } from '../src/theories/frege'
import { buildLambdaTheory } from '../src/theories/lambda'

/**
 * Emit the shipped theories as data. Each generator is the tested source of
 * truth; theoryToJson serializes it with stable key order. The app loads these
 * files at boot through loadTheory — the same verifying road as the shell's
 * "Load theory" button — so a user can replace or extend them without a rebuild.
 *
 * Output goes to the app's static public dir (served at '/theories/…' in dev and
 * copied into the build for preview/e2e). The manifest lists the files in load
 * order, which is the theory-merge order.
 */
const here = dirname(fileURLToPath(import.meta.url))
const outDir = join(here, '..', 'app', 'public', 'theories')

const sources: readonly { readonly file: string; readonly build: () => Theory }[] = [
  { file: 'frege.json', build: buildFregeTheory },
  { file: 'lambda.json', build: buildLambdaTheory },
]

mkdirSync(outDir, { recursive: true })
const manifest: string[] = []
for (const { file, build } of sources) {
  const json = theoryToJson(build())
  writeFileSync(join(outDir, file), `${JSON.stringify(json, null, 2)}\n`)
  manifest.push(file)
}
writeFileSync(join(outDir, 'index.json'), `${JSON.stringify(manifest, null, 2)}\n`)
console.log(`emitted ${manifest.length} theories + manifest to ${outDir}`)
