import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
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
 * Emit owns only ITS artifacts: it rewrites the shipped files and merges the
 * manifest, but never touches or deletes a file it did not write. A user's own
 * theory dropped alongside (and listed in index.json) survives every re-emit —
 * the pre-serve/pre-build hooks that keep the shipped set fresh cannot clobber
 * it. Output goes to the app's static public dir (served at '/theories/…' in
 * dev and copied into the build for preview/e2e). The manifest lists files in
 * load order; the shipped files always come first, in generation order.
 */
const here = dirname(fileURLToPath(import.meta.url))
const defaultOutDir = join(here, '..', 'app', 'public', 'theories')

const sources: readonly { readonly file: string; readonly build: () => Theory }[] = [
  { file: 'frege.json', build: buildFregeTheory },
  { file: 'lambda.json', build: buildLambdaTheory },
]

/**
 * The manifest to write: the shipped entries first (fixed order, deduped),
 * followed by every foreign entry from an existing manifest in its existing
 * order. A missing or unreadable existing manifest yields the shipped-only
 * list and a loud warning — foreign entries can only be preserved from a
 * manifest we could actually read.
 */
export function mergeManifest(
  shipped: readonly string[],
  existingRaw: string | null,
  warn: (msg: string) => void,
): string[] {
  const shippedSet = new Set(shipped)
  const foreign: string[] = []
  if (existingRaw === null) {
    warn('emit-theories: no existing manifest found; creating a shipped-only index.json (re-add any custom theory entries)')
  } else {
    let parsed: unknown = null
    try {
      parsed = JSON.parse(existingRaw)
    } catch (e) {
      warn(`emit-theories: existing manifest is unparseable (${e instanceof Error ? e.message : String(e)}); rebuilding shipped-only`)
    }
    if (Array.isArray(parsed) && parsed.every((x): x is string => typeof x === 'string')) {
      const seen = new Set<string>()
      for (const entry of parsed) {
        if (shippedSet.has(entry) || seen.has(entry)) continue
        seen.add(entry)
        foreign.push(entry)
      }
    } else if (parsed !== null) {
      warn('emit-theories: existing manifest is not an array of file-name strings; rebuilding shipped-only')
    }
  }
  return [...shipped, ...foreign]
}

/**
 * Build + write the shipped theory files, then write a manifest that merges the
 * existing one (read before overwriting). Only the shipped files and index.json
 * are ever written; nothing is deleted.
 */
export function emitTheories(
  outDir: string,
  warn: (msg: string) => void = (m) => console.error(m),
): { written: string[]; manifest: string[] } {
  mkdirSync(outDir, { recursive: true })
  const shipped: string[] = []
  for (const { file, build } of sources) {
    writeFileSync(join(outDir, file), `${JSON.stringify(theoryToJson(build()), null, 2)}\n`)
    shipped.push(file)
  }
  const indexPath = join(outDir, 'index.json')
  const existingRaw = existsSync(indexPath) ? readFileSync(indexPath, 'utf8') : null
  const manifest = mergeManifest(shipped, existingRaw, warn)
  writeFileSync(indexPath, `${JSON.stringify(manifest, null, 2)}\n`)
  return { written: shipped, manifest }
}

const isMain = process.argv[1] !== undefined && import.meta.url === pathToFileURL(process.argv[1]).href
if (isMain) {
  const { written, manifest } = emitTheories(defaultOutDir)
  console.log(`emitted ${written.length} theories + manifest (${manifest.length} entries) to ${defaultOutDir}`)
}
