import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { parseInterfaceManifest, validateInterfaceAssets } from './manifest'
import { validateEditorLoupeLayers } from './validate-editor-loupe-layers'

const root = process.cwd()
const manifestPath = resolve(root, 'assets/interface/manifest.json')

try {
  const manifest = parseInterfaceManifest(JSON.parse(readFileSync(manifestPath, 'utf8')))
  const errors = [
    ...validateInterfaceAssets(root, manifest),
    ...validateEditorLoupeLayers(root),
  ]
  for (const error of errors) console.error(error)
  if (errors.length > 0) process.exitCode = 1
} catch (error) {
  const detail = (error instanceof Error ? error.message : String(error)).replace(/\s+/g, ' ')
  console.error(`interface asset validation failed: ${detail}`)
  process.exitCode = 1
}
