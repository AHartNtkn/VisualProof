import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { parseInterfaceManifest, validateInterfaceAssets } from './manifest'

const root = process.cwd()
const manifestPath = resolve(root, 'assets/interface/manifest.json')
const manifest = parseInterfaceManifest(JSON.parse(readFileSync(manifestPath, 'utf8')))
const errors = validateInterfaceAssets(root, manifest)

for (const error of errors) console.error(error)
if (errors.length > 0) process.exit(1)
