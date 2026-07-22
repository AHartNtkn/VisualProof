import type { GameContentFiles } from '../content-loader'

const contentPrefix = '../../../content/'
const discovered = import.meta.glob<unknown>([
  '../../../content/manifest.json',
  '../../../content/puzzles/**/*.json',
  '../../../content/definitions/**/*.json',
  '../../../content/progression/**/*.json',
  '../../../content/catalog/**/*.json',
  '../../../content/guidance/**/*.json',
], { eager: true, import: 'default' })

const entries = Object.entries(discovered).map(([path, value]) => {
  if (!path.startsWith(contentPrefix)) throw new Error(`unexpected content module path '${path}'`)
  return [path.slice(contentPrefix.length), value] as const
})

export const gameContentFiles: GameContentFiles = Object.freeze(Object.fromEntries(entries))
