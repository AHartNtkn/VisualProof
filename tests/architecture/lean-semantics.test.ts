import { existsSync, readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

const excludedDirectories = new Set(['.lake', 'archive', 'scratchpad'])

function leanSourcesUnder(dir: string): string[] {
  const sources: string[] = []
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (entry.isDirectory() && excludedDirectories.has(entry.name)) continue
    const path = join(dir, entry.name)
    if (entry.isDirectory()) sources.push(...leanSourcesUnder(path))
    else if (entry.isFile() && entry.name.endsWith('.lean')) sources.push(path)
  }
  return sources.sort()
}

describe('Lean semantics architecture', () => {
  it('contains only the signature-indexed semantic core', () => {
    const source = leanSourcesUnder('.')
      .map((file) => readFileSync(file, 'utf8'))
      .join('\n')

    expect(existsSync('VisualProof/Lambda')).toBe(false)
    expect(source).not.toMatch(
      /\b(LambdaModel|betaEta|Item\.equation|comprehension|fusion|fission|headStrip|inconsistentCut)\b/i,
    )
    expect(source).not.toContain('openTermSpawn')
    expect(source).not.toContain('congruenceJoin')

    expect(existsSync('VisualProof/Sig.lean')).toBe(true)
    expect(existsSync('VisualProof/Model.lean')).toBe(true)
    expect(existsSync('VisualProof/Data/Finite.lean')).toBe(true)
  })
})
