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

function leanImportClosure(entry: string): Map<string, string> {
  const closure = new Map<string, string>()
  const pending = [entry]
  while (pending.length > 0) {
    const module = pending.pop()
    if (module === undefined || closure.has(module)) continue
    const path = `${module.replaceAll('.', '/')}.lean`
    if (!existsSync(path)) continue
    const source = readFileSync(path, 'utf8')
    closure.set(module, source)
    for (const match of source.matchAll(/^import\s+(VisualProof(?:\.[A-Za-z0-9_]+)+)\s*$/gm)) {
      pending.push(match[1])
    }
  }
  return closure
}

describe('Lean semantics architecture', () => {
  it('freezes one 34-constructor Lean proof-step inventory', () => {
    const source = readFileSync('VisualProof/Rule/Tag.lean', 'utf8')
    const inventory = source.match(
      /inductive StepTag\s+([\s\S]*?)\s+deriving Repr, DecidableEq/,
    )

    expect(inventory).not.toBeNull()
    const constructors = [
      ...(inventory?.[1].matchAll(/^\s*\|\s+([A-Za-z][A-Za-z0-9_]*)\s*$/gm) ??
        []),
    ].map((match) => match[1])

    expect(constructors).toHaveLength(34)
    expect(new Set(constructors).size).toBe(34)
    expect(source).toContain('theorem all_length : all.length = 34 := by')
  })

  it('contains only the signature-indexed semantic core', () => {
    const source = leanSourcesUnder('.')
      .map((file) => readFileSync(file, 'utf8'))
      .join('\n')

    expect(existsSync('VisualProof/Lambda')).toBe(false)
    expect(source).not.toMatch(
      /\b(LambdaModel|betaEta|Item\.equation|comprehension|fission|headStrip|inconsistentCut)\b/i,
    )
    expect(source).not.toMatch(/\b(?:def|theorem|axiom|opaque)\s+fusion\b/i)
    expect(source).not.toContain('openTermSpawn')
    expect(source).not.toContain('congruenceJoin')

    expect(existsSync('VisualProof/Sig.lean')).toBe(true)
    expect(existsSync('VisualProof/Model.lean')).toBe(true)
    expect(existsSync('VisualProof/Data/Finite.lean')).toBe(true)
  })

  it('keeps raw primitive compiler adequacy independent of identity normalization', () => {
    const closure = leanImportClosure(
      'VisualProof.Rule.WirePrimitive.CompilerSoundness',
    )

    expect(closure.size).toBeGreaterThan(0)
    expect(
      [...closure.keys()].filter((module) =>
        module.includes('IdentityNormalization'),
      ),
    ).toEqual([])
    expect([...closure.values()].join('\n')).not.toMatch(
      /\b(?:normalizeIdentities|IdentityNormalization)\b/,
    )
  })
})
