import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  renameSync,
  rmSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { expect, it } from 'vitest'
import { publishGeneratedSaves } from '../../scripts/game-save-publication'

it('restores the entire known output set when a later replacement fails', () => {
  const root = mkdtempSync(join(tmpdir(), 'orchard-save-publication-'))
  const outputDirectory = join(root, 'output')
  const generatedDirectory = join(root, 'generated')
  const filenames = ['large-1.sqlite3', 'stress-50.sqlite3', 'stress-10.sqlite3']
  mkdirSync(outputDirectory)
  mkdirSync(generatedDirectory)

  try {
    writeFileSync(join(outputDirectory, filenames[0]!), 'old-large')
    writeFileSync(join(outputDirectory, filenames[2]!), 'old-stress-10')
    writeFileSync(join(generatedDirectory, filenames[0]!), 'new-large')
    writeFileSync(join(generatedDirectory, filenames[1]!), 'new-stress-50')
    writeFileSync(join(generatedDirectory, filenames[2]!), 'new-stress-10')

    let replacementAttempts = 0
    expect(() => publishGeneratedSaves(
      outputDirectory,
      generatedDirectory,
      filenames,
      (source, destination) => {
        replacementAttempts++
        if (replacementAttempts === 3) rmSync(source)
        renameSync(source, destination)
      },
    )).toThrow(/ENOENT/)

    expect(replacementAttempts).toBe(3)
    expect(readFileSync(join(outputDirectory, filenames[0]!), 'utf8')).toBe('old-large')
    expect(() => readFileSync(join(outputDirectory, filenames[1]!))).toThrow()
    expect(readFileSync(join(outputDirectory, filenames[2]!), 'utf8')).toBe('old-stress-10')
  } finally {
    rmSync(root, { recursive: true, force: true })
  }
})
