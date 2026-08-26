import {
  existsSync,
  readFileSync,
  renameSync,
  rmSync,
  writeFileSync,
} from 'node:fs'
import { basename, join } from 'node:path'

type ReplaceFile = (source: string, destination: string) => void

type Publication = {
  readonly generated: string
  readonly destination: string
  readonly previousBytes: Buffer | null
}

export function publishGeneratedSaves(
  outputDirectory: string,
  generatedDirectory: string,
  filenames: readonly string[],
  replaceFile: ReplaceFile = renameSync,
): number {
  const names = new Set<string>()
  const changes: Publication[] = []
  for (const filename of filenames) {
    if (basename(filename) !== filename || names.has(filename)) {
      throw new Error(`generated save filename must be a unique plain filename: '${filename}'`)
    }
    names.add(filename)
    const generated = join(generatedDirectory, filename)
    const destination = join(outputDirectory, filename)
    if (!existsSync(generated)) throw new Error(`save emitter did not produce ${filename}`)
    const generatedBytes = readFileSync(generated)
    const previousBytes = existsSync(destination) ? readFileSync(destination) : null
    if (previousBytes === null || !previousBytes.equals(generatedBytes)) {
      changes.push({ generated, destination, previousBytes })
    }
  }

  const attempted: Publication[] = []
  try {
    for (const change of changes) {
      attempted.push(change)
      replaceFile(change.generated, change.destination)
    }
  } catch (publicationError) {
    const rollbackErrors: unknown[] = []
    for (const change of attempted.reverse()) {
      try {
        if (change.previousBytes === null) {
          rmSync(change.destination, { force: true })
        } else {
          writeFileSync(change.destination, change.previousBytes)
        }
      } catch (rollbackError) {
        rollbackErrors.push(rollbackError)
      }
    }
    if (rollbackErrors.length > 0) {
      throw new AggregateError(
        rollbackErrors,
        `generated save publication failed and rollback was incomplete: ${String(publicationError)}`,
      )
    }
    throw publicationError
  }

  return changes.length
}
