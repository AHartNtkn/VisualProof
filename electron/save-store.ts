import { randomUUID } from 'node:crypto'
import {
  mkdir,
  open,
  readFile,
  rename,
  unlink,
  type FileHandle,
} from 'node:fs/promises'
import path from 'node:path'

export const DEFAULT_MAX_SAVE_BYTES = 4 * 1024 * 1024

interface FileOperations {
  mkdir: typeof mkdir
  open: typeof open
  readFile: typeof readFile
  rename: typeof rename
  unlink: typeof unlink
}

export interface SaveStoreOptions {
  directory: string
  maxBytes?: number
  fileOps?: Partial<FileOperations>
  quarantineId?: () => string
}

const defaultFileOperations: FileOperations = { mkdir, open, readFile, rename, unlink }

function assertJsonValue(value: unknown, ancestors: Set<object>): void {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) throw new TypeError('Save contains a non-finite number')
    return
  }
  if (typeof value !== 'object') throw new TypeError('Save must contain only JSON-compatible plain data')
  if (ancestors.has(value)) throw new TypeError('Save contains a cycle')

  const prototype = Object.getPrototypeOf(value)
  if (Array.isArray(value)) {
    if (Reflect.ownKeys(value).some((key) => typeof key === 'symbol')) {
      throw new TypeError('Save arrays cannot contain symbol properties')
    }
    ancestors.add(value)
    try {
      for (let index = 0; index < value.length; index += 1) {
        if (!Object.hasOwn(value, index)) throw new TypeError('Save arrays cannot contain holes')
        assertJsonValue(value[index], ancestors)
      }
      const namedKeys = Object.keys(value).filter((key) => !/^\d+$/.test(key))
      if (namedKeys.length > 0) throw new TypeError('Save arrays cannot contain named properties')
    } finally {
      ancestors.delete(value)
    }
    return
  }

  if (prototype !== Object.prototype && prototype !== null) {
    throw new TypeError('Save objects must be plain objects')
  }
  if (Reflect.ownKeys(value).some((key) => typeof key === 'symbol')) {
    throw new TypeError('Save objects cannot contain symbol properties')
  }
  ancestors.add(value)
  try {
    for (const child of Object.values(value)) assertJsonValue(child, ancestors)
  } finally {
    ancestors.delete(value)
  }
}

export function serializeSaveDocument(document: unknown, maxBytes = DEFAULT_MAX_SAVE_BYTES): string {
  if (!Number.isSafeInteger(maxBytes) || maxBytes <= 0) throw new RangeError('Save size limit must be positive')
  assertJsonValue(document, new Set())
  const encoded = JSON.stringify(document)
  if (encoded === undefined) throw new TypeError('Save must be a JSON document')
  const encodedBytes = Buffer.byteLength(encoded, 'utf8')
  if (encodedBytes > maxBytes) {
    throw new RangeError(`Save size ${encodedBytes} exceeds the ${maxBytes} byte limit`)
  }
  return encoded
}

async function closeFile(file: FileHandle | undefined): Promise<void> {
  if (file !== undefined) await file.close()
}

async function syncDirectory(fileOps: FileOperations, directory: string): Promise<void> {
  let handle: FileHandle | undefined
  try {
    handle = await fileOps.open(directory, 'r')
    await handle.sync()
  } catch (error) {
    const code = (error as NodeJS.ErrnoException).code
    if (!['EINVAL', 'ENOTSUP', 'EISDIR', 'EBADF', 'EPERM'].includes(code ?? '')) throw error
  } finally {
    await closeFile(handle)
  }
}

export class SaveStore {
  readonly savePath: string
  readonly maxBytes: number
  private readonly directory: string
  private readonly fileOps: FileOperations
  private readonly quarantineId: () => string

  constructor(options: SaveStoreOptions) {
    this.directory = path.resolve(options.directory)
    this.savePath = path.join(this.directory, 'save.json')
    this.maxBytes = options.maxBytes ?? DEFAULT_MAX_SAVE_BYTES
    this.fileOps = { ...defaultFileOperations, ...options.fileOps }
    this.quarantineId = options.quarantineId ?? randomUUID
  }

  async loadSave(): Promise<unknown | null> {
    let encoded: string
    try {
      encoded = await this.fileOps.readFile(this.savePath, 'utf8')
    } catch (error) {
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') return null
      throw error
    }
    try {
      return JSON.parse(encoded) as unknown
    } catch (error) {
      if (error instanceof SyntaxError) return encoded
      throw error
    }
  }

  async replaceInvalidSave(document: unknown): Promise<void> {
    serializeSaveDocument(document, this.maxBytes)
    await this.fileOps.mkdir(this.directory, { recursive: true, mode: 0o700 })
    const rejectedPath = path.join(
      this.directory,
      `rejected-save-${this.quarantineId()}.json`,
    )
    let reservation: FileHandle | undefined
    let reservationCreated = false
    let moved = false
    try {
      reservation = await this.fileOps.open(rejectedPath, 'wx', 0o600)
      reservationCreated = true
      await reservation.close()
      reservation = undefined
      await this.fileOps.rename(this.savePath, rejectedPath)
      moved = true
      await syncDirectory(this.fileOps, this.directory)
    } catch (error) {
      await closeFile(reservation)
      if (reservationCreated && !moved) {
        try {
          await this.fileOps.unlink(rejectedPath)
        } catch (cleanupError) {
          if ((cleanupError as NodeJS.ErrnoException).code !== 'ENOENT') throw cleanupError
        }
      }
      if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
        throw new Error('Cannot replace invalid save: no authoritative save exists', { cause: error })
      }
      throw error
    }
    await this.writeSave(document)
  }

  async writeSave(document: unknown): Promise<void> {
    const encoded = serializeSaveDocument(document, this.maxBytes)
    await this.fileOps.mkdir(this.directory, { recursive: true, mode: 0o700 })
    const temporaryPath = path.join(this.directory, `.save-${process.pid}-${randomUUID()}.tmp`)
    let temporaryFile: FileHandle | undefined
    let temporaryCreated = false
    let renamed = false
    let primaryFailure: { error: unknown } | undefined
    try {
      temporaryFile = await this.fileOps.open(temporaryPath, 'wx', 0o600)
      temporaryCreated = true
      await temporaryFile.writeFile(encoded, { encoding: 'utf8' })
      await temporaryFile.sync()
      await temporaryFile.close()
      temporaryFile = undefined
      await this.fileOps.rename(temporaryPath, this.savePath)
      renamed = true
      await syncDirectory(this.fileOps, this.directory)
    } catch (error) {
      primaryFailure = { error }
    } finally {
      try {
        await closeFile(temporaryFile)
      } catch (error) {
        primaryFailure ??= { error }
      }
      if (temporaryCreated && !renamed) {
        try {
          await this.fileOps.unlink(temporaryPath)
        } catch (error) {
          if ((error as NodeJS.ErrnoException).code !== 'ENOENT') primaryFailure ??= { error }
        }
      }
    }
    if (primaryFailure !== undefined) throw primaryFailure.error
  }
}
