import { constants, deflateSync, inflateSync } from 'node:zlib'
import { lstatSync, readFileSync, readdirSync, writeFileSync } from 'node:fs'
import { basename, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

export type DecodedPng = { width: number; height: number; rgba: Buffer; nonemptyAlpha: boolean }

const signature = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10])
const fail = (label: string, message: string): never => { throw new Error(`${label} ${message}`) }
const crcTable = Array.from({ length: 256 }, (_, value) => {
  let crc = value
  for (let bit = 0; bit < 8; bit++) crc = (crc & 1) !== 0 ? 0xedb88320 ^ (crc >>> 1) : crc >>> 1
  return crc >>> 0
})
const crc32 = (value: Buffer): number => {
  let crc = 0xffffffff
  for (const byte of value) crc = crcTable[(crc ^ byte) & 0xff]! ^ (crc >>> 8)
  return (crc ^ 0xffffffff) >>> 0
}

export function decodePngBuffer(data: Buffer, label: string): DecodedPng {
  if (!data.subarray(0, 8).equals(signature)) fail(label, 'is not a PNG')
  let width = 0
  let height = 0
  let offset = 8
  let chunkIndex = 0
  let sawIdat = false
  let endedIdat = false
  let sawIend = false
  const idat: Buffer[] = []
  while (offset < data.length) {
    if (data.length - offset < 12) fail(label, 'has a truncated PNG chunk')
    const length = data.readUInt32BE(offset)
    const end = offset + 12 + length
    if (!Number.isSafeInteger(end) || end > data.length) fail(label, 'has an invalid PNG chunk length')
    const type = data.subarray(offset + 4, offset + 8).toString('ascii')
    const payload = data.subarray(offset + 8, offset + 8 + length)
    const expectedCrc = data.readUInt32BE(offset + 8 + length)
    const actualCrc = crc32(data.subarray(offset + 4, offset + 8 + length))
    if (actualCrc !== expectedCrc) fail(label, `${type} chunk CRC mismatch`)
    if (chunkIndex === 0) {
      if (type !== 'IHDR' || length !== 13) fail(label, 'must begin with a 13-byte IHDR chunk')
      width = payload.readUInt32BE(0)
      height = payload.readUInt32BE(4)
      if (width === 0 || height === 0) fail(label, 'has invalid zero dimensions')
      const [bitDepth, colorType, compression, filter, interlace] = payload.subarray(8)
      if (bitDepth !== 8 || colorType !== 6) fail(label, 'must be 8-bit RGBA')
      if (compression !== 0 || filter !== 0 || interlace !== 0) fail(label, 'has unsupported PNG compression, filter, or interlace fields')
    } else if (type === 'IHDR') {
      fail(label, 'has more than one IHDR chunk')
    }
    if (type === 'IDAT') {
      if (endedIdat) fail(label, 'has non-contiguous IDAT chunks')
      sawIdat = true
      idat.push(payload)
    } else if (sawIdat) {
      endedIdat = true
    }
    offset = end
    chunkIndex++
    if (type === 'IEND') {
      if (length !== 0) fail(label, 'IEND chunk must be empty')
      if (!sawIdat) fail(label, 'has no IDAT data')
      if (offset !== data.length) fail(label, 'has trailing bytes after IEND')
      sawIend = true
      break
    }
  }
  if (!sawIend) fail(label, 'has no IEND chunk')
  const raw = inflateSync(Buffer.concat(idat))
  const stride = width * 4
  const expectedBytes = height * (stride + 1)
  if (raw.length !== expectedBytes) fail(label, `decompressed byte count is ${raw.length}, expected ${expectedBytes}`)
  const prior = Buffer.alloc(stride)
  const current = Buffer.alloc(stride)
  const rgba = Buffer.alloc(stride * height)
  let cursor = 0
  let nonemptyAlpha = false
  const paeth = (a: number, b: number, c: number): number => {
    const p = a + b - c
    const pa = Math.abs(p - a), pb = Math.abs(p - b), pc = Math.abs(p - c)
    return pa <= pb && pa <= pc ? a : pb <= pc ? b : c
  }
  for (let y = 0; y < height; y++) {
    const filter = raw[cursor++]!
    for (let x = 0; x < stride; x++) {
      const encoded = raw[cursor++]!
      const left = x >= 4 ? current[x - 4]! : 0
      const up = prior[x]!
      const upperLeft = x >= 4 ? prior[x - 4]! : 0
      const predictor = filter === 0 ? 0 : filter === 1 ? left : filter === 2 ? up
        : filter === 3 ? Math.floor((left + up) / 2) : filter === 4 ? paeth(left, up, upperLeft)
        : fail(label, `uses unsupported PNG filter ${filter}`)
      current[x] = (encoded + predictor) & 255
    }
    for (let x = 3; x < stride; x += 4) if (current[x]! > 0) nonemptyAlpha = true
    current.copy(rgba, y * stride)
    current.copy(prior)
  }
  return { width, height, rgba, nonemptyAlpha }
}

export const inspectPngFile = (path: string): DecodedPng => decodePngBuffer(readFileSync(path), basename(path))

const chunk = (type: string, payload: Buffer): Buffer => {
  const name = Buffer.from(type, 'ascii')
  const result = Buffer.alloc(payload.length + 12)
  result.writeUInt32BE(payload.length, 0)
  name.copy(result, 4)
  payload.copy(result, 8)
  result.writeUInt32BE(crc32(Buffer.concat([name, payload])), payload.length + 8)
  return result
}

export function encodeCanonicalPng(decoded: DecodedPng): Buffer {
  const ihdr = Buffer.alloc(13)
  ihdr.writeUInt32BE(decoded.width, 0)
  ihdr.writeUInt32BE(decoded.height, 4)
  ihdr.set([8, 6, 0, 0, 0], 8)
  const stride = decoded.width * 4
  const raw = Buffer.alloc(decoded.height * (stride + 1))
  for (let y = 0; y < decoded.height; y++) decoded.rgba.copy(raw, y * (stride + 1) + 1, y * stride, (y + 1) * stride)
  const compressed = deflateSync(raw, { level: 9, strategy: constants.Z_DEFAULT_STRATEGY })
  return Buffer.concat([signature, chunk('IHDR', ihdr), chunk('IDAT', compressed), chunk('IEND', Buffer.alloc(0))])
}

export const canonicalizePngBuffer = (data: Buffer, label: string): Buffer => encodeCanonicalPng(decodePngBuffer(data, label))
export const canonicalizePngFile = (path: string): void => writeFileSync(path, canonicalizePngBuffer(readFileSync(path), basename(path)))

const main = (): void => {
  const args = process.argv.slice(2)
  if (args.length === 0) throw new Error('usage: canonical-png.ts <PNG file or directory> [...]')
  for (const candidate of args) {
    const absolute = resolve(candidate)
    const status = lstatSync(absolute)
    const files = status.isDirectory()
      ? readdirSync(absolute).filter((name) => name.endsWith('.png')).sort().map((name) => join(absolute, name))
      : [absolute]
    for (const file of files) canonicalizePngFile(file)
  }
}

if (process.argv[1] !== undefined && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    main()
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error))
    process.exitCode = 1
  }
}
