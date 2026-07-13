import { deflateSync } from 'node:zlib'
import { describe, expect, it } from 'vitest'
import { canonicalizePngBuffer } from '../../scripts/assets/canonical-png'

const signature = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10])
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
const chunk = (type: string, data: Buffer): Buffer => {
  const name = Buffer.from(type, 'ascii')
  const result = Buffer.alloc(data.length + 12)
  result.writeUInt32BE(data.length, 0)
  name.copy(result, 4)
  data.copy(result, 8)
  result.writeUInt32BE(crc32(Buffer.concat([name, data])), data.length + 8)
  return result
}
const encoded = (pixels: Buffer, level: number, split = false): Buffer => {
  const ihdr = Buffer.alloc(13)
  ihdr.writeUInt32BE(2, 0)
  ihdr.writeUInt32BE(1, 4)
  ihdr.set([8, 6, 0, 0, 0], 8)
  const raw = Buffer.concat([Buffer.from([0]), pixels])
  const compressed = deflateSync(raw, { level })
  const idat = split
    ? [chunk('IDAT', compressed.subarray(0, 2)), chunk('IDAT', compressed.subarray(2))]
    : [chunk('IDAT', compressed)]
  return Buffer.concat([signature, chunk('IHDR', ihdr), ...idat, chunk('IEND', Buffer.alloc(0))])
}

describe('canonical PNG encoding', () => {
  it('makes byte-different encodings of identical RGBA pixels identical', () => {
    const pixels = Buffer.from([21, 34, 55, 255, 89, 144, 233, 128])
    const first = encoded(pixels, 1, true)
    const second = encoded(pixels, 9)
    expect(first).not.toEqual(second)
    expect(canonicalizePngBuffer(first, 'first.png')).toEqual(canonicalizePngBuffer(second, 'second.png'))
  })

  it('does not collapse a pixel difference', () => {
    const first = encoded(Buffer.from([21, 34, 55, 255, 89, 144, 233, 128]), 1)
    const second = encoded(Buffer.from([22, 34, 55, 255, 89, 144, 233, 128]), 1)
    expect(canonicalizePngBuffer(first, 'first.png')).not.toEqual(canonicalizePngBuffer(second, 'second.png'))
  })
})
