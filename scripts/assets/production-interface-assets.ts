import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { inspectPngFile, type DecodedPng } from './canonical-png'

export type ProductionInterfaceAsset = {
  readonly path: string
  readonly width: number
  readonly height: number
  readonly colorType: 'rgb' | 'rgba'
  readonly consumer: string
  readonly token: string
}

export const PRODUCTION_INTERFACE_ASSETS = [
  {
    path: 'assets/interface/generated/desk/natural-indigo-hardwood.png',
    width: 2048, height: 2048, colorType: 'rgb',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'desk/natural-indigo-hardwood.png',
  },
  {
    path: 'assets/interface/generated/central-lens/gasket-frame.png',
    width: 4096, height: 4096, colorType: 'rgba',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'central-lens/gasket-frame.png',
  },
  {
    path: 'assets/interface/generated/central-lens/timeline-housing.png',
    width: 4096, height: 4096, colorType: 'rgba',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'central-lens/timeline-housing.png',
  },
  {
    path: 'assets/interface/generated/central-lens/timeline-handle.png',
    width: 4096, height: 4096, colorType: 'rgba',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'central-lens/timeline-handle.png',
  },
  {
    path: 'assets/interface/generated/substrates/static-review-substrate.png',
    width: 1024, height: 1024, colorType: 'rgb',
    consumer: 'src/game/interface/lens-environment.ts',
    token: 'substrates/static-review-substrate.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/folio-shell.png',
    width: 1100, height: 820, colorType: 'rgba',
    consumer: 'src/game/interface/folio.css',
    token: 'excavation-folio/folio-shell.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/dossier-sheet.png',
    width: 900, height: 720, colorType: 'rgba',
    consumer: 'src/game/interface/folio.css',
    token: 'excavation-folio/dossier-sheet.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/mount-photo.png',
    width: 720, height: 460, colorType: 'rgba',
    consumer: 'src/game/interface/folio.css',
    token: 'excavation-folio/mount-photo.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/clearance-slip.png',
    width: 500, height: 180, colorType: 'rgba',
    consumer: 'src/game/interface/folio.css',
    token: 'excavation-folio/clearance-slip.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/restricted-sleeve.png',
    width: 680, height: 430, colorType: 'rgba',
    consumer: 'src/game/interface/folio.css',
    token: 'excavation-folio/restricted-sleeve.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/auten-reliquary-closure.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/orra-gate-fragment.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/orra-gate-fragment.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/seyr-cairn-seal-iv.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/seyr-cairn-seal-iv.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/seyr-ossuary-seal.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/seyr-ossuary-seal.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/seyric-field-seal-s-27.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/tel-vey-chamber-seal-viii.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/tel-vey-chamber-seal-viii.png',
  },
  {
    path: 'assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png',
    width: 760, height: 470, colorType: 'rgba',
    consumer: 'src/game/interface/folio-view.ts',
    token: 'specimens/uninscribed-votive-of-myrat.png',
  },
  {
    path: 'assets/interface/generated/editor-loupe/rim-socket.png',
    width: 1400, height: 1400, colorType: 'rgba',
    consumer: 'src/game/interface/construction-loupe.ts',
    token: 'editor-loupe/rim-socket.png',
  },
  {
    path: 'assets/interface/generated/editor-loupe/handle-terminal.png',
    width: 1400, height: 1400, colorType: 'rgba',
    consumer: 'src/game/interface/construction-loupe.ts',
    token: 'editor-loupe/handle-terminal.png',
  },
  {
    path: 'assets/interface/generated/editor-loupe/optical-edge.png',
    width: 1400, height: 1400, colorType: 'rgba',
    consumer: 'src/game/interface/construction-loupe.ts',
    token: 'editor-loupe/optical-edge.png',
  },
] as const satisfies readonly ProductionInterfaceAsset[]

const pngSignature = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10])

type PngHeader = {
  readonly width: number
  readonly height: number
  readonly bitDepth: number
  readonly colorType: number
  readonly interlace: number
}

const readPngHeader = (path: string): PngHeader => {
  const data = readFileSync(path)
  if (data.length < 33 || !data.subarray(0, 8).equals(pngSignature)) {
    throw new Error('is not a PNG with a complete IHDR chunk')
  }
  if (data.readUInt32BE(8) !== 13 || data.subarray(12, 16).toString('ascii') !== 'IHDR') {
    throw new Error('must begin with a 13-byte IHDR chunk')
  }
  const compression = data[26]
  const filter = data[27]
  if (compression !== 0 || filter !== 0) throw new Error('has unsupported compression or filter fields')
  return {
    width: data.readUInt32BE(16),
    height: data.readUInt32BE(20),
    bitDepth: data[24]!,
    colorType: data[25]!,
    interlace: data[28]!,
  }
}

const alphaAt = (png: DecodedPng, x: number, y: number): number =>
  png.rgba[(y * png.width + x) * 4 + 3]!

export function validateProductionInterfaceAssets(root: string): string[] {
  const errors: string[] = []
  const decoded = new Map<string, DecodedPng>()
  const consumers = new Map<string, string>()

  for (const asset of PRODUCTION_INTERFACE_ASSETS) {
    const absolute = resolve(root, asset.path)
    let validHeader = false
    try {
      const header = readPngHeader(absolute)
      const expectedColorType = asset.colorType === 'rgb' ? 2 : 6
      if (header.width !== asset.width || header.height !== asset.height) {
        errors.push(`${asset.path} is ${header.width}x${header.height}, expected ${asset.width}x${asset.height}`)
      }
      if (header.bitDepth !== 8) errors.push(`${asset.path} is ${header.bitDepth}-bit, expected 8-bit`)
      if (header.colorType !== expectedColorType) {
        errors.push(`${asset.path} has PNG color type ${header.colorType}, expected ${expectedColorType}`)
      }
      if (header.interlace !== 0) errors.push(`${asset.path} must be non-interlaced`)
      validHeader = header.width === asset.width
        && header.height === asset.height
        && header.bitDepth === 8
        && header.colorType === expectedColorType
        && header.interlace === 0
    } catch (error) {
      errors.push(`${asset.path} ${error instanceof Error ? error.message : String(error)}`)
    }

    if (asset.colorType === 'rgba' && validHeader) {
      try {
        const png = inspectPngFile(absolute)
        if (!png.nonemptyAlpha) errors.push(`${asset.path} has no visible alpha pixels`)
        decoded.set(asset.path, png)
      } catch (error) {
        errors.push(`${asset.path} ${error instanceof Error ? error.message : String(error)}`)
      }
    }

    try {
      let consumer = consumers.get(asset.consumer)
      if (consumer === undefined) {
        consumer = readFileSync(resolve(root, asset.consumer), 'utf8')
        consumers.set(asset.consumer, consumer)
      }
      if (!consumer.includes(asset.token)) {
        errors.push(`${asset.consumer} does not consume ${asset.token}`)
      }
    } catch (error) {
      errors.push(`${asset.consumer} ${error instanceof Error ? error.message : String(error)}`)
    }
  }

  const loupeLayers = [
    'assets/interface/generated/editor-loupe/rim-socket.png',
    'assets/interface/generated/editor-loupe/handle-terminal.png',
    'assets/interface/generated/editor-loupe/optical-edge.png',
  ] as const
  for (const path of loupeLayers) {
    const png = decoded.get(path)
    if (png === undefined) continue
    for (const [x, y] of [[0, 0], [1399, 0], [0, 1399], [1399, 1399], [590, 700]] as const) {
      if (alphaAt(png, x, y) !== 0) errors.push(`${path} must be transparent at (${x}, ${y})`)
    }
  }

  const visibleSamples = [
    ['assets/interface/generated/editor-loupe/rim-socket.png', 650, 180],
    ['assets/interface/generated/editor-loupe/handle-terminal.png', 1200, 1180],
    ['assets/interface/generated/editor-loupe/optical-edge.png', 1080, 650],
  ] as const
  for (const [path, x, y] of visibleSamples) {
    const png = decoded.get(path)
    if (png !== undefined && alphaAt(png, x, y) === 0) {
      errors.push(`${path} must be visible at (${x}, ${y})`)
    }
  }

  return errors
}
