import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import {
  PRODUCTION_INTERFACE_ASSETS,
  validateProductionInterfaceAssets,
} from '../../scripts/assets/production-interface-assets'

const expectedRuntimeAssets = [
  'assets/interface/generated/desk/natural-indigo-hardwood.png',
  'assets/interface/generated/central-lens/gasket-frame.png',
  'assets/interface/generated/central-lens/timeline-housing.png',
  'assets/interface/generated/central-lens/timeline-handle.png',
  'assets/interface/generated/substrates/static-review-substrate.png',
  'assets/interface/generated/excavation-folio/folio-shell.png',
  'assets/interface/generated/excavation-folio/dossier-sheet.png',
  'assets/interface/generated/excavation-folio/mount-photo.png',
  'assets/interface/generated/excavation-folio/clearance-slip.png',
  'assets/interface/generated/excavation-folio/restricted-sleeve.png',
  'assets/interface/generated/excavation-folio/specimens/auten-reliquary-closure.png',
  'assets/interface/generated/excavation-folio/specimens/orra-gate-fragment.png',
  'assets/interface/generated/excavation-folio/specimens/seyr-cairn-seal-iv.png',
  'assets/interface/generated/excavation-folio/specimens/seyr-ossuary-seal.png',
  'assets/interface/generated/excavation-folio/specimens/seyric-field-seal-s-27.png',
  'assets/interface/generated/excavation-folio/specimens/tel-vey-chamber-seal-viii.png',
  'assets/interface/generated/excavation-folio/specimens/uninscribed-votive-of-myrat.png',
  'assets/interface/generated/editor-loupe/rim-socket.png',
  'assets/interface/generated/editor-loupe/handle-terminal.png',
  'assets/interface/generated/editor-loupe/optical-edge.png',
] as const

describe('production interface asset authority', () => {
  it('semantically validates only assets consumed by the game', () => {
    expect(validateProductionInterfaceAssets(process.cwd())).toEqual([])
    const paths = PRODUCTION_INTERFACE_ASSETS.map(({ path }) => path)
    expect(paths).toEqual(expectedRuntimeAssets)
    expect(paths).not.toContainEqual(expect.stringMatching(/^review\//))
    expect(paths).not.toContainEqual(expect.stringMatching(/\.blend$/))
    expect(paths).not.toContainEqual(expect.stringMatching(
      /central-lens\/(?:frame|glass|shadow|lever-housing|lever-handle)\.png$/,
    ))
  })

  it('rejects an RGB asset truncated after its PNG header', () => {
    const root = mkdtempSync(join(tmpdir(), 'cursebreaker-production-assets-'))
    const truncatedPath = 'assets/interface/generated/desk/natural-indigo-hardwood.png'
    try {
      const consumers = new Set<string>()
      for (const asset of PRODUCTION_INTERFACE_ASSETS) {
        const destination = resolve(root, asset.path)
        mkdirSync(dirname(destination), { recursive: true })
        if (asset.path === truncatedPath) {
          writeFileSync(destination, readFileSync(resolve(asset.path)).subarray(0, 33))
        } else {
          symlinkSync(resolve(asset.path), destination)
        }
        consumers.add(asset.consumer)
      }
      for (const consumer of consumers) {
        const destination = resolve(root, consumer)
        mkdirSync(dirname(destination), { recursive: true })
        symlinkSync(resolve(consumer), destination)
      }

      expect(validateProductionInterfaceAssets(root)).toContainEqual(
        expect.stringMatching(/^assets\/interface\/generated\/desk\/natural-indigo-hardwood\.png .+/),
      )
    } finally {
      rmSync(root, { recursive: true, force: true })
    }
  })
})
