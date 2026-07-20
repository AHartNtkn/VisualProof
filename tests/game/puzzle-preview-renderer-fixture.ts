import { diagramToJson } from '../../src/kernel/diagram/json'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import type {
  PuzzlePreviewRequest,
  PuzzlePreviewWorkerRequest,
  PuzzlePreviewWorkerResult,
} from '../../src/game/interface/puzzle-preview-contract'
import { minimalPuzzle } from './catalog-fixture'

const worker = new Worker(
  new URL('../../src/game/interface/puzzle-preview.worker.ts', import.meta.url),
  { type: 'module' },
)
let generation = 0

const render = (diagram: unknown): Promise<PuzzlePreviewWorkerResult> => {
  generation += 1
  const key = `fixture-${generation}`
  const request: PuzzlePreviewRequest = {
    key,
    fingerprint: key,
    diagram,
    width: 640,
    height: 400,
  }
  const message: PuzzlePreviewWorkerRequest = { kind: 'render', generation, request }
  return new Promise((resolve) => {
    const receive = (event: MessageEvent<PuzzlePreviewWorkerResult>): void => {
      if (event.data.generation !== message.generation) return
      worker.removeEventListener('message', receive)
      resolve(event.data)
    }
    worker.addEventListener('message', receive)
    worker.postMessage(message)
  })
}

const inspect = async (blob: Blob) => {
  const bitmap = await createImageBitmap(blob)
  const canvas = document.createElement('canvas')
  canvas.width = bitmap.width
  canvas.height = bitmap.height
  const context = canvas.getContext('2d')!
  context.drawImage(bitmap, 0, 0)
  bitmap.close()
  const pixels = context.getImageData(0, 0, canvas.width, canvas.height).data
  const background = [pixels[0]!, pixels[1]!, pixels[2]!, pixels[3]!] as const
  let minX = canvas.width
  let minY = canvas.height
  let maxX = -1
  let maxY = -1
  for (let y = 0; y < canvas.height; y += 1) {
    for (let x = 0; x < canvas.width; x += 1) {
      const offset = (y * canvas.width + x) * 4
      if (pixels[offset] === background[0]
        && pixels[offset + 1] === background[1]
        && pixels[offset + 2] === background[2]
        && pixels[offset + 3] === background[3]) continue
      minX = Math.min(minX, x)
      minY = Math.min(minY, y)
      maxX = Math.max(maxX, x)
      maxY = Math.max(maxY, y)
    }
  }
  return {
    width: canvas.width,
    height: canvas.height,
    background,
    bounds: { minX, minY, maxX, maxY },
    bytes: [...new Uint8Array(await blob.arrayBuffer())],
  }
}

const fixture = minimalPuzzle()
const largeDiagram = (): unknown => {
  const builder = new DiagramBuilder()
  for (let branch = 0; branch < 12; branch += 1) {
    const outer = builder.cut(builder.root)
    const middle = builder.cut(outer)
    const inner = builder.cut(middle)
    for (let node = 0; node < 4; node += 1) {
      builder.termNode(inner, parseTerm('\\a. a'))
    }
  }
  return diagramToJson(builder.build())
}
const api = {
  ready: true,
  valid: async () => {
    const result = await render(diagramToJson(fixture.goal.diagram))
    if (result.kind !== 'ready') return result
    return { kind: result.kind, inspection: await inspect(result.blob) }
  },
  large: async () => {
    const result = await render(largeDiagram())
    if (result.kind !== 'ready') return result
    return { kind: result.kind, inspection: await inspect(result.blob) }
  },
  deterministic: async () => {
    const diagram = diagramToJson(fixture.goal.diagram)
    const first = await render(diagram)
    const second = await render(diagram)
    if (first.kind !== 'ready' || second.kind !== 'ready') return false
    return await first.blob.arrayBuffer().then((left) =>
      second.blob.arrayBuffer().then((right) => {
        const a = new Uint8Array(left)
        const b = new Uint8Array(right)
        return a.length === b.length && a.every((value, index) => value === b[index])
      }))
  },
  malformed: () => render({ not: 'a diagram' }),
}

declare global { interface Window { __puzzlePreviewRendererFixture: typeof api } }
window.__puzzlePreviewRendererFixture = api
