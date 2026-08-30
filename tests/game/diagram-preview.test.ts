import { describe, expect, it } from 'vitest'
import { renderDiagramPreview } from '../../game/diagram-preview'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'

type Operation = readonly [string, ...unknown[]]

function recordingCanvas(): { readonly canvas: HTMLCanvasElement; readonly operations: Operation[] } {
  const operations: Operation[] = []
  const context = new Proxy({} as CanvasRenderingContext2D, {
    get(_target, property) {
      if (property === 'canvas') return canvas
      if (typeof property === 'symbol') return undefined
      return (...args: unknown[]) => { operations.push([property, ...args]) }
    },
    set(_target, property, value) {
      operations.push([`set:${String(property)}`, value])
      return true
    },
  })
  const canvas = {
    width: 240,
    height: 150,
    getContext: (kind: string) => kind === '2d' ? context : null,
  } as unknown as HTMLCanvasElement
  return { canvas, operations }
}

function blankSnapshot() {
  return snapshotFromDiagram(new DiagramBuilder().build())
}

function nestedSnapshot() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  builder.cut(cut)
  return snapshotFromDiagram(builder.build())
}

describe('diagram preview', () => {
  it('projects distinct blank and nonblank scenes into distinct canvas operations', () => {
    // Catches preview rendering a canned icon instead of the supplied snapshot.
    const blank = recordingCanvas()
    const nested = recordingCanvas()

    renderDiagramPreview(blank.canvas, blankSnapshot())
    renderDiagramPreview(nested.canvas, nestedSnapshot())

    expect(blank.operations.some(([operation]) => operation === 'clearRect')).toBe(true)
    expect(nested.operations).not.toEqual(blank.operations)
    expect(nested.operations.filter(([operation]) => operation === 'lineTo').length)
      .toBeGreaterThan(blank.operations.filter(([operation]) => operation === 'lineTo').length)
  })
})
