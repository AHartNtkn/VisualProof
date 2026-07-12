import { describe, expect, it } from 'vitest'
import { adaptCanvas } from '../../src/view/canvas'
import type { Shape } from '../../src/view/paint'

describe('CanvasAdapter layered frames', () => {
  it('owns background fill, ordered layers, and isolated alpha', () => {
    const calls: string[] = []
    let fillStyle = ''
    let globalAlpha = 1
    const savedAlpha: number[] = []
    const context = {
      clearRect: () => calls.push('clear'),
      fillRect: () => calls.push(`fillRect:${fillStyle}`),
      beginPath: () => calls.push('beginPath'),
      arc: () => calls.push('arc'),
      fill: () => calls.push(`fill:${fillStyle}:alpha=${globalAlpha}`),
      save: () => { calls.push('save'); savedAlpha.push(globalAlpha) },
      restore: () => { calls.push('restore'); globalAlpha = savedAlpha.pop() ?? 1 },
      set fillStyle(value: string) { fillStyle = value; calls.push(`fillStyle:${value}`) },
      get fillStyle() { return fillStyle },
      set globalAlpha(value: number) { globalAlpha = value; calls.push(`alpha:${value}`) },
      get globalAlpha() { return globalAlpha },
      lineJoin: 'round', lineCap: 'round', shadowBlur: 0,
    }
    const canvas = {
      width: 320, height: 180, clientWidth: 320, clientHeight: 180,
      getContext: () => context,
    } as unknown as HTMLCanvasElement
    const dot = (fill: string): Shape => ({ kind: 'dot', center: { x: 0, y: 0 }, rPx: 1, fill })
    const surface = adaptCanvas(canvas)

    surface.render({
      background: '#paper',
      layers: [
        { shapes: [dot('#base')] },
        { shapes: [dot('#hover')], alpha: 0.25 },
        { shapes: [dot('#overlay')] },
      ],
    }, { scale: 1, offsetX: 0, offsetY: 0 })

    expect(calls).toEqual([
      'clear', 'fillStyle:#paper', 'fillRect:#paper',
      'beginPath', 'arc', 'fillStyle:#base', 'fill:#base:alpha=1',
      'save', 'alpha:0.25', 'beginPath', 'arc', 'fillStyle:#hover', 'fill:#hover:alpha=0.25', 'restore',
      'beginPath', 'arc', 'fillStyle:#overlay', 'fill:#overlay:alpha=1',
    ])
  })
})
