import { fitPose } from '../../src/view3d/camera'
import { mountRender } from '../../src/view3d/render'

type RenderResult = {
  readonly theme: 'light' | 'dark'
  readonly lambda: readonly [number, number, number]
  readonly pip: readonly [number, number, number]
}

declare global {
  interface Window {
    __view3RenderResults?: readonly RenderResult[]
  }
}

const center = { x: 0, y: 0, z: 0 }
const plane = {
  right: { x: 1, y: 0, z: 0 },
  up: { x: 0, y: 1, z: 0 },
  normal: { x: 0, y: 0, z: 1 },
}
const term = { kind: 'free' as const, slot: 0 }
const lambda = (key: string, color: string) => ({
  kind: 'lambda' as const,
  key,
  node: 'lambda-node',
  region: 'lambda-region',
  term,
  interfaceArity: 1,
  center,
  plane,
  scale: 1,
  subtermPath: [],
  strokeId: key,
  role: 'lambda' as const,
  color,
  pts: [{ x: -0.8, y: 0, z: 0 }, { x: 0.8, y: 0, z: 0 }],
})
const pip = {
  kind: 'pip' as const,
  key: 'pip',
  node: 'pip-node',
  ownerWire: 'wire',
  pos: center,
}

function readCenter(canvas: HTMLCanvasElement): [number, number, number] {
  const copy = document.createElement('canvas')
  copy.width = canvas.width
  copy.height = canvas.height
  const context = copy.getContext('2d')!
  context.drawImage(canvas, 0, 0)
  const pixel = context.getImageData(Math.floor(copy.width / 2), Math.floor(copy.height / 2), 1, 1).data
  return [pixel[0]!, pixel[1]!, pixel[2]!]
}

const results: RenderResult[] = []
for (const mode of ['light', 'dark'] as const) {
  const host = document.createElement('div')
  host.style.cssText = 'position:fixed;left:0;top:0;width:256px;height:256px'
  document.body.appendChild(host)
  const renderer = mountRender(host, {
    mode,
    background: mode === 'dark' ? '#000000' : '#ffffff',
    line: '#555555',
    lineAlt: '#777777',
    baseWire: '#888888',
    hover: '#ffffff',
    hues: new Map([['wire', '#00ff00']]),
  })
  renderer.resize(256, 256)
  renderer.setPose(fitPose(center, 1, 1))
  renderer.setEntities([lambda('first', '#ff0000'), lambda('second', '#0000ff')])
  renderer.render()
  const canvas = host.querySelector('canvas')!
  const lambdaPixel = readCenter(canvas)
  renderer.setEntities([lambda('first', '#ff0000'), lambda('second', '#0000ff'), pip])
  renderer.render()
  results.push({ theme: mode, lambda: lambdaPixel, pip: readCenter(canvas) })
  renderer.dispose()
  host.remove()
}
window.__view3RenderResults = results
