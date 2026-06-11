import { parseTerm } from '../src/kernel/term/parse'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { buildScene, initialState, step, renderScene, drawShapes, DEFAULT_PARAMS } from '../src/view/index'

const consts = new Set<string>()
const p = (s: string) => parseTerm(s, consts)

const h = new DiagramBuilder()
const a = h.termNode(h.root, p('y'))
const b = h.termNode(h.root, p('\\x. x'))
h.wire(h.root, [
  { node: a, port: { kind: 'freeVar', name: 'y' } },
  { node: b, port: { kind: 'output' } },
])
const cut = h.cut(h.root)
const c = h.termNode(cut, p('\\f. \\x. f (f x)'))
const bub = h.bubble(cut, 1)
const atom = h.atom(bub, bub)
h.wire(cut, [
  { node: atom, port: { kind: 'arg', index: 0 } },
  { node: c, port: { kind: 'output' } },
])
const d = h.build()

const canvas = document.getElementById('c') as HTMLCanvasElement
const ctx = canvas.getContext('2d')!
let state = initialState(d)

function frame(): void {
  canvas.width = window.innerWidth
  canvas.height = window.innerHeight
  for (let i = 0; i < 4; i++) state = step(d, state, DEFAULT_PARAMS)
  const scene = buildScene(d, state.positions)
  ctx.clearRect(0, 0, canvas.width, canvas.height)
  drawShapes(ctx, renderScene(scene), {
    scale: 6,
    offsetX: canvas.width / 2,
    offsetY: canvas.height / 2,
  })
  requestAnimationFrame(frame)
}
frame()
