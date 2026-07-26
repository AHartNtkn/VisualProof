import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { IOTA, relSig } from '../src/kernel/diagram/sig'
import { mkEngine, settleStep, paint, LIGHT } from '../src/view/index'
import { drawShapes } from '../src/view/canvas'

const unary = relSig([IOTA])
const builder = new DiagramBuilder()
const cut = builder.cut(builder.root)
const ref = builder.ref(cut, 'Unary', unary)
const atom = builder.atom(cut, unary)
const identity = builder.identity(cut, IOTA, 2)
builder.wire(builder.root, [
  { node: ref, port: { kind: 'arg', index: 0 } },
  { node: identity, port: { kind: 'identity', index: 0 } },
])
builder.wire(builder.root, [
  { node: atom, port: { kind: 'arg', index: 0 } },
  { node: identity, port: { kind: 'identity', index: 1 } },
])

const canvas = document.getElementById('c') as HTMLCanvasElement
canvas.style.background = LIGHT.canvas
const ctx = canvas.getContext('2d')!
const engine = mkEngine(builder.build(), [])
settleStep(engine)

function frame(): void {
  canvas.width = window.innerWidth
  canvas.height = window.innerHeight
  for (let index = 0; index < 4; index++) settleStep(engine)
  ctx.clearRect(0, 0, canvas.width, canvas.height)
  drawShapes(ctx, paint(engine, LIGHT), {
    scale: 6,
    offsetX: canvas.width / 2,
    offsetY: canvas.height / 2,
  })
  requestAnimationFrame(frame)
}

frame()
