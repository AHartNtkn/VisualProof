/**
 * Settled-theorem render harness (plan 22 visual check). Builds the engine for a
 * bundled theorem diagram, settles it to rest in chunked frames (so the page
 * never hangs), then paints the plan-22 massless-elastica wires. Sets
 * window.__ready when settled so a screenshot driver can wait for rest.
 */
import { theoryToJson } from '../src/kernel/proof/store'
import { buildFregeTheory } from '../src/theories/frege'
import { buildLambdaTheory } from '../src/theories/lambda'
import { emptyLibrary, loadEntry, rebuild } from '../src/app/library'
import { mkReplay } from '../src/app/replay'
import { mkEngine } from '../src/view/engine'
import { settleStep } from '../src/view/relax'
import { paint, LIGHT } from '../src/view/paint'
import { drawShapes } from '../src/view/canvas'

const params = new URLSearchParams(location.search)
const THM = params.get('thm') ?? 'plusComm'
const STEP = Number(params.get('step') ?? '0')
const TICKS = Number(params.get('ticks') ?? '7800')

let lib = emptyLibrary()
lib = loadEntry(lib, 'frege.json', theoryToJson(buildFregeTheory()))
lib = loadEntry(lib, 'lambda.json', theoryToJson(buildLambdaTheory()))
const ctx = rebuild(lib).ctx
const r = mkReplay(ctx.theorems.get(THM)!, ctx)
const e = mkEngine(r.diagramAt(STEP), r.boundary)

const canvas = document.getElementById('c') as HTMLCanvasElement
const ctx2d = canvas.getContext('2d')!
canvas.width = 1400; canvas.height = 900

function draw(): void {
  // fit the drawing to the canvas
  const sheet = e.regions.get(e.d.root)
  const R = sheet ? sheet.radius + 40 : 120
  const s = Math.min(canvas.width, canvas.height) / (2 * R)
  const cx = sheet ? sheet.center.x : 0, cy = sheet ? sheet.center.y : 0
  const view = { scale: s, offsetX: canvas.width / 2 - cx * s, offsetY: canvas.height / 2 - cy * s }
  ctx2d.clearRect(0, 0, canvas.width, canvas.height)
  drawShapes(ctx2d, paint(e, LIGHT), view)
}

let done = 0
const CHUNK = 200
function frame(): void {
  const n = Math.min(CHUNK, TICKS - done)
  for (let i = 0; i < n; i++) settleStep(e)
  done += n
  draw()
  const banner = document.getElementById('banner')!
  banner.textContent = `${THM}@${STEP} — settled ${done}/${TICKS}`
  if (done >= TICKS) { (window as unknown as { __ready: boolean }).__ready = true; return }
  requestAnimationFrame(frame)
}
requestAnimationFrame(frame)
