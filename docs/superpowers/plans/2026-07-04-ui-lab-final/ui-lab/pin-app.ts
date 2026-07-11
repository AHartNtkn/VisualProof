/** Actual-app host for the revised movement round. No lab engine, camera,
    renderer, hit testing, or settling loop exists here: mountShell owns all of
    it, exactly as in app/main.ts. */
import { mountShell } from '../src/app'
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'

function scene() {
  const b = new DiagramBuilder()
  const pair = b.ref(b.root, 'pair', 2)
  const left = b.ref(b.root, 'left', 1)
  b.wire(b.root, [
    { node: pair, port: { kind: 'arg', index: 0 } },
    { node: left, port: { kind: 'arg', index: 0 } },
  ])
  const cut = b.cut(b.root)
  const step = b.ref(cut, 'step', 2)
  const value = b.termNode(cut, parseTerm('\\x. x'))
  b.wire(cut, [
    { node: step, port: { kind: 'arg', index: 0 } },
    { node: value, port: { kind: 'output' } },
  ])
  const inner = b.cut(cut)
  b.termNode(inner, parseTerm('\\f. \\x. f (f x)'))
  return b.build()
}

export function mountPinApp(): void {
  const canvas = document.getElementById('c')
  const chrome = document.getElementById('chrome')
  if (!(canvas instanceof HTMLCanvasElement) || !(chrome instanceof HTMLElement)) throw new Error('pin demo host is missing the actual app mount points')
  void mountShell({
    canvas,
    chrome,
    interactionPrototype: { initialDiagram: scene(), cursorCenteredZoom: true },
  })
}
