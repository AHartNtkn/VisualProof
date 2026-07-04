import { it } from 'vitest'
import { writeFileSync } from 'node:fs'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep } from '../../src/view/relax'

it('DUMP tow scenario', () => {
  const b = new DiagramBuilder()
  const n = b.ref(b.root, 'nat', 1)
  const wid = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
  void wid
  const e = mkEngine(b.build(), [])
  settle(e, 2600)
  const body = e.bodies.get(n)!
  body.pos = { x: body.pos.x + 40, y: body.pos.y }
  const frames: string[] = []
  for (let f = 0; f < 4; f++) {
    if (f > 0) for (let i = 0; i < 800; i++) settleStep(e)
    const parts: string[] = []
    for (const bb of e.bodies.values()) {
      const col = bb.kind === 'junction' ? 'red' : 'steelblue'
      parts.push(`<circle cx="${bb.pos.x.toFixed(2)}" cy="${bb.pos.y.toFixed(2)}" r="${bb.kind === 'junction' ? 1 : bb.discR}" fill="none" stroke="${col}"/><text x="${bb.pos.x.toFixed(2)}" y="${bb.pos.y.toFixed(2)}" font-size="3">${bb.id}</text>`)
    }
    for (const [wid, ch] of e.chains) {
      for (let v = 0; v < ch.pts.length; v++) {
        for (const n of ch.adj[v]!) {
          if (n <= v) continue
          parts.push(`<line x1="${ch.pts[v]!.x.toFixed(2)}" y1="${ch.pts[v]!.y.toFixed(2)}" x2="${ch.pts[n]!.x.toFixed(2)}" y2="${ch.pts[n]!.y.toFixed(2)}" stroke="green" stroke-width="0.4"/>`)
        }
        parts.push(`<circle cx="${ch.pts[v]!.x.toFixed(2)}" cy="${ch.pts[v]!.y.toFixed(2)}" r="0.4" fill="green"/>`)
      }
      void wid
    }
    frames.push(`<g transform="translate(${f * 100},0)">${parts.join('')}</g>`)
  }
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="-65 -65 420 130">${frames.join('')}</svg>`
  writeFileSync('/tmp/claude-1001/-home-ahart-Documents-VisualProofAssistant/a640ce42-c609-401f-a2ca-17a76e2bb103/scratchpad/tow-frames.svg', svg)
  console.log('dumped')
})
