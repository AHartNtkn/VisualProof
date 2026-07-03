/**
 * ROUND 2 · A — "verbs on selection". All construction goes through the
 * Round-1 brush: select things, then press a verb on the floating bar that
 * follows the selection. Verbs light up only when applicable (join needs
 * exactly two wires; sever exactly one, then you pick the strand). Creation
 * verbs live on a docked bar when nothing is selected. Ctrl+Z / Delete work.
 */
import { boot, installBrush, installEditKeys, legShape, mergeWires, promptAt, severLeg, spawnRelAt, spawnTermAt, tryEdit, wrapHits, REL_PALETTE } from './shared'

boot('Round 2 · A — verbs on selection', 'brush-select, then press a verb; verbs enable by applicability', (lab) => {
  const brush = installBrush(lab)
  installEditKeys(lab, brush)
  let severPick: { wid: string } | null = null

  const bar = document.createElement('div')
  bar.style.cssText = 'position:fixed;z-index:7;display:flex;gap:4px;padding:4px;background:#ffffffe8;border:1px solid #ccc;border-radius:8px;font:13px system-ui;box-shadow:0 2px 8px #0002'
  document.body.append(bar)
  const btn = (label: string, onClick: () => void): HTMLButtonElement => {
    const b = document.createElement('button')
    b.textContent = label
    b.style.cssText = 'font:13px system-ui;padding:3px 9px;border:1px solid #bbb;border-radius:6px;background:#fff;cursor:pointer'
    b.addEventListener('pointerdown', (e) => e.stopPropagation())
    b.addEventListener('click', onClick)
    bar.append(b)
    return b
  }
  const selWires = () => brush.selected.filter((h) => h.kind === 'wire')
  const selRegionTarget = () =>
    brush.selected.length === 1 && brush.selected[0]!.kind === 'region' ? brush.selected[0]!.id : lab.d.root

  const bJoin = btn('join', () => {
    const ws = selWires()
    tryEdit(lab, () => {
      lab.mutate(mergeWires(lab.d, ws[0]!.id, ws[1]!.id))
      brush.prune()
      lab.toast('joined the two lines')
    })
  })
  const bSever = btn('sever…', () => {
    severPick = { wid: selWires()[0]!.id }
    lab.toast('sever: click the strand to detach (Esc cancels)')
  })
  const bCut = btn('cut around', () => {
    if (tryEdit(lab, () => { wrapHits(lab, brush.selected, null) })) { brush.clear(); lab.toast('wrapped in a cut') }
  })
  const bBubble = btn('bubble…', () => {
    promptAt(innerWidth / 2 - 100, 60, 'bubble arity (e.g. 1)', (t) => {
      const n = Number(t)
      if (!Number.isInteger(n) || n < 0) { lab.toast(`'${t}' is not a valid arity`); return false }
      if (tryEdit(lab, () => { wrapHits(lab, brush.selected, n) })) { brush.clear(); lab.toast('wrapped in a bubble'); return true }
      return false
    })
  })
  const bTerm = btn('+ term…', () => {
    const region = selRegionTarget()
    promptAt(innerWidth / 2 - 100, 60, 'λ-term, e.g. \\x. x x', (t) =>
      tryEdit(lab, () => {
        spawnTermAt(lab, region, t, lab.toWorld(innerWidth / 2, innerHeight / 2))
        lab.toast(`term added in '${region}'`)
      }))
  })
  const relBtns = REL_PALETTE.map((r) => {
    const b = btn(`+ ${r.name}`, () => {
      tryEdit(lab, () => {
        spawnRelAt(lab, selRegionTarget(), r.name, r.arity, lab.toWorld(innerWidth / 2, innerHeight / 2))
        lab.toast(`${r.name}/${r.arity} added`)
      })
    })
    return b
  })
  const bUndo = btn('undo', () => { if (lab.undo()) { brush.prune(); lab.toast('undo') } else lab.toast('nothing to undo') })

  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') severPick = null })
  lab.canvas.addEventListener('pointerdown', (e) => {
    if (severPick === null) return
    const g = lab.legAt(lab.toWorld(e.clientX, e.clientY), 3)
    if (g !== null && g.leg.wid === severPick.wid) {
      if (severLeg(lab, g)) { lab.toast('severed'); brush.prune() }
      severPick = null
      e.stopImmediatePropagation()
    }
  }, { capture: true })

  lab.overlay((out) => {
    if (severPick !== null) {
      for (const g of lab.legs()) if (g.leg.wid === severPick.wid) out.push(legShape(g, '#dc2626', 3.2))
    }
  })
  lab.onFrame(() => {
    const enable = (b: HTMLButtonElement, on: boolean) => {
      b.disabled = !on
      b.style.opacity = on ? '1' : '0.35'
    }
    enable(bJoin, selWires().length === 2)
    enable(bSever, selWires().length === 1)
    enable(bCut, brush.selected.length > 0)
    enable(bBubble, brush.selected.length > 0)
    enable(bTerm, true); enable(bUndo, true)
    for (const b of relBtns) enable(b, true)
    if (brush.selected.length === 0) {
      bar.style.left = '50%'; bar.style.transform = 'translateX(-50%)'; bar.style.top = ''
      bar.style.bottom = '34px'
    } else {
      let sx = 0, sy = 0, n = 0
      for (const h of brush.selected) {
        const p = h.kind === 'node' ? lab.engine.bodies.get(h.id)?.pos
          : h.kind === 'region' ? lab.engine.regions.get(h.id)?.center : null
        if (p) { sx += p.x; sy += p.y; n++ }
      }
      if (n === 0) { const c = lab.engine.regions.get(lab.d.root)?.center; if (c) { sx = c.x; sy = c.y; n = 1 } }
      const px = sx / Math.max(n, 1) * lab.view.scale + lab.view.offsetX
      const py = sy / Math.max(n, 1) * lab.view.scale + lab.view.offsetY
      bar.style.transform = ''
      bar.style.left = `${Math.max(8, Math.min(innerWidth - 380, px - 150))}px`
      bar.style.top = `${Math.max(40, py - 70)}px`
      bar.style.bottom = ''
    }
  })
})
