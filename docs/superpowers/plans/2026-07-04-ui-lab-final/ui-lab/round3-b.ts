/**
 * ROUND 3 · B — the lit rule palette. The COMPLETE rule vocabulary is always
 * on screen (right strip); the current selection lights up what applies.
 * Hovering a dim rule explains what it needs (the teaching layer); clicking
 * a lit rule commits (iterate enters the target phase). The bet: newcomers
 * learn the calculus by watching what lights up as they select.
 */
import { boot, installBrush } from './shared'
import { commit, discover, installTargetPhase, installUndoKey, proveShowcase, RULE_VOCAB } from './prove'
import { polarity } from '../src/kernel/diagram/regions'

boot('Round 3 · B — lit rule palette', 'the whole vocabulary, always visible; selection lights up what applies; hover a dim rule to learn what it needs', (lab) => {
  const brush = installBrush(lab)
  installUndoKey(lab, brush)
  const picker = installTargetPhase(lab, brush)

  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;right:8px;top:44px;z-index:7;width:210px;background:#fffffff2;border:1px solid #ccc;border-radius:8px;font:13px system-ui;overflow:hidden'
  const polLine = document.createElement('div')
  polLine.style.cssText = 'padding:5px 10px;border-bottom:1px solid #eee;color:#666;font-size:12px'
  strip.append(polLine)
  const rows = RULE_VOCAB.map((v) => {
    const row = document.createElement('div')
    row.style.cssText = 'padding:6px 10px'
    row.textContent = v.label
    row.addEventListener('pointerenter', () => { if (row.dataset.on !== '1') lab.toast(`${v.label}: ${v.why}`) })
    row.addEventListener('click', () => {
      if (row.dataset.on !== '1') return
      const disc = discover(lab, brush.selected)
      if (disc === null) return
      const a = disc.actions.find((x) => x.kind === v.kind)
      if (a === undefined) return
      if (a.kind === 'iterate') picker.begin(disc.sel, a)
      else commit(lab, brush, disc.sel, a)
    })
    strip.append(row)
    return { v, row }
  })
  document.body.append(strip)

  let lastSig: string | null = null
  lab.onFrame(() => {
    const sig = brush.selected.map((h) => `${h.kind}:${h.id}`).sort().join(',')
    if (sig === lastSig) return
    lastSig = sig
    const disc = discover(lab, brush.selected)
    polLine.textContent = disc === null
      ? (brush.selected.length === 0 ? 'nothing selected' : 'selection spans regions')
      : `selection in '${disc.sel.region}' — ${polarity(lab.d, disc.sel.region)}`
    for (const { v, row } of rows) {
      const a = disc?.actions.find((x) => x.kind === v.kind)
      const parameterized = v.kind === 'insert' || v.kind === 'convert'
      const on = a !== undefined && !parameterized
      row.dataset.on = on ? '1' : '0'
      row.style.color = on ? '#111' : '#b8b2a7'
      row.style.cursor = on ? 'pointer' : 'default'
      row.style.background = on ? '#fde68a33' : ''
    }
  })
}, proveShowcase)
