/**
 * ROUND 5 · B — PiP target. One full-size working view; the side you are
 * MEETING sits in a corner inset (the plan-17 companion, session-refined).
 * S swaps which side you work on; the meet chip lives in the inset header.
 * Same goal and machinery as 5a — the question is pure presentation:
 * split lanes vs corner target.
 */
import { boot, promptAt, type BrushHandle } from './shared'
import { renderPreview } from './prove'
import { installVerdictMoves, mkRefusalBubble } from './verdict'
import { mkSessionLab, sessionStart } from './session5'

boot('Round 5 · B — PiP target', 'full-size working view; the side you are meeting is the corner inset; S swaps sides; A assembles on meet', (lab) => {
  const sess = mkSessionLab(lab)
  let brushRef: BrushHandle | null = null
  const refuse = mkRefusalBubble(lab, () => brushRef)
  const brush = installVerdictMoves(lab, sess.sink(refuse))
  brushRef = brush

  const pip = document.createElement('div')
  pip.style.cssText = 'position:fixed;right:8px;bottom:34px;z-index:7;background:#fff;border:1.5px solid #d97706;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const pipLabel = document.createElement('div')
  pipLabel.style.cssText = 'padding:3px 8px;border-bottom:1px solid #eee;display:flex;justify-content:space-between;gap:8px'
  const pipCanvas = document.createElement('canvas')
  pipCanvas.width = 300; pipCanvas.height = 210
  pip.append(pipLabel, pipCanvas)
  document.body.append(pip)

  const repaint = () => {
    const other = sess.side() === 'forward' ? 'backward' : 'forward'
    const met = sess.met()
    pipLabel.innerHTML = `<span>meeting: ${other} side (S swaps)</span><span style="color:${met ? '#16a34a' : '#999'};font-weight:600">${met ? 'MET — press A' : 'not met'}</span>`
    const st = sess.states(other)
    const cur = st[st.length - 1]!
    const bd = (other === 'forward' ? sess.session().lhs.boundary : sess.session().rhs.boundary).filter((w) => cur.wires[w] !== undefined)
    renderPreview(pipCanvas, cur, bd)
  }
  sess.onChange(repaint)
  setTimeout(repaint, 600)

  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key === 's' || e.key === 'S') { sess.swap(); brush.clear(); return }
    if (e.key !== 'a' && e.key !== 'A') return
    if (!sess.met()) { refuse('not met yet — the inset chip turns green when the sides agree'); return }
    promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
      if (name.trim() === '') { refuse('a theorem needs a name'); return false }
      try {
        sess.assemble(name.trim())
        lab.toast(`theorem '${name.trim()}' assembled, re-checked by replay, and added to the context`)
        return true
      } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
    })
  })
}, sessionStart)
