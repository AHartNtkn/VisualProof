/**
 * ROUND 5 · A — two-lane split. The other side of the proof is ALWAYS beside
 * you: the right pane renders it live (view-only); CLICK IT to work there
 * instead (the panes trade places). The meet banner between the lanes turns
 * green the moment both sides' canonical forms agree; press A to assemble,
 * name it, and the theorem joins the context (immediately citable).
 * Goal: succNat's own statement — one citation away, or the long way round.
 */
import { boot, promptAt, type BrushHandle } from './shared'
import { renderPreview } from './prove'
import { installVerdictMoves, mkRefusalBubble } from './verdict'
import { mkSessionLab, sessionStart } from './session5'

boot('Round 5 · A — two-lane split', 'left = the side you work; right = the other side, live; click it to swap; A assembles when the banner turns green', (lab) => {
  const sess = mkSessionLab(lab)
  let brushRef: BrushHandle | null = null
  const refuse = mkRefusalBubble(lab, () => brushRef)
  const brush = installVerdictMoves(lab, sess.sink(refuse))
  brushRef = brush

  // right lane: the other side, rendered on change
  const lane = document.createElement('div')
  lane.style.cssText = 'position:fixed;right:0;top:44px;bottom:28px;width:38vw;z-index:6;background:#f7f5efee;border-left:2px solid #d97706;display:flex;flex-direction:column;cursor:pointer'
  const laneLabel = document.createElement('div')
  laneLabel.style.cssText = 'padding:5px 12px;font:13px system-ui;color:#92400e;border-bottom:1px solid #ddd'
  const laneCanvas = document.createElement('canvas')
  laneCanvas.style.cssText = 'flex:1;width:100%'
  lane.append(laneLabel, laneCanvas)
  lane.title = 'click to work on this side'
  document.body.append(lane)
  lane.addEventListener('click', () => { sess.swap(); brush.clear() })

  // meet banner
  const banner = document.createElement('div')
  banner.style.cssText = 'position:fixed;left:50%;transform:translateX(-50%);top:44px;z-index:7;padding:5px 16px;border-radius:0 0 10px 10px;font:600 13px system-ui'
  document.body.append(banner)

  const repaint = () => {
    const other = sess.side() === 'forward' ? 'backward' : 'forward'
    laneLabel.textContent = `${other} side (the target you are meeting) — click to work here`
    const st = sess.states(other)
    const cur = st[st.length - 1]!
    laneCanvas.width = laneCanvas.clientWidth || 380
    laneCanvas.height = laneCanvas.clientHeight || 500
    const bd = (other === 'forward' ? sess.session().lhs.boundary : sess.session().rhs.boundary).filter((w) => cur.wires[w] !== undefined)
    renderPreview(laneCanvas, cur, bd)
    const met = sess.met()
    banner.textContent = met ? 'MET — the sides agree; press A to assemble' : `working ${sess.side()} · not met yet`
    banner.style.background = met ? '#16a34a' : '#78716c'
    banner.style.color = '#fff'
  }
  sess.onChange(repaint)
  setTimeout(repaint, 600)

  window.addEventListener('keydown', (e) => {
    if (document.activeElement instanceof HTMLInputElement) return
    if (e.key !== 'a' && e.key !== 'A') return
    if (!sess.met()) { refuse('the sides have not met yet — the banner turns green when they agree'); return }
    promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
      if (name.trim() === '') { refuse('a theorem needs a name'); return false }
      try {
        sess.assemble(name.trim())
        lab.toast(`theorem '${name.trim()}' assembled, re-checked by replay, and added to the context — it now cites like any other`)
        return true
      } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
    })
  })
}, sessionStart)
