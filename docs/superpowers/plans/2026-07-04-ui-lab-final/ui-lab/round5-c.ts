/**
 * ROUND 5 · C — the proof as a timeline. A bottom strip shows the derivation
 * growing from BOTH ends toward the middle: [lhs] forward steps → ⋯gap⋯ ←
 * backward steps [rhs]. Clicking any chip peeks that historic state in an
 * inset (the memory box generalized to the whole proof). The gap chip is the
 * meet indicator and becomes the assemble button when the sides agree; after
 * assembly the strip turns into a REPLAY scrubber over the checked theorem
 * (chips = steps; ←/→ walk it).
 */
import { boot, promptAt, type BrushHandle } from './shared'
import { renderPreview } from './prove'
import { installVerdictMoves, mkRefusalBubble } from './verdict'
import { mkSessionLab, sessionStart } from './session5'
import type { Diagram, WireId } from '../src/kernel/diagram/diagram'

boot('Round 5 · C — proof timeline', 'the derivation grows from both ends toward the gap; click a chip to peek that state; the gap assembles on meet, then scrubs the replay', (lab) => {
  const sess = mkSessionLab(lab)
  let brushRef: BrushHandle | null = null
  const refuse = mkRefusalBubble(lab, () => brushRef)
  const brush = installVerdictMoves(lab, sess.sink(refuse))
  brushRef = brush

  const strip = document.createElement('div')
  strip.style.cssText = 'position:fixed;left:0;right:0;bottom:28px;z-index:7;display:flex;justify-content:center;align-items:center;gap:4px;padding:6px;background:#ffffffe8;border-top:1px solid #ccc;font:12px system-ui;flex-wrap:wrap'
  document.body.append(strip)
  const peek = document.createElement('div')
  peek.style.cssText = 'position:fixed;right:8px;bottom:70px;z-index:8;display:none;background:#fff;border:1.5px solid #57534e;border-radius:8px;box-shadow:0 4px 16px #0003;font:12px system-ui'
  const peekLabel = document.createElement('div')
  peekLabel.style.cssText = 'padding:3px 8px;color:#57534e;border-bottom:1px solid #eee'
  const peekCanvas = document.createElement('canvas')
  peekCanvas.width = 300; peekCanvas.height = 210
  peek.append(peekLabel, peekCanvas)
  document.body.append(peek)
  const showPeek = (label: string, d: Diagram, boundary: readonly WireId[]): void => {
    peekLabel.textContent = label
    renderPreview(peekCanvas, d, boundary.filter((w) => d.wires[w] !== undefined))
    peek.style.display = 'block'
  }
  window.addEventListener('keydown', (e) => { if (e.key === 'Escape') { peek.style.display = 'none' } })

  let replay: { states: { d: Diagram; boundary: readonly WireId[] }[]; labels: string[]; k: number } | null = null
  const chip = (label: string, opts: { strong?: boolean; green?: boolean; active?: boolean; onClick?: () => void }): HTMLElement => {
    const c = document.createElement('button')
    c.textContent = label
    c.style.cssText = `font:12px system-ui;padding:3px 9px;border-radius:999px;cursor:${opts.onClick ? 'pointer' : 'default'};border:1.5px solid ${opts.green ? '#16a34a' : opts.strong ? '#d97706' : '#bbb'};background:${opts.active ? '#fde68a' : opts.green ? '#dcfce7' : '#fff'};${opts.strong ? 'font-weight:600;' : ''}`
    if (opts.onClick) c.addEventListener('click', opts.onClick)
    return c
  }
  const rebuild = () => {
    strip.replaceChildren()
    if (replay !== null) {
      const r = replay
      strip.append(chip('replay:', {}))
      r.states.forEach((st, i) => {
        strip.append(chip(i === 0 ? 'lhs' : r.labels[i - 1]!, {
          strong: i === 0 || i === r.states.length - 1,
          active: i === r.k,
          onClick: () => { r.k = i; showPeek(`replay ${i}/${r.states.length - 1}`, st.d, st.boundary); rebuild() },
        }))
      })
      strip.append(chip('exit replay', { onClick: () => { replay = null; peek.style.display = 'none'; rebuild() } }))
      return
    }
    const s = sess.session()
    const fStates = sess.states('forward'), bStates = sess.states('backward')
    const fLabels = sess.stepLabels('forward'), bLabels = sess.stepLabels('backward')
    strip.append(chip('lhs', {
      strong: true,
      active: sess.side() === 'forward',
      onClick: () => { if (sess.side() !== 'forward') { sess.swap(); brush.clear() } },
    }))
    fLabels.forEach((l, i) => strip.append(chip(l, { onClick: () => showPeek(`forward after step ${i + 1}: ${l}`, fStates[i + 1]!, s.lhs.boundary) })))
    const met = sess.met()
    strip.append(chip(met ? 'MET — assemble…' : '⋯ gap ⋯', {
      green: met,
      onClick: met ? () => {
        promptAt(innerWidth / 2 - 100, 60, 'name the theorem', (name) => {
          if (name.trim() === '') { refuse('a theorem needs a name'); return false }
          try {
            const thm = sess.assemble(name.trim())
            replay = { states: sess.replayStates(thm), labels: thm.steps.map((st) => st.rule === 'theorem' ? `cite ${st.name}` : st.rule), k: 0 }
            lab.toast(`theorem '${name.trim()}' assembled and checked — the strip now scrubs its replay`)
            rebuild()
            return true
          } catch (e) { refuse(e instanceof Error ? e.message : String(e)); return false }
        })
      } : undefined,
    }))
    for (let i = bLabels.length - 1; i >= 0; i--) {
      strip.append(chip(bLabels[i]!, { onClick: () => showPeek(`backward after step ${i + 1}: ${bLabels[i]}`, bStates[i + 1]!, s.rhs.boundary) }))
    }
    strip.append(chip('rhs', {
      strong: true,
      active: sess.side() === 'backward',
      onClick: () => { if (sess.side() !== 'backward') { sess.swap(); brush.clear() } },
    }))
  }
  sess.onChange(rebuild)
  rebuild()

  window.addEventListener('keydown', (e) => {
    if (replay === null || document.activeElement instanceof HTMLInputElement) return
    if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return
    replay.k = Math.max(0, Math.min(replay.states.length - 1, replay.k + (e.key === 'ArrowRight' ? 1 : -1)))
    const st = replay.states[replay.k]!
    showPeek(`replay ${replay.k}/${replay.states.length - 1}`, st.d, st.boundary)
    rebuild()
  })
}, sessionStart)
