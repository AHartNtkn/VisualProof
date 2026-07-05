import type { Shape } from './paint'
import type { Vec2 } from './vec'

/**
 * The only module that touches the canvas API — thin, untested browser glue.
 * The transform maps world units to device pixels; stroke WIDTHS, glow blur,
 * junction-dot radii and boundary ticks are already in device pixels (they do
 * not zoom), while circle/arc radii and disc-label sizes are world units and
 * scale with the view.
 */

/** Device-pixel blur of the theme glow. */
const GLOW_BLUR = 5
/** Half-length (device px) of a boundary-exit tick. */
const EXIT_TICK_HALF = 5

export function drawShapes(
  ctx: CanvasRenderingContext2D,
  shapes: readonly Shape[],
  transform: { readonly scale: number; readonly offsetX: number; readonly offsetY: number },
): void {
  const X = (x: number): number => x * transform.scale + transform.offsetX
  const Y = (y: number): number => y * transform.scale + transform.offsetY
  const P = (p: Vec2): { x: number; y: number } => ({ x: X(p.x), y: Y(p.y) })
  const setGlow = (glow: string | null): void => {
    if (glow === null) { ctx.shadowBlur = 0; return }
    ctx.shadowColor = glow
    ctx.shadowBlur = GLOW_BLUR
  }
  ctx.lineJoin = 'round'
  ctx.lineCap = 'round'
  for (const s of shapes) {
    switch (s.kind) {
      case 'frame': {
        ctx.beginPath()
        ctx.roundRect(X(s.x), Y(s.y), s.w * transform.scale, s.h * transform.scale, s.cornerW * transform.scale)
        ctx.fillStyle = s.fill
        ctx.fill()
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'circle': {
        const cx = X(s.center.x), cy = Y(s.center.y), r = s.r * transform.scale
        ctx.beginPath()
        ctx.arc(cx, cy, r, 0, 2 * Math.PI)
        if (s.fill !== null) { ctx.fillStyle = s.fill; ctx.fill() }
        if (s.insetColor !== null) {
          const grad = ctx.createRadialGradient(cx, cy, r * 0.72, cx, cy, r)
          grad.addColorStop(0, 'rgba(0,0,0,0)')
          grad.addColorStop(1, s.insetColor)
          ctx.fillStyle = grad
          ctx.fill()
        }
        if (s.stroke !== null) {
          setGlow(s.glow)
          ctx.strokeStyle = s.stroke
          ctx.lineWidth = s.width
          ctx.stroke()
          ctx.shadowBlur = 0
        }
        break
      }
      case 'arc': {
        setGlow(s.glow)
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.r * transform.scale, s.a0, s.a1)
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        ctx.shadowBlur = 0
        break
      }
      case 'segment': {
        setGlow(s.glow)
        ctx.beginPath()
        ctx.moveTo(X(s.from.x), Y(s.from.y))
        ctx.lineTo(X(s.to.x), Y(s.to.y))
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        ctx.shadowBlur = 0
        break
      }
      case 'polyline': {
        if (s.pts.length < 2) break
        setGlow(s.glow)
        ctx.beginPath()
        const p0 = P(s.pts[0]!)
        ctx.moveTo(p0.x, p0.y)
        for (let i = 1; i < s.pts.length; i++) { const q = P(s.pts[i]!); ctx.lineTo(q.x, q.y) }
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        ctx.shadowBlur = 0
        break
      }
      case 'exit': {
        setGlow(s.glow)
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        if (s.pts.length >= 2) {
          ctx.beginPath()
          const p0 = P(s.pts[0]!)
          ctx.moveTo(p0.x, p0.y)
          for (let i = 1; i < s.pts.length; i++) { const q = P(s.pts[i]!); ctx.lineTo(q.x, q.y) }
          ctx.stroke()
        }
        const q = P(s.tick.center)
        const tx = Math.cos(s.tick.angle) * EXIT_TICK_HALF, ty = Math.sin(s.tick.angle) * EXIT_TICK_HALF
        ctx.beginPath()
        ctx.moveTo(q.x - tx, q.y - ty)
        ctx.lineTo(q.x + tx, q.y + ty)
        ctx.stroke()
        ctx.shadowBlur = 0
        break
      }
      case 'stub': {
        setGlow(s.glow)
        const a = P(s.from), b = P(s.to)
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.beginPath()
        ctx.moveTo(a.x, a.y)
        ctx.lineTo(b.x, b.y)
        ctx.stroke()
        ctx.shadowBlur = 0
        const d = P(s.dot)
        ctx.beginPath()
        ctx.arc(d.x, d.y, s.dotRpx, 0, 2 * Math.PI)
        ctx.fillStyle = s.stroke
        ctx.fill()
        break
      }
      case 'dot': {
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.rPx, 0, 2 * Math.PI)
        ctx.fillStyle = s.fill
        ctx.fill()
        break
      }
      case 'label': {
        const size = Math.max(8.5, Math.min(14, s.r * transform.scale * 0.5))
        ctx.font = `600 ${size}px ${s.font}`
        ctx.textAlign = 'center'
        ctx.textBaseline = 'middle'
        ctx.fillStyle = s.color
        ctx.fillText(s.text, X(s.center.x), Y(s.center.y))
        break
      }
    }
  }
}
