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
const LABEL_MAX_FONT_PX = 14
const LABEL_MIN_FONT_PX = 6
const LABEL_WIDTH_TO_RADIUS = 1.65

export type CanvasAdapter = {
  readonly size: () => { readonly width: number; readonly height: number }
  readonly syncSize: () => boolean
  readonly render: (
    shapes: readonly Shape[],
    transform: { readonly scale: number; readonly offsetX: number; readonly offsetY: number },
  ) => void
}

/**
 * Owns context acquisition, backing-store sizing, clearing, and drawing so the
 * app layer handles a canvas as an input surface without reaching through the
 * view adapter into browser drawing state.
 */
export function adaptCanvas(canvas: HTMLCanvasElement): CanvasAdapter {
  const ctx = canvas.getContext('2d')
  if (ctx === null) throw new Error('canvas has no 2d context')
  const size = (): { readonly width: number; readonly height: number } => ({ width: canvas.width, height: canvas.height })
  return {
    size,
    syncSize(): boolean {
      const width = canvas.clientWidth
      const height = canvas.clientHeight
      if (width <= 0 || height <= 0) return false
      if (canvas.width !== width || canvas.height !== height) {
        canvas.width = width
        canvas.height = height
      }
      return true
    },
    render(shapes, transform): void {
      ctx.clearRect(0, 0, canvas.width, canvas.height)
      drawShapes(ctx, shapes, transform)
    },
  }
}

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
        const radiusPx = s.r * transform.scale
        const maxWidth = Math.max(1, radiusPx * LABEL_WIDTH_TO_RADIUS)
        let size = Math.max(8.5, Math.min(LABEL_MAX_FONT_PX, radiusPx * 0.5))
        ctx.font = `600 ${size}px ${s.font}`
        const measuredWidth = ctx.measureText(s.text).width
        if (measuredWidth > maxWidth && measuredWidth > 0) {
          size = Math.max(LABEL_MIN_FONT_PX, size * maxWidth / measuredWidth)
          ctx.font = `600 ${size}px ${s.font}`
        }
        ctx.textAlign = 'center'
        ctx.textBaseline = 'middle'
        ctx.fillStyle = s.color
        // maxWidth is a final guard for exceptionally long leaves after the
        // readable font-size floor; Canvas scales the complete string to fit.
        ctx.fillText(s.text, X(s.center.x), Y(s.center.y), maxWidth)
        break
      }
    }
  }
}
