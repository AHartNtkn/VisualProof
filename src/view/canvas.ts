import type { Shape } from './display'

/**
 * The only module that touches the canvas API — thin, untested browser glue.
 * The transform maps world units to device pixels.
 */
export function drawShapes(
  ctx: CanvasRenderingContext2D,
  shapes: readonly Shape[],
  transform: { readonly scale: number; readonly offsetX: number; readonly offsetY: number },
): void {
  const X = (x: number): number => x * transform.scale + transform.offsetX
  const Y = (y: number): number => y * transform.scale + transform.offsetY
  for (const s of shapes) {
    switch (s.kind) {
      case 'circle': {
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.r * transform.scale, 0, 2 * Math.PI)
        if (s.fill !== undefined) {
          ctx.fillStyle = s.fill
          ctx.fill()
        }
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = 1
        ctx.stroke()
        break
      }
      case 'arc': {
        ctx.beginPath()
        ctx.arc(X(s.center.x), Y(s.center.y), s.r * transform.scale, s.a0, s.a1)
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'segment': {
        ctx.beginPath()
        ctx.moveTo(X(s.from.x), Y(s.from.y))
        ctx.lineTo(X(s.to.x), Y(s.to.y))
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'polyline': {
        if (s.points.length === 0) break
        ctx.beginPath()
        ctx.moveTo(X(s.points[0]!.x), Y(s.points[0]!.y))
        for (const pt of s.points.slice(1)) ctx.lineTo(X(pt.x), Y(pt.y))
        ctx.strokeStyle = s.stroke
        ctx.lineWidth = s.width
        ctx.stroke()
        break
      }
      case 'label': {
        ctx.fillStyle = s.color
        ctx.font = `${12}px sans-serif`
        ctx.fillText(s.text, X(s.pos.x), Y(s.pos.y))
        break
      }
    }
  }
}
