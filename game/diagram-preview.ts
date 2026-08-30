import type { DiagramSnapshot } from '../src/game/diagram-snapshot'
import { scene3, type Entity } from '../src/view3d/scene'
import type { Vec3 } from '../src/view3d/vec3'

const BRANCH_COLOR = '#b1e09b'
const CUT_BRANCH_COLOR = '#879a85'
const WIRE_COLOR = '#5bd2de'

type DrawableEntity = Extract<Entity, { kind: 'branch' | 'strand' }>

function isDrawable(entity: Entity): entity is DrawableEntity {
  return entity.kind === 'branch' || entity.kind === 'strand'
}

export function renderDiagramPreview(canvas: HTMLCanvasElement, snapshot: DiagramSnapshot): void {
  const context = canvas.getContext('2d')
  if (context === null) throw new Error('diagram preview requires a 2D canvas context')

  const scene = scene3(snapshot.diagram)
  const width = canvas.width
  const height = canvas.height
  const radius = Math.max(scene.radius, Number.EPSILON)
  const scale = Math.min(width, height) * 0.42 / radius
  const project = (point: Vec3): readonly [number, number] => [
    width / 2 + (point.x - scene.center.x) * scale,
    height / 2 - (point.y - scene.center.y) * scale,
  ]

  context.clearRect(0, 0, width, height)
  context.save()
  context.lineCap = 'round'
  context.lineJoin = 'round'
  for (const entity of scene.entities) {
    if (!isDrawable(entity) || entity.pts.length < 2) continue
    context.beginPath()
    const [startX, startY] = project(entity.pts[0]!)
    context.moveTo(startX, startY)
    for (const point of entity.pts.slice(1)) {
      const [x, y] = project(point)
      context.lineTo(x, y)
    }
    context.strokeStyle = entity.kind === 'strand'
      ? WIRE_COLOR
      : entity.polarity === 0 ? BRANCH_COLOR : CUT_BRANCH_COLOR
    context.lineWidth = entity.kind === 'strand' ? 1.5 : 2.25
    context.stroke()
  }
  context.restore()
}
