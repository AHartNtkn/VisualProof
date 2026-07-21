import { diagramFromJson } from '../../kernel/diagram/json'
import { fitCamera } from '../../view/camera'
import { rasterizeShapes } from '../../view/canvas'
import { mkEngine } from '../../view/engine'
import { DARK, paint } from '../../view/paint'
import { seedProject, settleStep } from '../../view/relax'
import type { PuzzlePreviewRequest } from './puzzle-preview-contract'

const PREVIEW_RELAXATION_STEPS = 16

export async function renderPuzzlePreview(request: PuzzlePreviewRequest): Promise<Blob> {
  const diagram = diagramFromJson(request.diagram)
  const engine = mkEngine(diagram, [])
  seedProject(engine)
  for (let index = 0; index < PREVIEW_RELAXATION_STEPS; index += 1) {
    settleStep(engine, null)
  }

  const view = fitCamera(
    engine.frame === null
      ? undefined
      : { center: engine.frame.center, radius: engine.frame.half },
    request.width,
    request.height,
    1,
  )
  return rasterizeShapes(
    request.width,
    request.height,
    DARK.canvas,
    paint(engine, DARK).filter((shape) => shape.kind !== 'frame'),
    view,
  )
}
