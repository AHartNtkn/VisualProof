import type {
  PuzzlePreviewWorkerRequest,
  PuzzlePreviewWorkerResult,
} from './puzzle-preview-contract'
import { renderPuzzlePreview } from './puzzle-preview-renderer'

type WorkerScope = {
  onmessage: ((event: MessageEvent<PuzzlePreviewWorkerRequest>) => void) | null
  postMessage(message: PuzzlePreviewWorkerResult): void
}
const scope = self as unknown as WorkerScope

scope.onmessage = (event): void => {
  if (event.data.kind !== 'render') return
  const { generation, request } = event.data
  void renderPuzzlePreview(request).then(
    (blob) => scope.postMessage({ kind: 'ready', key: request.key, generation, blob }),
    (error) => scope.postMessage({
      kind: 'error',
      key: request.key,
      generation,
      message: error instanceof Error ? error.message : String(error),
    }),
  )
}
