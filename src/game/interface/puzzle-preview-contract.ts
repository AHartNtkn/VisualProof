export const PUZZLE_PREVIEW_WIDTH = 640
export const PUZZLE_PREVIEW_HEIGHT = 400
export const PUZZLE_PREVIEW_RENDERER_VERSION = 'dark-slate-v1'

export type PuzzlePreviewRequest = {
  readonly key: string
  readonly fingerprint: string
  readonly diagram: unknown
  readonly width: typeof PUZZLE_PREVIEW_WIDTH
  readonly height: typeof PUZZLE_PREVIEW_HEIGHT
}

export type PuzzlePreviewWorkerRequest = {
  readonly kind: 'render'
  readonly generation: number
  readonly request: PuzzlePreviewRequest
}

export type PuzzlePreviewWorkerResult =
  | {
      readonly kind: 'ready'
      readonly key: string
      readonly generation: number
      readonly blob: Blob
    }
  | {
      readonly kind: 'error'
      readonly key: string
      readonly generation: number
      readonly message: string
    }

export const puzzlePreviewKey = (fingerprint: string): string =>
  `cursebreaker-thumbnail:${PUZZLE_PREVIEW_RENDERER_VERSION}:${fingerprint}:${PUZZLE_PREVIEW_WIDTH}x${PUZZLE_PREVIEW_HEIGHT}`
