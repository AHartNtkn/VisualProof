import { describe, expect, it } from 'vitest'
import {
  PUZZLE_PREVIEW_HEIGHT,
  PUZZLE_PREVIEW_RENDERER_VERSION,
  PUZZLE_PREVIEW_WIDTH,
  puzzlePreviewKey,
} from '../../src/game/interface/puzzle-preview-contract'

describe('puzzle preview contract', () => {
  it('keys derived rasters by renderer, logical fingerprint, and fixed dimensions', () => {
    expect(PUZZLE_PREVIEW_RENDERER_VERSION).toBe('dark-slate-v1')
    expect(PUZZLE_PREVIEW_WIDTH).toBe(640)
    expect(PUZZLE_PREVIEW_HEIGHT).toBe(400)
    expect(puzzlePreviewKey('logical-form')).toBe(
      'cursebreaker-thumbnail:dark-slate-v1:logical-form:640x400',
    )
  })
})
