/**
 * ROUND 6h · D — the verdict composite (see history.ts installScrubber):
 * the scrubber IS undo/redo, future retained, zoom-to-change hover popups.
 */
import { boot, emptyStart } from './shared'
import { mkChromeApp, installMinimalChrome } from './chrome'
import { installScrubber } from './history'

boot('Round 6h · D — scrubber = undo/redo', 'drag the bar: real time travel, future retained; new moves discard it; hover a tick = the change, zoomed; Ctrl+Z / Ctrl+Shift+Z', (lab) => {
  const app = mkChromeApp(lab)
  installMinimalChrome(lab, app)
  installScrubber(lab, app)
}, emptyStart)
