import { mountShell } from '../src/app/index'

const canvas = document.getElementById('c')
const chrome = document.getElementById('chrome')
if (!(canvas instanceof HTMLCanvasElement)) throw new Error("missing <canvas id='c'> in app/index.html")
if (!(chrome instanceof HTMLElement)) throw new Error("missing <div id='chrome'> in app/index.html")

// Boot reads the shipped theory data over the network, so mounting is async. A
// boot failure (missing/corrupt theory file) is shown loudly in the chrome and
// re-thrown — never a silent empty context.
mountShell({ canvas, chrome }).catch((e: unknown) => {
  const msg = e instanceof Error ? e.message : String(e)
  chrome.textContent = `boot failed: ${msg}`
  throw e
})
