import { mountShell } from '../src/app'
import { AESTHETIC_THEMES } from './aesthetic-themes'
import { loadLibraryFixture } from './library-fixture'
import { createLibraryPrototype } from './library-prototype'

const canvas = document.getElementById('c')
const chrome = document.getElementById('chrome')
if (!(canvas instanceof HTMLCanvasElement) || !(chrome instanceof HTMLElement)) {
  throw new Error('the feedback app surface is incomplete')
}

const value = new URLSearchParams(location.search).get('feedback')
if (value !== 'field' && value !== 'ribbon' && value !== 'chronicle') {
  throw new Error(`unknown feedback variant '${value ?? ''}'`)
}
const fixture = await loadLibraryFixture()
await mountShell({
  canvas,
  chrome,
  initialDiagram: fixture.diagram.diagram,
  themes: AESTHETIC_THEMES.porcelain,
  initialLibrary: fixture.library,
  initialDirectoryHandle: fixture.directory,
  initialLibraryErrors: fixture.errors,
  libraryRenderer: createLibraryPrototype('ledger'),
})

;(window as Window & { __feedbackDemo?: { readonly variant: string } }).__feedbackDemo = { variant: value }
