import { mountShell } from '../src/app'
import { AESTHETIC_THEMES } from './aesthetic-themes'
import { loadLibraryFixture } from './library-fixture'
import { createLibraryPrototype, type LibraryPrototypeVariant } from './library-prototype'

const canvas = document.getElementById('c')
const chrome = document.getElementById('chrome')
if (!(canvas instanceof HTMLCanvasElement) || !(chrome instanceof HTMLElement)) {
  throw new Error('the Library app surface is incomplete')
}

const value = new URLSearchParams(location.search).get('library')
if (value !== 'ledger' && value !== 'prism' && value !== 'shelf') throw new Error(`unknown Library variant '${value ?? ''}'`)
const variant: LibraryPrototypeVariant = value

const fixture = await loadLibraryFixture()
await mountShell({
  canvas,
  chrome,
  initialDiagram: fixture.diagram.diagram,
  themes: AESTHETIC_THEMES.porcelain,
  initialLibrary: fixture.library,
  initialDirectoryHandle: fixture.directory,
  initialLibraryErrors: fixture.errors,
  libraryRenderer: createLibraryPrototype(variant),
})

;(window as Window & { __libraryDemo?: { variant: string } }).__libraryDemo = { variant }
