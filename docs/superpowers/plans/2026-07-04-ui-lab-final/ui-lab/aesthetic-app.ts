import { mountShell } from '../src/app'
import { loadTheory } from '../src/kernel/proof/store'
import { AESTHETIC_THEMES, aestheticId } from './aesthetic-themes'

const canvas = document.getElementById('c')
const chrome = document.getElementById('chrome')
if (!(canvas instanceof HTMLCanvasElement) || !(chrome instanceof HTMLElement)) {
  throw new Error('the aesthetic app surface is incomplete')
}

const aesthetic = aestheticId(new URLSearchParams(location.search).get('aesthetic'))
const response = await fetch('/examples/frege.json')
if (!response.ok) throw new Error(`failed to load the verified aesthetic fixture (${response.status})`)
const source = await response.text()
const loaded = loadTheory(JSON.parse(source))
const relation = loaded.theory.relations.nat
if (relation === undefined) throw new Error("the verified aesthetic fixture has no 'nat' relation")

await mountShell({ canvas, chrome, initialDiagram: relation.diagram, themes: AESTHETIC_THEMES[aesthetic] })

const input = document.getElementById('open-file-input')
if (!(input instanceof HTMLInputElement)) throw new Error('the real Library file input is missing')
const transfer = new DataTransfer()
transfer.items.add(new File([source], 'frege.json', { type: 'application/json' }))
input.files = transfer.files
input.dispatchEvent(new Event('change', { bubbles: true }))

;(window as Window & { __aestheticDemo?: { aesthetic: string; fixture: string } }).__aestheticDemo = {
  aesthetic,
  fixture: 'nat relation body',
}
