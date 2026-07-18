import { GameProofViewport } from '../../src/game/interface/proof-surface'
import { gameProofMotionPreferences } from '../../src/game/interface/proof-motion'
import { applyStep, type ProofStep } from '../../src/kernel/proof/step'
import { DARK } from '../../src/view/paint'
import { comprehensionFixture } from '../app/comprehension-fixture'
import { minimalPuzzle } from './catalog-fixture'

const fixture = comprehensionFixture()
let diagram = fixture.diagram
let prepared = 0
let refusals = 0
const host = document.querySelector<HTMLElement>('#host')!
const surface = new GameProofViewport({
  host,
  diagram: () => diagram,
  boundary: () => [],
  context: () => ({ theorems: new Map(), relations: new Map() }),
  theme: () => DARK,
  fuel: () => 256,
  prepare: (step: ProofStep) => {
    prepared++
    const next = applyStep(diagram, step, { theorems: new Map(), relations: new Map() }, 'backward')
    return () => { diagram = next }
  },
  motionPreferences: () => gameProofMotionPreferences(true),
  inputAllowed: () => true,
  refuse: () => { refusals++ },
  changed: () => {},
})
surface.resize(innerWidth, innerHeight)

const state = {
  mapping: (client: { readonly x: number; readonly y: number }) => surface.mapClient(client),
  open: (): boolean => {
    const wire = Object.keys(diagram.wires)[0]!
    surface.interaction.setSelection([{ kind: 'wire', id: wire }])
    return surface.openConstruction(fixture.bubble, { x: innerWidth / 2, y: innerHeight / 2 })
  },
  editing: (): boolean => surface.editing,
  prepared: (): number => prepared,
  refusals: (): number => refusals,
  refuseIncompleteArtifact: (): void => {
    surface.dropArtifact(minimalPuzzle(), { x: 10, y: 10 })
  },
  cornerAlpha: (): number => {
    surface.frame(performance.now())
    return surface.canvas.getContext('2d')!.getImageData(0, 0, 1, 1).data[3]!
  },
}

declare global {
  interface Window { __gameProofSurfaceFixture: typeof state }
}
window.__gameProofSurfaceFixture = state

const animate = (now: number): void => {
  surface.frame(now)
  requestAnimationFrame(animate)
}
requestAnimationFrame(animate)
