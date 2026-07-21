import type { ProofAction } from '../../src/kernel/proof/action'
import { actionFromJson } from '../../src/kernel/proof/json'
import twoVeils from '../../content/validation/two-veils.json'
import fourVeils from '../../content/validation/four-veils.json'
import forkedVeil from '../../content/validation/forked-veil.json'
import echoedVeil from '../../content/validation/echoed-veil.json'
import emptyRingRelease from '../../content/validation/empty-ring-release.json'
import singleMarkReturn from '../../content/validation/single-mark-return.json'
import nestedOwnerIntroduction from '../../content/validation/nested-owner-introduction.json'
import twoMarkProjection from '../../content/validation/two-mark-projection.json'
import blankWitness from '../../content/validation/blank-witness.json'

type RawEvidence = {
  puzzle: string
  solution: unknown[]
  recognizedStates: Array<{ intervention: string; demonstration: unknown[] }>
}

const evidence = [
  twoVeils,
  fourVeils,
  forkedVeil,
  echoedVeil,
  emptyRingRelease,
  singleMarkReturn,
  nestedOwnerIntroduction,
  twoMarkProjection,
  blankWitness,
] as RawEvidence[]

export const openingWitness = (id: string): readonly ProofAction[] =>
  evidence.find(({ puzzle }) => puzzle === id)?.solution.map((action) => actionFromJson(action)) ?? []

export const openingDemonstration = (id: string, intervention: string): readonly ProofAction[] =>
  evidence.find(({ puzzle }) => puzzle === id)?.recognizedStates
    .find((entry) => entry.intervention === intervention)?.demonstration
    .map((action) => actionFromJson(action)) ?? []
