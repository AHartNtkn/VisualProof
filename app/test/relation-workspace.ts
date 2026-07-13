import { mkDiagram, type Diagram, type WireId } from '../../src/kernel/diagram/diagram'
import type { PlacementHint } from '../../src/kernel/proof/action'
import type { ProofContext } from '../../src/kernel/proof/step'
import { mkEngine } from '../../src/view/engine'
import { LIGHT, type Shape } from '../../src/view/paint'
import type { MutableView } from '../../src/app/interact/viewport'
import {
  RelationWorkspace,
  type RelationWorkspaceTransaction,
  type WorkspaceStatus,
} from '../../src/app/relation-workspace'
import {
  addRelationTerm,
  beginAbstractionDraft,
  beginSubstitutionDraft,
  currentRelationDraft,
  insertOptionalPort,
  type RelationWorkspaceDraft,
  type RelationWorkspaceSnapshot,
} from '../../src/app/relation-workspace-draft'
import { bvar, lam } from '../../src/kernel/term/term'

type Mode = RelationWorkspaceTransaction['mode']
type FinalizeBehavior = 'succeed' | 'refuse'

const canvas = document.querySelector('#host')
if (!(canvas instanceof HTMLCanvasElement)) throw new Error('missing host canvas')

const source: Diagram = mkDiagram({
  root: 'r0',
  regions: {
    r0: { kind: 'sheet' },
    bubble: { kind: 'bubble', parent: 'r0', arity: 1 },
  },
  wires: { host: { scope: 'r0', endpoints: [] } },
})
const hostEngine = mkEngine(source, [])
const view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
const context: ProofContext = { theorems: new Map(), relations: new Map() }

let workspace: RelationWorkspace | null = null
let cancelCount = 0
let finalizeCount = 0
let refusals: string[] = []

function initialDraft(mode: Mode): RelationWorkspaceDraft {
  const draft = mode === 'substitute'
    ? beginSubstitutionDraft(source, 'bubble')
    : beginAbstractionDraft(source)
  const withTerm = addRelationTerm(draft, lam(bvar(0)))
  const wire = Object.keys(currentRelationDraft(withTerm).diagram.wires)
    .find((candidate) => !candidate.startsWith('arg'))!
  return insertOptionalPort(withTerm, wire, 0)
}

function mount(mode: Mode, finalizeBehavior: FinalizeBehavior = 'succeed'): void {
  workspace?.dispose()
  cancelCount = 0
  finalizeCount = 0
  refusals = []
  const transaction: RelationWorkspaceTransaction = {
    mode,
    title: mode === 'substitute' ? 'SUBSTITUTE FIXTURE' : 'ABSTRACT FIXTURE',
    finalizeLabel: mode === 'substitute' ? 'Instantiate' : 'Abstract',
    sourceDiagram: () => source,
    sourceBoundary: () => [],
    previewShapes: (): readonly Shape[] => [],
    status: (): WorkspaceStatus => ({ kind: 'ready', message: 'ready' }),
    finalize: (_snapshot: RelationWorkspaceSnapshot, _placements: readonly PlacementHint[]) => {
      if (finalizeBehavior === 'refuse') throw new Error('fixture kernel refusal')
      finalizeCount += 1
    },
    cancel: () => { cancelCount += 1 },
  }
  workspace = new RelationWorkspace({
    mount: document.body,
    canvas,
    engine: () => hostEngine,
    view: () => view,
    context: () => context,
    theme: () => LIGHT,
    fuel: () => 100,
    refuse: (text) => { refusals.push(text) },
    changed: () => { workspace?.frame(performance.now()) },
    openChanged: (open) => { if (!open) workspace = null },
  }, transaction, initialDraft(mode), { x: 80, y: 80 })
  workspace.frame(performance.now())
}

declare global {
  interface Window {
    relationWorkspaceFixture: {
      mount(mode: Mode, finalizeBehavior?: FinalizeBehavior): void
      state(): {
        cancelCount: number
        finalizeCount: number
        refusals: string[]
        debug: ReturnType<RelationWorkspace['debugState']> | null
      }
    }
  }
}

window.relationWorkspaceFixture = {
  mount,
  state: () => ({
    cancelCount,
    finalizeCount,
    refusals: [...refusals],
    debug: workspace?.debugState() ?? null,
  }),
}
