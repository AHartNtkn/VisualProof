import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram, type Diagram, type WireId } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { PlacementHint } from '../../src/kernel/proof/action'
import type { ProofContext } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { LIGHT, type Shape } from '../../src/view/paint'
import type { MutableView } from '../../src/app/interact/viewport'
import {
  RelationWorkspace,
  SubstituteTransaction,
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
import { AbstractTransaction } from '../../src/app/relation-transactions'

type Mode = RelationWorkspaceTransaction['mode']
type FinalizeBehavior = 'succeed' | 'refuse'
type AbstractionScenario = 'multi-set' | 'zero-match' | 'matcher-exhausted' | 'solver-exhausted'
  | 'stale-source' | 'kernel-refusal' | 'invalid-ports'

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
let hostEngine = mkEngine(source, [])
const view: MutableView = { scale: 1, offsetX: 0, offsetY: 0 }
const context: ProofContext = { theorems: new Map(), relations: new Map() }

let workspace: RelationWorkspace | null = null
let cancelCount = 0
let finalizeCount = 0
let refusals: string[] = []
let staleSourceAction: (() => void) | null = null

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
  staleSourceAction = null
  hostEngine = mkEngine(source, [])
  const transaction: RelationWorkspaceTransaction = {
    mode,
    title: mode === 'substitute' ? 'SUBSTITUTE FIXTURE' : 'ABSTRACT FIXTURE',
    finalizeLabel: mode === 'substitute' ? 'Instantiate' : 'Abstract',
    sourceDiagram: () => source,
    sourceBoundary: () => [],
    previewShapes: (): readonly Shape[] => [],
    status: (): WorkspaceStatus => ({ kind: 'ready', code: 'ready', message: 'ready' }),
    finalizeError: (error): WorkspaceStatus => ({
      kind: 'refused', code: 'kernel-refusal', message: error instanceof Error ? error.message : String(error),
    }),
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

function identityDiagram(count: number): Diagram {
  const builder = new DiagramBuilder()
  for (let index = 0; index < count; index++) builder.termNode(builder.root, parseTerm('\\x. x'))
  return builder.build()
}

function sharedIdentityDiagram(count: number): { diagram: Diagram; wire: WireId } {
  const builder = new DiagramBuilder()
  const endpoints = []
  for (let index = 0; index < count; index++) {
    const node = builder.termNode(builder.root, parseTerm('\\x. x'))
    endpoints.push({ node, port: { kind: 'output' as const } })
  }
  const wire = builder.wire(builder.root, endpoints)
  return { diagram: builder.build(), wire }
}

function unaryConstantDiagram(nested: boolean): { diagram: Diagram; wrap: ReturnType<typeof mkSelection> } {
  const builder = new DiagramBuilder()
  const anchor = nested ? builder.cut(builder.root) : builder.root
  const node = builder.termNode(anchor, parseTerm('\\x. \\y. x'))
  const diagram = builder.build()
  return {
    diagram,
    wrap: mkSelection(diagram, nested
      ? { region: diagram.root, regions: [anchor], nodes: [], wires: [] }
      : { region: diagram.root, regions: [], nodes: [node], wires: [] }),
  }
}

function mountAbstractionScenario(scenario: AbstractionScenario): void {
  workspace?.dispose()
  cancelCount = 0
  finalizeCount = 0
  refusals = []
  staleSourceAction = null

  if (scenario === 'invalid-ports') {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 1)
    const host = builder.build()
    const transaction = new SubstituteTransaction({
      diagram: () => host,
      boundary: () => [],
      bubble,
      context: () => context,
      apply: () => { finalizeCount += 1 },
      cancel: () => { cancelCount += 1 },
    })
    const invalidDraft: RelationWorkspaceDraft = {
      host,
      mode: 'substitute',
      history: [{
        diagram: mkDiagram({
          root: 'r0',
          regions: { r0: { kind: 'sheet' } },
          wires: {
            arg1: { scope: 'r0', endpoints: [] },
            loose: { scope: 'r0', endpoints: [] },
          },
        }),
        ports: [
          { id: 'forced1', wire: 'arg1', kind: 'forced' },
          { id: 'unbound', wire: 'loose', kind: 'optional' },
        ],
      }],
      cursor: 0,
    }
    hostEngine = mkEngine(host, [])
    mountTransaction(transaction, invalidDraft)
    return
  }

  const multi = scenario === 'multi-set' || scenario === 'solver-exhausted'
  const constant = scenario === 'zero-match' || scenario === 'matcher-exhausted'
  const multiHost = multi ? sharedIdentityDiagram(4) : null
  const initial = multiHost !== null
    ? { diagram: multiHost.diagram, wrap: undefined }
    : constant
      ? unaryConstantDiagram(scenario === 'matcher-exhausted')
      : { diagram: identityDiagram(1), wrap: undefined }
  const sourceDiagram = initial.diagram
  const wrap = initial.wrap ?? mkSelection(sourceDiagram, {
    region: sourceDiagram.root,
    regions: [],
    nodes: Object.keys(sourceDiagram.nodes),
    wires: [],
  })
  let live = sourceDiagram
  const multiPattern = multi ? sharedIdentityDiagram(2) : null
  const pattern = multiPattern !== null ? multiPattern.diagram : constant ? identityDiagram(1) : mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
  const draft: RelationWorkspaceDraft = {
    host: sourceDiagram,
    mode: 'abstract',
    history: [{
      diagram: pattern,
      ports: multiPattern === null ? [] : [{ id: 'pattern-port', wire: multiPattern.wire, kind: 'optional' }],
    }],
    cursor: 0,
  }
  hostEngine = mkEngine(sourceDiagram, [])
  const firstBody = hostEngine.bodies.get(Object.keys(sourceDiagram.nodes)[0]!)
  if (firstBody !== undefined && scenario === 'multi-set') firstBody.pos = { x: -177, y: -93 }
  if (firstBody !== undefined && scenario === 'stale-source') firstBody.pos = { x: 177, y: 93 }
  const transaction = new AbstractTransaction({
    diagram: () => live,
    boundary: () => [],
    wrap,
    context: () => context,
    orientation: scenario === 'kernel-refusal' ? 'backward' : 'forward',
    apply: () => { finalizeCount += 1 },
    cancel: () => { cancelCount += 1 },
    engine: () => hostEngine,
    theme: () => LIGHT,
    matcherFuel: () => scenario === 'matcher-exhausted' ? 1 : 4096,
    solverFuel: () => scenario === 'solver-exhausted' ? 1 : 100000,
  })
  staleSourceAction = scenario === 'stale-source'
    ? () => { live = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } }) }
    : null
  mountTransaction(transaction, draft)
}

function mountTransaction(transaction: RelationWorkspaceTransaction, draft: RelationWorkspaceDraft): void {
  workspace = new RelationWorkspace({
    mount: document.body,
    canvas,
    engine: () => hostEngine,
    view: () => view,
    context: () => context,
    theme: () => LIGHT,
    fuel: () => 512,
    refuse: (text) => { refusals.push(text) },
    changed: () => { workspace?.frame(performance.now()) },
    openChanged: (open) => { if (!open) workspace = null },
  }, transaction, draft, { x: 80, y: 80 })
  workspace.frame(performance.now())
}

declare global {
  interface Window {
    relationWorkspaceFixture: {
      mount(mode: Mode, finalizeBehavior?: FinalizeBehavior): void
      mountAbstractionScenario(scenario: AbstractionScenario): void
      staleSource(): void
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
  mountAbstractionScenario,
  staleSource: () => { staleSourceAction?.() },
  state: () => ({
    cancelCount,
    finalizeCount,
    refusals: [...refusals],
    debug: workspace?.debugState() ?? null,
  }),
}
