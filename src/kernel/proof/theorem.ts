import type { Diagram, DiagramNode, NodeId, WireId } from '../diagram/diagram'
import { mkDiagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { removeSubgraph, spliceSubgraphMapped } from '../diagram/subgraph/splice'
import type { IdReservation } from '../diagram/subgraph/freshId'
import { freshId } from '../diagram/subgraph/freshId'
import { sameDiagram } from '../diagram/canonical/iso'
import { diagramToJson } from '../diagram/json'
import { RuleError } from '../rules/error'
import type { ProofContext } from './context'
import { assertProofContext } from './context'
import { reboundWires, transportBoundary } from './step'
import type { StepReceipt } from './step'
import type { ProofAction } from './action'
import { replayActions } from './action'
import { ProofError } from './error'

export type Theorem = {
  readonly name: string
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
  /** Forward-oriented actions, replayed from the lhs. */
  readonly actions: readonly ProofAction[]
  /** Backward-oriented actions, replayed from the RHS with the flipped gates
      (the calculus's cut symmetry: each backward move S→S′ asserts S′ ⟹ S,
      so a chain from the rhs composes to lhs ⟹ rhs). A backward-proved
      theorem is recorded EXACTLY as the user derived it — no inverse steps
      are ever constructed. Absent = the all-forward classic form. */
  readonly backActions?: readonly ProofAction[]
}

export type TheoremApplication = {
  readonly sel: SubgraphSelection
  readonly args: readonly WireId[]
}

/**
 * Verify a theorem once: replay its steps from lhs.diagram (each applier
 * enforcing its own gate) and require the result, pinned by the lhs boundary,
 * to be isomorphic to the stated rhs respecting boundary order. Each step's
 * semantic interface transports the ordered boundary; positions may
 * coalesce, while a position with no image rejects the proof. Boundary wires
 * must be root-scoped on both stated sides (splice's stub invariant).
 *
 * Transport is checked after EVERY step, not just at the end, so a boundary
 * identity with no semantic image cannot be replaced later by an unrelated
 * wire that happens to reuse its identifier.
 */
/**
 * Close an open side for replay: every ordered boundary entry becomes a
 * frame pin — an arity-1 identity at the root standing in for the frame
 * exit, which is exactly the end that entry contributes. Deterministic ids
 * ('framepin', 'framepin_0', ...) so recording and checking mint alike.
 */
export function pinnedForReplay(side: DiagramWithBoundary): Diagram {
  const nodes: Record<NodeId, DiagramNode> = { ...side.diagram.nodes }
  const wires = { ...side.diagram.wires }
  const taken = new Set(Object.keys(nodes))
  side.boundary.forEach((wireId) => {
    const pin = freshId(taken, 'framepin')
    taken.add(pin)
    const wire = wires[wireId]!
    nodes[pin] = { kind: 'identity', region: side.diagram.root, sig: wire.sig, arity: 1 }
    wires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node: pin, port: { kind: 'identity', index: 0 } }],
    }
  })
  return mkDiagram({
    root: side.diagram.root,
    regions: { ...side.diagram.regions },
    nodes,
    wires,
  })
}

export function checkTheorem(thm: Theorem, ctx: ProofContext): void {
  assertProofContext(ctx)
  if (thm.lhs.boundary.length !== thm.rhs.boundary.length) {
    throw new ProofError(
      `theorem '${thm.name}': boundary arity mismatch (lhs ${thm.lhs.boundary.length}, rhs ${thm.rhs.boundary.length})`,
    )
  }
  const backActions = thm.backActions ?? []
  const carry = (initial: readonly WireId[], actions: readonly ProofAction[]) => {
    let boundary = initial
    return {
      afterStep(_d: Diagram, actionIndex: number, stepIndex: number, receipt: StepReceipt): void {
        const step = actions[actionIndex]!.steps[stepIndex]!
        const rebound = reboundWires(step).find((wire) => boundary.includes(wire))
        if (rebound !== undefined) {
          throw new ProofError(
            `theorem '${thm.name}': step ${stepIndex} (${step.rule}) of action ${actionIndex} `
            + `rebinds boundary wire '${rebound}'; a boundary wire is not a local binder`,
          )
        }
        const mapped = transportBoundary(receipt.interface, boundary)
        if (mapped === undefined) {
          const missing = boundary.find((wire) => receipt.interface.image(wire) === undefined)
          throw new ProofError(
            `theorem '${thm.name}': boundary wire '${missing ?? '<unknown>'}' has no semantic image (action ${actionIndex}, step ${stepIndex})`,
          )
        }
        boundary = mapped
      },
      boundary: () => boundary,
    }
  }
  const fwdInterface = carry(thm.lhs.boundary, thm.actions)
  const fwd = replayActions(pinnedForReplay(thm.lhs), thm.actions, ctx, fwdInterface.afterStep)
  // the backward half replays from the RHS with flipped gates — each step
  // asserts its result entails its input, so the chain runs rhs-ward
  const bwdInterface = carry(thm.rhs.boundary, backActions)
  const bwd = replayActions(pinnedForReplay(thm.rhs), backActions, ctx, bwdInterface.afterStep, 'backward')
  if (!sameDiagram(fwd, bwd, fwdInterface.boundary(), bwdInterface.boundary())) {
    const detail = process.env.THEOREM_DEBUG
      ? `\n-- forward:\n${JSON.stringify({ diagram: diagramToJson(fwd), boundary: fwdInterface.boundary() })}`
        + `\n-- stated/backward:\n${JSON.stringify({ diagram: diagramToJson(bwd), boundary: bwdInterface.boundary() })}`
      : ''
    throw new ProofError((backActions.length === 0
      ? `theorem '${thm.name}': the proof does not arrive at the stated right-hand side`
      : `theorem '${thm.name}': the forward and backward halves do not meet`) + detail)
  }
}

/**
 * The derived-rule application (justify once, apply natively — the stored
 * proof is NEVER inlined): rewrite a verified occurrence of one theorem side
 * into the other. Forward (lhs→rhs) is sound at POSITIVE regions, reverse
 * (rhs→lhs) at NEGATIVE regions, by monotonicity. The occurrence is checked
 * exactly — extract, reorder its boundary by args, and compare pinned
 * fingerprints through the ordinary exact-occurrence matcher.
 */
export function applyTheorem(
  d: Diagram,
  ctx: ProofContext,
  name: string,
  at: TheoremApplication,
  direction: 'forward' | 'reverse',
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  assertProofContext(ctx)
  const thm = ctx.theorems.get(name)
  if (thm === undefined) throw new ProofError(`unknown theorem '${name}'`)
  return applyVerifiedTheorem(d, thm, at, direction, orientation, reservation)
}

function applyVerifiedTheorem(
  d: Diagram,
  thm: Theorem,
  at: TheoremApplication,
  direction: 'forward' | 'reverse',
  orientation: 'forward' | 'backward' = 'forward',
  reservation?: IdReservation,
): Diagram {
  const from = direction === 'forward' ? thm.lhs : thm.rhs
  const to = direction === 'forward' ? thm.rhs : thm.lhs
  // direction ties to sign; the backward orientation (reasoning from a goal)
  // flips the gate — reverse-citing on a goal's positive region is the
  // forward citation read right-to-left
  const need = (direction === 'forward') === (orientation === 'forward') ? 'positive' : 'negative'
  const have = polarity(d, at.sel.region)
  if (have !== need) {
    throw new RuleError(
      `theorem '${thm.name}' applied ${direction}${orientation === 'backward' ? ' (backward)' : ''} requires a ${need} region; '${at.sel.region}' is ${have}`,
    )
  }
  const { pattern, attachments } = extractSubgraph(d, at.sel)
  if (at.args.length !== from.boundary.length) {
    throw new RuleError(
      `theorem '${thm.name}' has ${from.boundary.length} boundary positions but ${at.args.length} arguments were given`,
    )
  }
  for (const attachment of attachments) {
    if (!at.args.includes(attachment)) {
      throw new RuleError(`attachment wire '${attachment}' is not used by any theorem argument position`)
    }
  }
  /*
   * Build the complete candidate boundary seen at the application site.
   *
   * A theorem-side boundary wire with endpoints is incident to selected
   * content, so its host argument must be one of extraction's touching
   * attachments. An endpoint-free theorem-side boundary wire is instead an
   * ambient capture: the ordered theorem argument supplies its host identity
   * directly even though the empty wire cannot appear in extraction.
   *
   * Reuse one candidate stub per host wire, including an extracted stub when
   * the same host wire is also a touching attachment. This makes sameDiagram
   * check the actual alias relation at the call site: distinct theorem
   * identities cannot be diagonalized onto one host wire, and a repeated
   * theorem identity cannot be split across different host wires.
   */
  const candidateWires = { ...pattern.diagram.wires }
  const candidateNodes = { ...pattern.diagram.nodes }
  const takenCandidateWires = new Set(Object.keys(candidateWires))
  const takenCandidateNodes = new Set(Object.keys(candidateNodes))
  const detachedCaptureStubs = new Map<WireId, WireId>()
  const candidateBoundary = from.boundary.map((sourceBoundary, index) => {
    const argument = at.args[index]!
    const hostWire = d.wires[argument]
    if (hostWire === undefined) {
      throw new RuleError(`argument wire '${argument}' does not exist`)
    }
    const attachmentIndex = attachments.indexOf(argument)
    if (attachmentIndex !== -1) return pattern.boundary[attachmentIndex]!

    const sourceWire = from.diagram.wires[sourceBoundary]!
    const sourcePins = sourceWire.endpoints.filter((endpoint) => {
      const node = from.diagram.nodes[endpoint.node]
      return node !== undefined && node.kind === 'identity' && node.arity === 1
    })
    if (sourcePins.length !== sourceWire.endpoints.length) {
      throw new RuleError(`argument wire '${argument}' is not an attachment wire of the selection`)
    }
    const existing = detachedCaptureStubs.get(argument)
    if (existing !== undefined) return existing

    // Mirror the detached formal's shape exactly — its pins included — so
    // the sameDiagram comparison sees the same structure.
    const stub = freshId(takenCandidateWires, `capture${index}`)
    takenCandidateWires.add(stub)
    const endpoints = sourcePins.map((sourcePin) => {
      const node = freshId(takenCandidateNodes, `capturepin${index}`)
      takenCandidateNodes.add(node)
      const sourceNode = from.diagram.nodes[sourcePin.node]!
      if (sourceNode.kind !== 'identity') {
        throw new RuleError(`capture pin '${sourcePin.node}' is not an identity node`)
      }
      candidateNodes[node] = {
        kind: 'identity',
        region: pattern.diagram.root,
        sig: sourceNode.sig,
        arity: 1,
      }
      return { node, port: { kind: 'identity', index: 0 } as const }
    })
    candidateWires[stub] = { sig: hostWire.sig, endpoints }
    detachedCaptureStubs.set(argument, stub)
    return stub
  })
  const candidate = mkDiagramWithBoundary(
    {
      ...pattern.diagram,
      nodes: candidateNodes,
      wires: candidateWires,
    },
    candidateBoundary,
  )
  if (!sameDiagram(candidate.diagram, from.diagram, candidate.boundary, from.boundary)) {
    throw new RuleError(
      `the selection is not an occurrence of theorem '${thm.name}' ${direction === 'forward' ? 'left' : 'right'}-hand side`,
    )
  }
  // Splice BEFORE removing: fresh ids are then minted against the FULL
  // pre-removal id set, so this step can never resurrect an id it destroys
  // (checkTheorem's per-step boundary checks rely on exactly that). The two
  // phases commute — the splice only adds content and extends the attachment
  // wires, none of which the removal selection touches.
  const spliced = spliceSubgraphMapped(d, at.sel.region, to, at.args, { reserved: reservation }).diagram
  return removeSubgraph(spliced, at.sel)
}
