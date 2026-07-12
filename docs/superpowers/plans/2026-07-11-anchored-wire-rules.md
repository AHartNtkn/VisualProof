# Anchored Wire Rules Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace `endpointTransport` with availability-aware anchored wire split and contraction rules without losing shielded local-equality derivations.

**Architecture:** A focused `anchored-wire.ts` module owns closed-witness availability and both rule appliers. `ProofStep`, strict JSON, and composition carry only authoritative host operands; fresh duplicate IDs remain applier-derived. The Frege derivation migrates to split at the guard bubble followed by contraction into the unshielded root witness, and the old primitive is deleted everywhere.

**Tech Stack:** TypeScript 5.5, Vitest 2, immutable diagram kernel, strict JSON proof codec, canonical diagram explorer, generated Frege theory JSON.

## Global Constraints

- `anchorAvailability` stops before crossing the first cut outward and never leaves the witness output wire's scope; bubbles are transparent.
- `anchoredWireSplit` places both the fresh wire scope and duplicate closed witness exactly at the explicit `target` region.
- `anchoredWireContract` requires the redundant witness to be unshielded to its wire scope and every moved endpoint to lie inside the survivor witness's availability.
- Both rules are polarity-blind and replay certificates through existing kernel machinery.
- `endpointTransport` is deleted without an alias, legacy JSON reader, wrapper, or fallback.
- Application interaction integration is out of scope until target-region authorship is visually approved.

---

## File Structure

- Create `src/kernel/rules/anchored-wire.ts`: availability computation and both immutable rule transformations.
- Create `tests/kernel/rules/anchored-wire.test.ts`: semantic, refusal, counterexample, round-trip, and transport-factorization tests.
- Modify `src/kernel/rules/index.ts`: export the new authority and remove transport.
- Modify `src/kernel/proof/step.ts`: replace the primitive step variant and dispatch.
- Modify `src/kernel/proof/json.ts`: strict serialization/parsing for both new variants; remove transport.
- Modify `src/kernel/proof/compose.ts`: remap wire/node/endpoint/region operands; remove transport.
- Modify `tests/kernel/proof/json.test.ts`: exhaustive kind coverage and malformed-field tests.
- Modify `tests/kernel/proof/compose.test.ts`: non-identity operand remapping tests.
- Delete `src/kernel/rules/transport.ts` and `tests/kernel/rules/transport.test.ts` after their capability assertions are migrated.
- Modify `src/theories/frege.ts`: shorter `zeroIsNat` derivation.
- Modify `tests/theories/frege.test.ts`: pin the new steps, shorter trace, internal base scope, and absence of obsolete steps.
- Regenerate `examples/frege.json` from `src/theories/frege.ts`.

---

### Task 1: Witness Availability Authority

**Files:**
- Create: `src/kernel/rules/anchored-wire.ts`
- Create: `tests/kernel/rules/anchored-wire.test.ts`

**Interfaces:**
- Consumes: `termNodeAt(d, witness)`, `wireAt(d, witness, { kind: 'output' })`, `freePorts(term)`, `cutDepth(d, region)`, and diagram parent links.
- Produces: `anchorAvailability(d: Diagram, witness: NodeId): RegionId`.

- [ ] **Step 1: Write the failing availability tests**

Create fixtures that place a closed witness on a root-scoped wire through nested bubbles and cuts. Add these exact assertions:

```ts
describe('anchorAvailability', () => {
  it('crosses bubbles to the witness wire scope', () => {
    const b = new DiagramBuilder()
    const outer = b.bubble(b.root, 1)
    const inner = b.bubble(outer, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(b.root)
  })

  it('stops inside the first enclosing cut', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const bubble = b.bubble(cut, 1)
    const witness = b.termNode(bubble, CLOSED)
    b.wire(b.root, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(cut)
  })

  it('never walks above the output wire scope', () => {
    const b = new DiagramBuilder()
    const scope = b.bubble(b.root, 1)
    const inner = b.bubble(scope, 1)
    const witness = b.termNode(inner, CLOSED)
    b.wire(scope, [{ node: witness, port: { kind: 'output' } }])
    expect(anchorAvailability(b.build(), witness)).toBe(scope)
  })

  it('refuses open and non-term witnesses', () => {
    const b = new DiagramBuilder()
    const open = b.termNode(b.root, port('x'))
    const ref = b.ref(b.root, 'R', 0)
    b.wire(b.root, [{ node: open, port: { kind: 'output' } }])
    expect(() => anchorAvailability(b.build(), open)).toThrow(/closed witness/)
    expect(() => anchorAvailability(b.build(), ref)).toThrow(/term nodes/)
  })
})
```

- [ ] **Step 2: Run the focused test and verify RED**

Run: `npx vitest run tests/kernel/rules/anchored-wire.test.ts`

Expected: FAIL because `anchored-wire.ts` and `anchorAvailability` do not exist.

- [ ] **Step 3: Implement the minimal availability walk**

Create `src/kernel/rules/anchored-wire.ts` with:

```ts
import { freePorts } from '../term/term'
import type { Diagram, NodeId, RegionId } from '../diagram/diagram'
import { cutDepth } from '../diagram/regions'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

export function anchorAvailability(d: Diagram, witnessId: NodeId): RegionId {
  const witness = termNodeAt(d, witnessId)
  const free = freePorts(witness.term)
  if (free.length > 0) {
    throw new RuleError(
      `anchored wire rules require a closed witness; '${witnessId}' has free ports [${free.map((name) => `'${name}'`).join(', ')}]`,
    )
  }
  const wire = wireAt(d, witnessId, { kind: 'output' })
  const scope = d.wires[wire]!.scope
  const depth = cutDepth(d, witness.region)
  let available = witness.region
  while (available !== scope) {
    const region = d.regions[available]!
    if (region.kind === 'sheet') break
    if (cutDepth(d, region.parent) !== depth) break
    available = region.parent
  }
  return available
}
```

- [ ] **Step 4: Run the focused test and verify GREEN**

Run: `npx vitest run tests/kernel/rules/anchored-wire.test.ts`

Expected: PASS for the availability group.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/anchored-wire.ts tests/kernel/rules/anchored-wire.test.ts
git commit -m "feat: define closed witness availability"
```

---

### Task 2: Anchored Split and Contraction Rules

**Files:**
- Modify: `src/kernel/rules/anchored-wire.ts`
- Modify: `tests/kernel/rules/anchored-wire.test.ts`
- Modify: `src/kernel/rules/index.ts`

**Interfaces:**
- Consumes: `anchorAvailability`, `checkConversion`, `freshId`, `isAncestorOrEqual`, `cutDepth`, `mkDiagram`, `portKey`.
- Produces:
  - `applyAnchoredWireSplit(d: Diagram, wire: WireId, witness: NodeId, endpoints: readonly Endpoint[], target: RegionId): Diagram`
  - `applyAnchoredWireContract(d: Diagram, redundant: NodeId, survivor: NodeId, certificate: ConversionCertificate): Diagram`

- [ ] **Step 1: Add failing positive and inverse tests**

Add helpers `sameEndpoint`, `outputWire`, and fixtures for an internal witness, a shielded root-scoped witness, and endpoints under nested cuts. Add these exact behavioral tests:

```ts
it('splits an arbitrary endpoint group onto a target-scoped duplicate anchor', () => {
  const s = splitFixture()
  const out = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first, s.second], s.target)
  const duplicate = Object.entries(out.nodes).find(([id, node]) =>
    id !== s.witness && node.kind === 'term' && node.region === s.target && termEq(node.term, CLOSED))![0]
  const fresh = outputWire(out, duplicate)
  expect(out.wires[fresh]!.scope).toBe(s.target)
  expect(out.wires[fresh]!.endpoints).toEqual(expect.arrayContaining([
    { node: duplicate, port: { kind: 'output' } }, s.first, s.second,
  ]))
  expect(out.wires[s.wire]!.endpoints).not.toEqual(expect.arrayContaining([s.first, s.second]))
})

it('contracts an unshielded redundant anchor into a locally available survivor', () => {
  const s = contractFixture()
  const out = applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate)
  expect(out.nodes[s.redundant]).toBeUndefined()
  expect(out.wires[s.redundantWire]).toBeUndefined()
  expect(out.wires[s.survivorWire]!.scope).toBe(s.survivorScope)
  expect(out.wires[s.survivorWire]!.endpoints).toContainEqual(s.moved)
})

it('split then contract returns the exact canonical starting diagram', () => {
  const s = splitFixture()
  const split = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first], s.target)
  const duplicate = newClosedWitness(split, s.d, s.target)
  const back = applyAnchoredWireContract(split, duplicate, s.witness, EMPTY_CERT)
  expect(exploreForm(back)).toBe(exploreForm(s.d))
})
```

- [ ] **Step 2: Add failing hard-wall and malformed-input tests**

Add named tests using the positive fixtures from Step 1 plus this shielded
counterexample fixture:

```ts
function shieldedFixture() {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const witness = b.termNode(cut, CLOSED)
  const rootConsumer = b.termNode(b.root, port('s0'))
  const insideConsumer = b.termNode(cut, port('s0'))
  const wire = b.wire(b.root, [
    { node: witness, port: { kind: 'output' } },
    { node: rootConsumer, port: { kind: 'freeVar', name: 's0' } },
    { node: insideConsumer, port: { kind: 'freeVar', name: 's0' } },
  ])
  return {
    d: b.build(), cut, witness, rootConsumer, insideConsumer, wire,
    rootEndpoint: { node: rootConsumer, port: { kind: 'freeVar' as const, name: 's0' } },
    insideEndpoint: { node: insideConsumer, port: { kind: 'freeVar' as const, name: 's0' } },
  }
}

it('refuses a split target outside witness availability', () => {
  const s = shieldedFixture()
  expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.rootEndpoint], s.d.root))
    .toThrow(/outside witness .* availability/)
})

it('refuses a moved endpoint whose node is outside the split target', () => {
  const s = shieldedFixture()
  expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.rootEndpoint], s.cut))
    .toThrow(/endpoint .* outside target/)
})

it('refuses moving the selected witness output', () => {
  const s = splitFixture()
  expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [
    { node: s.witness, port: { kind: 'output' } },
  ], s.target)).toThrow(/cannot move witness .* output/)
})

it('refuses duplicate and unknown split endpoints', () => {
  const s = splitFixture()
  expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first, s.first], s.target))
    .toThrow(/selected more than once/)
  expect(() => applyAnchoredWireSplit(s.d, s.wire, s.witness, [
    { node: s.first.node, port: { kind: 'freeVar', name: 'missing' } },
  ], s.target)).toThrow(/is not on wire/)
})

it('refuses contraction of a cut-shielded redundant witness', () => {
  const s = contractFixture({ shieldRedundant: true })
  expect(() => applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate))
    .toThrow(/redundant witness .* shielded/)
})

it('refuses contraction when one moved endpoint lies just outside survivor availability', () => {
  const s = contractFixture({ survivorBehindCut: true, movedAtRoot: true })
  expect(() => applyAnchoredWireContract(s.d, s.redundant, s.survivor, s.certificate))
    .toThrow(/outside survivor .* availability/)
})

it('refuses open witnesses and a rejected conversion certificate', () => {
  const open = contractFixture({ redundantTerm: port('x') })
  expect(() => applyAnchoredWireContract(open.d, open.redundant, open.survivor, open.certificate))
    .toThrow(/closed witness/)
  const unequal = contractFixture({ survivorTerm: OTHER_CLOSED, certificate: EMPTY_CERT })
  expect(() => applyAnchoredWireContract(unequal.d, unequal.redundant, unequal.survivor, unequal.certificate))
    .toThrow(/certificate rejected/)
})

it('refuses identical witnesses and witnesses already on one wire', () => {
  const s = contractFixture()
  expect(() => applyAnchoredWireContract(s.d, s.redundant, s.redundant, s.certificate))
    .toThrow(/two distinct witnesses/)
  const shared = sharedAnchorFixture()
  expect(() => applyAnchoredWireContract(shared.d, shared.a, shared.b, EMPTY_CERT))
    .toThrow(/already share wire/)
})

it('is polarity-blind inside positive and negative regions', () => {
  for (const inCut of [false, true]) {
    const s = splitFixture({ inCut })
    const split = applyAnchoredWireSplit(s.d, s.wire, s.witness, [s.first], s.target)
    const duplicate = newClosedWitness(split, s.d, s.target)
    expect(() => applyAnchoredWireContract(split, duplicate, s.witness, EMPTY_CERT)).not.toThrow()
  }
})
```

Each test must assert the semantic refusal phrase (`outside ... availability`, `redundant witness ... shielded`, `closed witness`, or `certificate rejected`) rather than only `RuleError`.

- [ ] **Step 3: Run the rule tests and verify RED**

Run: `npx vitest run tests/kernel/rules/anchored-wire.test.ts`

Expected: FAIL because both appliers are missing.

- [ ] **Step 4: Implement anchored split**

Add the complete immutable transformation:

```ts
export function applyAnchoredWireSplit(
  d: Diagram,
  wireId: WireId,
  witnessId: NodeId,
  endpoints: readonly Endpoint[],
  target: RegionId,
): Diagram {
  const witness = termNodeAt(d, witnessId)
  const source = d.wires[wireId]
  if (source === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (wireAt(d, witnessId, { kind: 'output' }) !== wireId) {
    throw new RuleError(`witness '${witnessId}' does not anchor wire '${wireId}'`)
  }
  const available = anchorAvailability(d, witnessId)
  if (!isAncestorOrEqual(d, available, target)) {
    throw new RuleError(`split target '${target}' lies outside witness '${witnessId}' availability '${available}'`)
  }
  const seen = new Set<string>()
  const chosen = (candidate: Endpoint): boolean => endpoints.some((endpoint) => sameEndpoint(endpoint, candidate))
  for (const endpoint of endpoints) {
    const key = `${endpoint.node}/${portKey(endpoint.port)}`
    if (seen.has(key)) throw new RuleError(`split endpoint '${key}' is selected more than once`)
    seen.add(key)
    if (!source.endpoints.some((candidate) => sameEndpoint(candidate, endpoint))) {
      throw new RuleError(`split endpoint '${key}' is not on wire '${wireId}'`)
    }
    if (endpoint.node === witnessId && endpoint.port.kind === 'output') {
      throw new RuleError(`split cannot move witness '${witnessId}'s output`)
    }
    if (!isAncestorOrEqual(d, target, d.nodes[endpoint.node]!.region)) {
      throw new RuleError(`split endpoint '${key}' lies outside target '${target}'`)
    }
  }
  const duplicate = freshId(new Set(Object.keys(d.nodes)), `${witnessId}_split`)
  const freshWire = freshId(new Set(Object.keys(d.wires)), `${wireId}_split`)
  return mkDiagram({
    root: d.root,
    regions: { ...d.regions },
    nodes: { ...d.nodes, [duplicate]: { kind: 'term', region: target, term: witness.term } },
    wires: {
      ...d.wires,
      [wireId]: { scope: source.scope, endpoints: source.endpoints.filter((endpoint) => !chosen(endpoint)) },
      [freshWire]: {
        scope: target,
        endpoints: [{ node: duplicate, port: { kind: 'output' } }, ...endpoints],
      },
    },
  })
}
```

Define `sameEndpoint` once in the module with node identity plus `portKey` equality.

- [ ] **Step 5: Implement anchored contraction**

Add:

```ts
export function applyAnchoredWireContract(
  d: Diagram,
  redundantId: NodeId,
  survivorId: NodeId,
  certificate: ConversionCertificate,
): Diagram {
  if (redundantId === survivorId) throw new RuleError(`anchored contraction needs two distinct witnesses`)
  const redundant = termNodeAt(d, redundantId)
  const survivor = termNodeAt(d, survivorId)
  requireClosed(redundantId, redundant.term)
  requireClosed(survivorId, survivor.term)
  const checked = checkConversion(redundant.term, survivor.term, certificate)
  if (!checked.ok) throw new RuleError(`anchored contraction certificate rejected: ${checked.reason}`)
  const dropId = wireAt(d, redundantId, { kind: 'output' })
  const keepId = wireAt(d, survivorId, { kind: 'output' })
  if (dropId === keepId) throw new RuleError(`anchored witnesses already share wire '${dropId}'`)
  if (cutDepth(d, d.wires[dropId]!.scope) !== cutDepth(d, redundant.region)) {
    throw new RuleError(`redundant witness '${redundantId}' is shielded from wire '${dropId}'s scope`)
  }
  const available = anchorAvailability(d, survivorId)
  const moved = d.wires[dropId]!.endpoints.filter((endpoint) =>
    !(endpoint.node === redundantId && endpoint.port.kind === 'output'))
  for (const endpoint of moved) {
    if (!isAncestorOrEqual(d, available, d.nodes[endpoint.node]!.region)) {
      throw new RuleError(
        `endpoint '${endpoint.node}/${portKey(endpoint.port)}' lies outside survivor '${survivorId}' availability '${available}'`,
      )
    }
  }
  const nodes = { ...d.nodes }
  delete nodes[redundantId]
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (id === dropId) continue
    wires[id] = id === keepId
      ? { scope: wire.scope, endpoints: [...wire.endpoints, ...moved] }
      : wire
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
```

Factor `requireClosed` so availability and contraction share the exact closedness message.

- [ ] **Step 6: Export the new authority and verify GREEN**

Replace the transport export in `src/kernel/rules/index.ts` with:

```ts
export {
  anchorAvailability,
  applyAnchoredWireSplit,
  applyAnchoredWireContract,
} from './anchored-wire'
```

Run: `npx vitest run tests/kernel/rules/anchored-wire.test.ts`

Expected: all anchored-wire tests PASS.

- [ ] **Step 7: Commit**

```bash
git add src/kernel/rules/anchored-wire.ts src/kernel/rules/index.ts tests/kernel/rules/anchored-wire.test.ts
git commit -m "feat: add availability-aware anchored wire rules"
```

---

### Task 3: Proof-Step, JSON, and Composition Integration

**Files:**
- Modify: `src/kernel/proof/step.ts`
- Modify: `src/kernel/proof/json.ts`
- Modify: `src/kernel/proof/compose.ts`
- Modify: `tests/kernel/proof/json.test.ts`
- Modify: `tests/kernel/proof/compose.test.ts`

**Interfaces:**
- Produces the two exact `ProofStep` variants from the design spec.
- JSON fields are required and strict: split uses `rule,wire,witness,endpoints,target`; contract uses `rule,redundant,survivor,certificate`.
- Composition remaps every host ID and leaves certificates unchanged.

- [ ] **Step 1: Write failing JSON coverage and strictness tests**

Replace the exhaustive endpoint transport sample with:

```ts
{ rule: 'anchoredWireSplit', wire: 'w0', witness: 'n0', endpoints: [
  { node: 'n1', port: { kind: 'freeVar', name: 's0' } },
], target: 'r1' },
{ rule: 'anchoredWireContract', redundant: 'n0', survivor: 'n1', certificate },
```

Add malformed tests that remove each required split field, remove the contract certificate, and add an unknown field. Expected failures name the missing array/string/certificate or unknown field.

- [ ] **Step 2: Write failing composition remapping tests**

```ts
it('remaps every anchored split host operand', () => {
  expect(mapStepIds({
    rule: 'anchoredWireSplit', wire: 'w0', witness: 'n0',
    endpoints: [{ node: 'n1', port: { kind: 'arg', index: 0 } }], target: 'r0',
  }, iso)).toEqual({
    rule: 'anchoredWireSplit', wire: 'W0', witness: 'N0',
    endpoints: [{ node: 'N1', port: { kind: 'arg', index: 0 } }], target: 'R0',
  })
})

it('remaps both anchored contraction witnesses', () => {
  expect(mapStepIds({
    rule: 'anchoredWireContract', redundant: 'n0', survivor: 'n1', certificate,
  }, iso)).toEqual({
    rule: 'anchoredWireContract', redundant: 'N0', survivor: 'N1', certificate,
  })
})
```

Each test also passes one missing ID and asserts `composition cannot map ...`.

- [ ] **Step 3: Run focused proof tests and verify RED**

Run: `npx vitest run tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts`

Expected: type/compile failures because the new variants are absent.

- [ ] **Step 4: Replace ProofStep variants and dispatch**

In `src/kernel/proof/step.ts`, delete `endpointTransport`, import the two new appliers, and add:

```ts
| { readonly rule: 'anchoredWireSplit'; readonly wire: WireId; readonly witness: NodeId; readonly endpoints: readonly Endpoint[]; readonly target: RegionId }
| { readonly rule: 'anchoredWireContract'; readonly redundant: NodeId; readonly survivor: NodeId; readonly certificate: ConversionCertificate }
```

Dispatch with:

```ts
case 'anchoredWireSplit':
  return applyAnchoredWireSplit(d, step.wire, step.witness, step.endpoints, step.target)
case 'anchoredWireContract':
  return applyAnchoredWireContract(d, step.redundant, step.survivor, step.certificate)
```

Orientation is intentionally not forwarded.

- [ ] **Step 5: Replace strict JSON cases**

Serialize with:

```ts
case 'anchoredWireSplit':
  return { rule: s.rule, wire: s.wire, witness: s.witness, endpoints: s.endpoints.map(endpointToJson), target: s.target }
case 'anchoredWireContract':
  return { rule: s.rule, redundant: s.redundant, survivor: s.survivor, certificate: certToJson(s.certificate) }
```

Parse with required arrays and exact keys:

```ts
case 'anchoredWireSplit': {
  assertOnlyKeys(j, ['rule', 'wire', 'witness', 'endpoints', 'target'], 'anchoredWireSplit step')
  if (!Array.isArray(j.endpoints)) fail('endpoints must be an array')
  return {
    rule, wire: str(j.wire, 'wire'), witness: str(j.witness, 'witness'),
    endpoints: j.endpoints.map((endpoint, index) => endpointFromJson(endpoint, `endpoints[${index}]`)),
    target: str(j.target, 'target'),
  }
}
case 'anchoredWireContract':
  assertOnlyKeys(j, ['rule', 'redundant', 'survivor', 'certificate'], 'anchoredWireContract step')
  return {
    rule, redundant: str(j.redundant, 'redundant'), survivor: str(j.survivor, 'survivor'),
    certificate: certFromJson(j.certificate, 'certificate'),
  }
```

- [ ] **Step 6: Replace composition cases**

```ts
case 'anchoredWireSplit':
  return {
    ...step,
    wire: mapId(iso.wires, step.wire, 'wire'),
    witness: mapId(iso.nodes, step.witness, 'node'),
    endpoints: step.endpoints.map((endpoint) => mapEndpoint(iso, endpoint)),
    target: mapId(iso.regions, step.target, 'region'),
  }
case 'anchoredWireContract':
  return {
    ...step,
    redundant: mapId(iso.nodes, step.redundant, 'node'),
    survivor: mapId(iso.nodes, step.survivor, 'node'),
  }
```

- [ ] **Step 7: Run focused proof tests and verify GREEN**

Run: `npx vitest run tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts tests/kernel/proof/step.test.ts`

Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add src/kernel/proof/step.ts src/kernel/proof/json.ts src/kernel/proof/compose.ts tests/kernel/proof/json.test.ts tests/kernel/proof/compose.test.ts
git commit -m "feat: integrate anchored wire proof steps"
```

---

### Task 4: Preserve Transport Capability and Remove the Primitive

**Files:**
- Modify: `tests/kernel/rules/anchored-wire.test.ts`
- Delete: `tests/kernel/rules/transport.test.ts`
- Delete: `src/kernel/rules/transport.ts`

**Interfaces:**
- The new pair must reproduce `applyEndpointTransport` post-states without importing or calling it.
- Capability tests use canonical forms and explicit scope/identity assertions.

- [ ] **Step 1: Port the old capability tests before deleting transport**

Add a helper that applies split, discovers the fresh duplicate by before/after node difference, and contracts it:

```ts
function redistribute(
  d: Diagram,
  sourceWitness: NodeId,
  targetWitness: NodeId,
  endpoints: readonly Endpoint[],
  target: RegionId,
  certificate = EMPTY_CERT,
): Diagram {
  const wire = outputWire(d, sourceWitness)
  const split = applyAnchoredWireSplit(d, wire, sourceWitness, endpoints, target)
  const duplicate = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
  return applyAnchoredWireContract(split, duplicate, targetWitness, certificate)
}
```

Port positive and negative polarity, real β conversion, unchanged nodes/regions/wire IDs/scopes, consumer-inside-evidence, sibling/outside refusal, open evidence, rejected certificate, and one/many endpoint cases. Add the shielded case:

```ts
it('derives shielded local redistribution with root-scoped original wires', () => {
  const s = shieldedTransportFixture()
  const out = redistribute(s.d, s.a, s.b, [s.endpoint], s.evidenceRegion, s.certificate)
  expect(out.wires[s.aWire]!.scope).toBe(s.d.root)
  expect(out.wires[s.bWire]!.scope).toBe(s.d.root)
  expect(out.wires[s.aWire]!.endpoints).not.toContainEqual(s.endpoint)
  expect(out.wires[s.bWire]!.endpoints).toContainEqual(s.endpoint)
})
```

- [ ] **Step 2: Run the migrated capability tests while transport still exists**

Run: `npx vitest run tests/kernel/rules/anchored-wire.test.ts tests/kernel/rules/transport.test.ts`

Expected: PASS, demonstrating parity before deletion.

- [ ] **Step 3: Delete the displaced rule and old test**

Delete `src/kernel/rules/transport.ts` and `tests/kernel/rules/transport.test.ts`. Remove the transport export already replaced in Task 2.

- [ ] **Step 4: Run kernel and architecture searches**

Run:

```bash
npx vitest run tests/kernel/rules/anchored-wire.test.ts tests/kernel/proof
rg -n "endpointTransport|applyEndpointTransport" src/kernel tests/kernel
```

Expected: tests PASS; `rg` returns no matches.

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/transport.ts tests/kernel/rules/transport.test.ts tests/kernel/rules/anchored-wire.test.ts
git commit -m "refactor: replace endpoint transport with anchored wires"
```

---

### Task 5: Migrate `zeroIsNat` and Generated Theory

**Files:**
- Modify: `src/theories/frege.ts`
- Modify: `tests/theories/frege.test.ts`
- Modify: `examples/frege.json`

**Interfaces:**
- `DerivationCursor.push` consumes ordinary new `ProofStep` values.
- The duplicate witness is found from the diagram delta after split; no fresh ID is predicted.

- [ ] **Step 1: Add failing theorem trace and scope assertions**

Extend the existing `zeroIsNat` test:

```ts
const rules = t.steps.map((step) => step.rule)
expect(rules).toContain('anchoredWireSplit')
expect(rules).toContain('anchoredWireContract')
expect(rules).not.toContain('endpointTransport')
expect(rules.filter((rule) => rule === 'iteration')).toHaveLength(1)
expect(rules).not.toContain('deiteration')
expect(t.steps).toHaveLength(11)
```

Add a replay observer or focused derivation helper that captures the state after split and asserts the original `w0` remains scoped at the guard bubble with both internal ZERO and base predicate endpoints. Pin the expected `zeroIsNat` step count to 11: the copy iteration and deiteration disappear while one transport step becomes two anchored steps, for a net reduction of one.

- [ ] **Step 2: Run the theorem test and verify RED**

Run: `npx vitest run tests/theories/frege.test.ts`

Expected: FAIL because `zeroIsNat` still contains `endpointTransport` and the copy iteration/deiteration pair.

- [ ] **Step 3: Rewrite the derivation**

After unfolding `zrefIn` and obtaining `z0`, replace the iterated copy, transport, and deiteration with:

```ts
snap = e.cur
e.push('split conclusion from internal zero', {
  rule: 'anchoredWireSplit',
  wire: w0,
  witness: z0,
  endpoints: [{ node: a3, port: { kind: 'arg', index: 0 } }],
  target: rB,
})
const localZero = e.newNodeIn(rB, snap, ZEROp)
e.push('contract conclusion onto external zero', {
  rule: 'anchoredWireContract',
  redundant: localZero,
  survivor: zExt,
  certificate: idCert,
})
```

Keep the internal/external zero refolds and final nat fold unchanged. Update the surrounding comments to describe availability and retained scope rather than transport.

- [ ] **Step 4: Run theorem and battery tests**

Run:

```bash
npx vitest run tests/theories/frege.test.ts tests/theories/battery.test.ts tests/kernel/rules/reldef-fresh.test.ts
```

Expected: PASS; every theorem verifies through serialization.

- [ ] **Step 5: Regenerate authoritative examples**

Run: `npm run emit:theories`

Expected: `examples/frege.json` changes from one transport step plus copy/deiteration to anchored split/contract; `examples/lambda.json` is unchanged.

Run:

```bash
rg -n "endpointTransport" src tests examples
npx vitest run tests/scripts/emit-theories.test.ts
```

Expected: no search matches; generator test PASS.

- [ ] **Step 6: Commit**

```bash
git add src/theories/frege.ts tests/theories/frege.test.ts examples/frege.json
git commit -m "refactor: derive zero is nat with anchored wires"
```

---

### Task 6: Full Verification and Conformance

**Files:**
- Modify: `docs/superpowers/specs/2026-07-11-anchored-wire-rules-design.md` only to set implemented status after all checks pass.
- Modify: `/tmp/visualproof-foundation-20260711-proof-move-authoring.md` by appending `<conformance>` without changing prior sections.

**Interfaces:**
- No new code interfaces.

- [ ] **Step 1: Run formatting-neutral static checks**

Run:

```bash
npm run typecheck
git diff --check
```

Expected: both exit 0.

- [ ] **Step 2: Run the full unit/theory suite**

Run: `npm test`

Expected: every Vitest test passes with no unhandled errors.

- [ ] **Step 3: Verify generated artifacts are current**

Run:

```bash
npm run emit:theories
git diff --exit-code -- examples/frege.json examples/lambda.json
```

Expected: regeneration produces no further diff.

- [ ] **Step 4: Prove the displaced model is absent**

Run:

```bash
rg -n "endpointTransport|applyEndpointTransport" src tests examples
```

Expected: no matches. Historical plan records may retain the old name; production, tests, and generated examples may not.

- [ ] **Step 5: Update design status and foundation conformance**

Set the design status to `Implemented and validated` with the implementation commit IDs. Append a `<conformance>` section recording rule ownership, deleted structures, migrated proof surfaces, exact commands run, and absence-search output.

- [ ] **Step 6: Commit documentation closure**

```bash
git add docs/superpowers/specs/2026-07-11-anchored-wire-rules-design.md
git commit -m "docs: close anchored wire rule replacement"
```
