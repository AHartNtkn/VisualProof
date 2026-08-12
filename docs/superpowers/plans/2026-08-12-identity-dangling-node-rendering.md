# Shared Small-Node Geometry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give semantic identity nodes and wire-owned existential nodes one small circular geometry implementation with rim anchors, rotation, escape stubs, clamped terminal directions, obstacle participation, and ordinary body painting.

**Architecture:** Kernel identities and scope-homed existential bodies retain their distinct semantic and interaction ownership. In the view layer, both materialize the same circular `NodeGeometry` profile: identity nodes provide one `i:n` rim anchor per incidence, while an existential provides one private rim anchor. All connected small bodies then use the ordinary bind/escape/boundary-condition pipeline and the ordinary anatomy paint pass.

**Tech Stack:** TypeScript, Vitest, Vite view geometry, routed Hobby curves.

## Global Constraints

- Identity nodes use the same circular body, rim-anchor distribution, rotation, escape-stub, and perpendicular terminal constraints as other port-bearing nodes.
- Identity and existential bodies share one small-node radius and scale policy.
- Multi-port identity anchors are evenly spaced around the rim; identity ports receive no visible ordering marker.
- Scope-homed existential bodies remain independently movable wire-owned bodies and retain their wire interaction semantics.
- Routing, full/frozen energy, incremental score, paint, and hit geometry must derive from the same body geometry policy.
- The unrelated `VisualProof/Concrete/Elaboration/SpliceRootCompilation.lean` worktree change is outside task scope and must not be staged or modified.

## Complexity Ledger

- **Essential behavior:** semantic identities remain selectable diagram nodes; dangling existentials remain scope-homed wire terminals; small nodes render as circles and wires meet their rims perpendicularly.
- **Essential state:** kernel diagram/boundary, body poses, wire network topology/junction poses, frame, content scale, and slot shift.
- **Integrity invariants:** every required identity incidence has one distinct rim bind; all small-node anchors lie at one positive radius; terminal BC normals are the rotated radial normals; all obstacle evaluators classify the same bodies.
- **Derived data:** node geometry, local anchors, world anchors, escape points, curve BCs, route spaces, paint shapes, and hit extents.
- **Accidental state/control:** kind branches that replace identity/end anchors with centers or free BCs; separate point-glyph drawing; repeated obstacle-kind predicates.
- **Code volume:** centered identity exceptions, dot/stub paint ownership, and duplicate obstacle classification are one displaced view model and leave no parallel authority after migration.
- **Power leaks:** `Body.kind` must not override a present geometry for anchoring, routing, or painting; obstacle eligibility derives from whether the body has visible geometry.

---

### Task 1: Specify the shared geometry and terminal contract

**Files:**
- Modify: `tests/view/bend.test.ts`
- Modify: `tests/view/engine.test.ts`
- Modify: `tests/view/wires.test.ts`
- Modify: `tests/view/stub-scope.test.ts`
- Modify: `tests/formula/diagram.test.ts`

**Interfaces:**
- Consumes: existing `identityGeometry`, `mkEngine`, `worldBindAnchor`, `escapePoint`, `wireTerminalPoints`, and `wireTerminalBCs`.
- Produces: executable expectations for positive circular geometry, evenly spaced `i:n` anchors, shared identity/end scale, rim terminals, outward escape points, and radial non-null BCs.

- [ ] **Step 1: Replace centered identity geometry assertions**

Assert one full circular arc, a positive arity-independent radius, equal nonzero anchor radii, and successive positive angular turns of `2 * Math.PI / arity`.

```ts
const anchors = Array.from({ length: 5 }, (_, index) => geometry.portAnchors[`i:${index}`]!)
expect(geometry.arcs).toHaveLength(1)
expect(geometry.outerRadius).toBeGreaterThan(0)
expect(anchors.every((anchor) => Math.hypot(anchor.x, anchor.y) > 0)).toBe(true)
```

- [ ] **Step 2: Specify clamped identity and existential terminals**

For a rotated identity and a singleton wire's end body, assert that bind/BC points lie on their visible rims, routed terminal points lie farther outward, and BC normals equal the rotated local radial unit vectors.

```ts
expect(Math.hypot(anchor.x - body.pos.x, anchor.y - body.pos.y)).toBeGreaterThan(0)
expect(Math.hypot(terminal.x - body.pos.x, terminal.y - body.pos.y))
  .toBeGreaterThan(Math.hypot(anchor.x - body.pos.x, anchor.y - body.pos.y))
expect(bc).not.toBeNull()
```

- [ ] **Step 3: Strengthen formula and rim-bind coverage**

Retain one semantic identity for binary/chained equality, assert distinct incidence keys, and prove each local identity anchor is nonzero and reaches its rotated/scaled world position.

```ts
expect(new Set(identityBinds.map((bind) => bind.key)).size).toBe(identityBinds.length)
for (const bind of identityBinds) {
  const local = identityBody.localAnchor.get(bind.key)!
  expect(Math.hypot(local.x, local.y)).toBeGreaterThan(0)
}
```

- [ ] **Step 4: Run RED validation**

Run: `npm test -- tests/view/bend.test.ts tests/view/engine.test.ts tests/view/wires.test.ts tests/view/stub-scope.test.ts tests/formula/diagram.test.ts`

Expected: failures in circular identity geometry, identity/end rim terminals, and shared end-body geometry.

### Task 2: Materialize all small bodies through one geometry policy

**Files:**
- Modify: `src/view/bend.ts`
- Modify: `src/view/engine.ts`
- Modify: `src/view/optimize.ts`

**Interfaces:**
- Consumes: kernel identity arity/ports and wire scope/end classification.
- Produces: `identityGeometry(arity)`, `endGeometry()`, one end-anchor key, geometry-derived obstacle eligibility, and port-bearing end terminals.

- [ ] **Step 1: Add one circular geometry constructor**

Build circular geometry from an ordered list of storage/view keys. `identityGeometry` supplies `i:0...i:n`; `endGeometry` supplies one private end key.

```ts
function circularGeometry(keys: readonly string[]): NodeGeometry {
  return {
    outerRadius: RAIL_R + 0.5,
    arcs: [RAIL_ARC],
    headAnchor: null,
    portAnchors: rimAnchors(keys),
  }
}
```

- [ ] **Step 2: Give identity and end bodies the same small profile**

Set both kinds to the same anatomy scale. Materialize end bodies with `endGeometry()`, one local anchor, and the same derived clearance radius used by identity bodies. Represent the optional wire-owned end as a `WireBind` so its body and key remain explicit.

```ts
export const END_PORT_KEY = 'end'
export type WireView = {
  readonly binds: WireBind[]
  readonly end: WireBind | null
  readonly slots: readonly number[]
  readonly net: WireNet
}
```

- [ ] **Step 3: Remove kind overrides from terminal geometry**

Make `worldBindAnchor`, `portNormal`, `escapePoint`, and `wireTerminalBCs` operate on every keyed bind. Append the optional end bind through those same helpers in `wireTerminalPoints` and `wireTerminalBCs`.

```ts
if (w.end !== null) {
  const body = e.bodies.get(w.end.body)!
  out.push(bindBC(e, body, w.end.key))
}
```

- [ ] **Step 4: Derive rotation eligibility from anchors**

Use `body.localAnchor.size > 0` for optimizer rotation candidates so identity and existential small nodes share the port-bearing rule.

```ts
for (const [id, body] of e.bodies) {
  if (!pinned.has(id) && body.localAnchor.size > 0) out.push(id)
}
```

- [ ] **Step 5: Run Task 1 tests to GREEN**

Run: `npm test -- tests/view/bend.test.ts tests/view/engine.test.ts tests/view/wires.test.ts tests/view/stub-scope.test.ts tests/formula/diagram.test.ts`

Expected: PASS.

### Task 3: Unify obstacle, paint, and interaction geometry

**Files:**
- Modify: `src/view/engine.ts`
- Modify: `src/view/relax.ts`
- Modify: `src/view/score-delta.ts`
- Modify: `src/view/wires.ts`
- Modify: `src/view/paint.ts`
- Modify: `src/view/canvas.ts`
- Modify: `src/app/hittest.ts`
- Modify: `src/app/interact/copy-view.ts`
- Modify: `src/app/shell.ts`
- Modify: `src/view/index.ts`
- Modify: `tests/view/paint.test.ts`
- Modify: `tests/physics/paint.test.ts`
- Modify: `tests/physics/drawn-energy.test.ts`
- Modify: `tests/physics/frozen-probe.test.ts`

**Interfaces:**
- Consumes: materialized `Body.geometry`, explicit node/end binds, and `anatomyOutline`.
- Produces: one obstacle predicate used by live/frozen/incremental routing and one ordinary body paint pass for atom/identity/end circular anatomy.

- [ ] **Step 1: Specify ordinary paint ownership**

Assert identity and existential arcs remain present when `paint` receives an empty wire painter, have the same radius under the same engine scale, and emit no centered dot/stub glyph.

```ts
const bodiesOnly = paint(engine, LIGHT, () => [])
expect(arcsAt(bodiesOnly, identityBody.pos)).toHaveLength(1)
expect(arcsAt(bodiesOnly, endBody.pos)).toHaveLength(1)
```

- [ ] **Step 2: Collapse obstacle classification**

Export a geometry-derived body predicate from `engine.ts` and use it in `routeObstacles`, `drawnObstacles`, frozen obstacle capture, and incremental moved-obstacle evaluation.

```ts
export const isBodyObstacle = (body: Body): boolean => body.geometry !== null
```

- [ ] **Step 3: Paint small nodes in the semantic/body pass**

Retain wire-owner lookup only for stroke colour. Send identity and end bodies through `anatomyOutline`; retain identity's no-pip rule. Remove point-dot and degenerate existential-stub drawing authority.

```ts
if (body.geometry !== null) {
  shapes.push(...anatomyOutline(e, body, body.geometry, bodyStroke(body), st.wireW, glow(bodyStroke(body))))
}
```

- [ ] **Step 4: Migrate interaction consumers**

Hit-test existential bodies directly as wire targets, let routed leg paths provide wire strokes, and include wire-owned end body circles when calculating copy/debug extents. Preserve semantic-node hit ownership for identities.

```ts
if (wire.end !== null) {
  const body = engine.bodies.get(wire.end.body)!
  discs.push({ center: body.pos, r: body.discR * engine.scale + 2 })
}
```

- [ ] **Step 5: Validate focused physics**

Run: `npm run test:physics -- tests/physics/paint.test.ts tests/physics/drawn-energy.test.ts tests/physics/frozen-probe.test.ts tests/physics/stub-scope.test.ts`

Expected: PASS, including identity rail linework and exact full/frozen energy agreement.

### Task 4: Integrate, review, and commit

**Files:**
- Modify if a failing authoritative check identifies a task-owned dependent: the narrow dependent only.
- Commit: all validated task-owned files; exclude unrelated worktree state.

**Interfaces:**
- Consumes: Tasks 1-3.
- Produces: a type-safe, fully validated shared small-node view model.

- [ ] **Step 1: Run authoritative validation**

Run: `npm run typecheck`

Run: `npm test`

Run: `npm run test:physics`

Expected: all PASS.

- [ ] **Step 2: Inspect the final diff and review the complexity gates**

Confirm one terminal geometry path, one body paint path, one obstacle predicate, no identity/end centered-terminal branches, and no task changes to unrelated Lean sources.

- [ ] **Step 3: Commit task-owned work**

```bash
git add docs/superpowers/plans/2026-08-12-identity-dangling-node-rendering.md src/view src/app tests/view tests/physics tests/formula/diagram.test.ts
git commit -m "fix: share small node geometry across identities and existentials"
```
