# Plan 7: Equational + Comprehension Rules Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The remaining three rule families of spec §3.1 — βη-congruence (rule 5), fusion/fission (rule 6), fold/unfold over a definitions environment (rule 7) — plus both directions of comprehension (rule 8), completing the kernel's rule surface.

**Architecture:** Same shape as Plan 6: pure functions `Diagram → Diagram` (conversion also returns its certificate) in `src/kernel/rules/`, gates throwing `RuleError`, malformed input throwing `DiagramError` (the Plan 6 vocabulary invariant: RuleError ⇔ a rule evaluated its gate against a real referent and refused). Term surgery lives in a new `src/kernel/term/path.ts` (subterm navigation, port substitution); the rules layer gains a tiny shared `access.ts` (node/wire lookups). Comprehension reuses splice (instantiate) and extract + boundary-pinned fingerprints (abstract).

**Tech Stack:** TypeScript strict, Vitest, no runtime deps.

---

## Design decisions (read before implementing)

**Conversion and the port problem.** βη-conversion can change a term's free-port set: `(λx. y) z` has ports {y, z} but normalizes to `y` with ports {y}. The λ-node `o = t(x⃗)` denotes the relation `{(o, x⃗) | o =βη t(x⃗)}`; when `t ≈βη t′`, any column absent from `t′` was already unconstrained in `t` (o =βη t ⟺ o =βη t′ pointwise). So: **vanished ports** silently lose their endpoint (the wire survives, trimmed — possibly to zero endpoints, which Plan 6 established is a sound isolated line of identity); **added ports** are vacuous columns and may attach anywhere — the caller may name an existing wire per added port, and unnamed ones get fresh singleton wires at the node's region. Both directions are equivalences, so conversion has **no polarity gate**.

**Fuel honesty + certificates.** `applyConversion` uses `convertible` (fueled search) and returns `{ diagram, certificate }` so Plan 8 proof steps can store the certificate. Fuel exhaustion throws a RuleError that says so. `applyConversionByCertificate` replays a stored certificate via `checkConversion` — fuel-free, so fuel limits are never terminal.

**Fusion is the one-point rule.** `∃w (w = t_a(x⃗) ∧ Φ(w)) ⟺ Φ(t_a(x⃗))` requires: the wire has exactly two endpoints, one the producer's output and one a consumer freeVar port (so nothing else observes w); the producer sits **at the wire's scope** (the equation must be a conjunct at the quantifier's location — a producer under an intervening cut or bubble is not a plain conjunct); producer ≠ consumer (a self-loop is a recursive equation the one-point rule cannot remove). It is an equivalence — no polarity gate. Port collisions between the producer's term and the consumer's residual term are renamed to fresh names **unless both sides already share the same wire** (then the consumer's existing endpoint carries the merged port). Substituting a node term under the consumer's binders is capture-free without shifting because node terms are bvar-closed and ports are a separate namespace from de Bruijn indices.

**Fission is fusion's exact inverse.** Extract a **bvar-closed** subterm at a path (a subterm referencing binders above it would arrive at the new node with dangling indices — refused by name), replace it with a fresh port, create the producer node and the two-endpoint wire at the node's region. `applyFusion(applyFission(d, n, path), newWire)` is a fingerprint identity.

**Definitions are opaque constants, syntactically matched.** `Definitions = Readonly<Record<string, Term>>`; every body must be bvar-closed and **port-free** (a definition cannot capture wiring). Unfold replaces `const c` at a path by its body; fold replaces a subterm **syntactically equal** (termEq) to a body by the constant. Conversion-up-to-βη before folding is rule 5's job — compose, don't conflate. Both are equivalences — no polarity gate, wires untouched (bodies are port-free).

**Comprehension polarity.** `φ(G) ⟹ ∃R.φ(R)`. At a **positive** region you may replace φ(G) by ∃R.φ(R) — *abstraction* (wrap content in a fresh bubble, replace chosen G-occurrences by atoms). At a **negative** region you may replace ∃R.φ(R) by φ(G) — *instantiation* (splice a copy of G at every atom of the bubble, then dissolve the bubble). The gate tests `polarity(d, bubbleOrWrapRegion)` — bubbles never flip parity, so the bubble's own polarity equals its parent's.

**Instantiation mechanics:** for each atom bound by the bubble, `spliceSubgraph(cur, atom.region, comp, argWires)` with `argWires[i]` = the wire holding the atom's `arg i` port, then drop the atom; finally dissolve the bubble exactly like double-cut elim promotes the inner cut (children/nodes/wire-scopes to the bubble's parent). Atoms with repeated argument wires (R(x,x)) work — `arg 0` and `arg 1` are distinct ports that may share a wire.

**Abstraction mechanics and the consistency obligation:** every replaced occurrence must be the *same* relation with the *same argument order*. The caller supplies, per occurrence, a `SubgraphSelection` plus `args` — the attachment wire serving as argument i. We `extractSubgraph` each occurrence, reorder its boundary by `args`, and require `boundaryFingerprint(reordered) === boundaryFingerprint(comp)` — exact by the Plan 3 theorem (equal pinned fingerprints iff isomorphic respecting boundary order). Occurrences must be pairwise disjoint and lie inside the wrapped content. The wrap works like double-cut intro: a fresh bubble at `wrap.region`, selected subtree roots and direct nodes reparented in, selected top-level wires keeping their scope (∃x ∃R φ ⟺ ∃R ∃x φ for independent quantifiers).

**Known limitation (carried):** abstraction cannot express an occurrence using one host wire as two different arguments (R(x,x) direction) — extraction yields one stub per touching wire, so `args` must be distinct; the permutation check refuses loudly. Instantiation handles the R(x,x) shape fine. Revisit if a Plan 8+ proof needs the abstract direction with identified arguments.

**File map:**
- Create `src/kernel/term/path.ts` (+ barrel line in `src/kernel/term/index.ts`)
- Create `src/kernel/rules/access.ts`, `conversion.ts`, `fusion.ts`, `definitions.ts`, `comprehension.ts`
- Extend `src/kernel/rules/index.ts`
- Tests mirror under `tests/kernel/term/path.test.ts` and `tests/kernel/rules/{conversion,fusion,definitions,comprehension-instantiate,comprehension-abstract,equational-gates}.test.ts`

---

### Task 1: Term path & port utilities

**Files:**
- Create: `src/kernel/term/path.ts`
- Modify: `src/kernel/term/index.ts` (add barrel line)
- Test: `tests/kernel/term/path.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/term/path.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { termEq, port } from '../../../src/kernel/term/term'
import { subtermAt, replaceSubtermAt, isBvarClosed, substPort, freshPortName } from '../../../src/kernel/term/path'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('subtermAt / replaceSubtermAt', () => {
  it('navigates body/fn/arg and round-trips replacement', () => {
    const t = p('\\x. (\\y. y) x')
    expect(printTerm(subtermAt(t, ['body', 'fn']))).toBe(printTerm(p('\\y. y')))
    const swapped = replaceSubtermAt(t, ['body', 'fn'], p('\\y. z'))
    expect(printTerm(subtermAt(swapped, ['body', 'fn']))).toBe(printTerm(p('\\y. z')))
    expect(termEq(replaceSubtermAt(swapped, ['body', 'fn'], p('\\y. y')), t)).toBe(true)
  })

  it('the empty path is the whole term', () => {
    const t = p('x y')
    expect(termEq(subtermAt(t, []), t)).toBe(true)
    expect(termEq(replaceSubtermAt(t, [], p('z')), p('z'))).toBe(true)
  })

  it('rejects invalid paths by position and kind', () => {
    expect(() => subtermAt(p('x'), ['body'])).toThrowError(/invalid path segment 'body' at position 0 into 'port'/)
    expect(() => replaceSubtermAt(p('\\x. x'), ['fn'], p('y'))).toThrowError(/invalid path segment 'fn' into 'lam'/)
  })
})

describe('isBvarClosed', () => {
  it('accepts internally bound bvars and rejects escaping ones', () => {
    expect(isBvarClosed(p('\\x. x'))).toBe(true)
    expect(isBvarClosed(p('y'))).toBe(true)
    // the subterm `x` of `\x. x` escapes: bvar 0 at depth 0
    expect(isBvarClosed(subtermAt(p('\\x. x'), ['body']))).toBe(false)
    expect(isBvarClosed(subtermAt(p('\\x. \\y. x y'), ['body', 'body']))).toBe(false)
  })
})

describe('substPort', () => {
  it('replaces every occurrence, including under binders, without shifting', () => {
    const t = p('\\x. q (x q)')
    const out = substPort(t, 'q', p('\\y. y'))
    expect(printTerm(out)).toBe(printTerm(p('\\x. (\\y. y) (x (\\y. y))')))
  })

  it('leaves other ports and bvars alone', () => {
    const t = p('\\x. r x')
    expect(termEq(substPort(t, 'q', p('z')), t)).toBe(true)
  })

  it('rejects a replacement that is not bvar-closed', () => {
    const escaping = subtermAt(p('\\x. x'), ['body'])
    expect(() => substPort(p('q'), 'q', escaping)).toThrowError(/replacement must be bvar-closed/)
  })
})

describe('freshPortName', () => {
  it('returns the base when free, else suffixes deterministically', () => {
    expect(freshPortName(new Set(), 'x')).toBe('x')
    expect(freshPortName(new Set(['x']), 'x')).toBe('x_0')
    expect(freshPortName(new Set(['x', 'x_0']), 'x')).toBe('x_1')
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/term/path.test.ts`
Expected: FAIL — cannot resolve `term/path`.

- [ ] **Step 3: Implement**

`src/kernel/term/path.ts`:

```ts
import type { Term } from './term'
import { lam, app } from './term'
import type { PathSeg } from './reduce'

/** The subterm at a path of body/fn/arg segments. Throws on a path/term mismatch. */
export function subtermAt(t: Term, path: readonly PathSeg[]): Term {
  let cur = t
  for (const [i, seg] of path.entries()) {
    if (seg === 'body' && cur.kind === 'lam') { cur = cur.body; continue }
    if (seg === 'fn' && cur.kind === 'app') { cur = cur.fn; continue }
    if (seg === 'arg' && cur.kind === 'app') { cur = cur.arg; continue }
    throw new Error(`invalid path segment '${seg}' at position ${i} into '${cur.kind}'`)
  }
  return cur
}

/** Replace the subterm at a path. No shifting: callers substitute bvar-closed terms only. */
export function replaceSubtermAt(t: Term, path: readonly PathSeg[], replacement: Term): Term {
  if (path.length === 0) return replacement
  const [seg, ...rest] = path
  if (seg === 'body' && t.kind === 'lam') return lam(replaceSubtermAt(t.body, rest, replacement))
  if (seg === 'fn' && t.kind === 'app') return app(replaceSubtermAt(t.fn, rest, replacement), t.arg)
  if (seg === 'arg' && t.kind === 'app') return app(t.fn, replaceSubtermAt(t.arg, rest, replacement))
  throw new Error(`invalid path segment '${seg}' into '${t.kind}'`)
}

/** True iff every bvar in t is bound by a lam inside t. */
export function isBvarClosed(t: Term): boolean {
  const visit = (u: Term, depth: number): boolean => {
    switch (u.kind) {
      case 'bvar': return u.index < depth
      case 'lam': return visit(u.body, depth + 1)
      case 'app': return visit(u.fn, depth) && visit(u.arg, depth)
      case 'port':
      case 'const':
        return true
    }
  }
  return visit(t, 0)
}

/**
 * Replace every occurrence of the named port by s. s must be bvar-closed:
 * a closed term needs no shifting under binders, and ports are a separate
 * namespace from de Bruijn indices, so plain replacement is capture-free.
 */
export function substPort(t: Term, name: string, s: Term): Term {
  if (!isBvarClosed(s)) throw new Error('substPort replacement must be bvar-closed')
  const visit = (u: Term): Term => {
    switch (u.kind) {
      case 'port': return u.name === name ? s : u
      case 'lam': return lam(visit(u.body))
      case 'app': return app(visit(u.fn), visit(u.arg))
      case 'bvar':
      case 'const':
        return u
    }
  }
  return visit(t)
}

/** Deterministic fresh port name: the base if free, else base_0, base_1, ... */
export function freshPortName(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let i = 0; ; i++) {
    const candidate = `${base}_${i}`
    if (!taken.has(candidate)) return candidate
  }
}
```

Append to `src/kernel/term/index.ts`:

```ts
export { subtermAt, replaceSubtermAt, isBvarClosed, substPort, freshPortName } from './path'
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/term/path.ts src/kernel/term/index.ts tests/kernel/term/path.test.ts
git commit -m "feat(kernel): term path navigation, port substitution, bvar-closure"
```

**Review outcome (commit `060cc55`):** APPROVED; only permitted deviation (unused `port` test import removed). Capture-safety probes confirmed: closed-term substitution under three nested lams leaves inner indices unchanged; escaping replacements refused. All five mutation probes killed by existing tests. Suite: 272.

---

### Task 2: Access helpers + conversion rule

**Files:**
- Create: `src/kernel/rules/access.ts`
- Create: `src/kernel/rules/conversion.ts`
- Test: `tests/kernel/rules/conversion.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/conversion.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyConversion, applyConversionByCertificate } from '../../../src/kernel/rules/conversion'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applyConversion', () => {
  it('normalizes a node term in place (same ports), returning a certificate', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { diagram, certificate } = applyConversion(d, n, p('y'), 10)
    expect(diagram.nodes[n]?.kind).toBe('term')
    expect(certificate.leftSteps.length).toBeGreaterThan(0)
    // ports unchanged: y's wire still has its endpoint
    const after = Object.values(diagram.wires).filter((w) => w.endpoints.some((ep) => ep.node === n))
    expect(after).toHaveLength(2) // output + y
  })

  it('detaches vanished ports, trimming their wires', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. y) z'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const wz = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'z' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    const { diagram } = applyConversion(d, n, p('y'), 10)
    expect(diagram.wires[wz]?.endpoints).toHaveLength(1)
    expect(diagram.wires[wz]?.endpoints[0]?.node).toBe(hub)
  })

  it('attaches added ports to named wires, or to fresh singletons', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const wz = h.wire(h.root, [{ node: hub, port: { kind: 'output' } }])
    const d = h.build()
    const named = applyConversion(d, n, p('(\\x. y) z'), 10, { z: wz }).diagram
    expect(named.wires[wz]?.endpoints).toHaveLength(2)
    const fresh = applyConversion(d, n, p('(\\x. y) z'), 10).diagram
    const newWires = Object.keys(fresh.wires).filter((id) => d.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(fresh.wires[newWires[0]!]?.scope).toBe(d.root)
    expect(fresh.wires[newWires[0]!]?.endpoints).toHaveLength(1)
  })

  it('conversion round-trips by fingerprint when the port sets match', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const there = applyConversion(d, n, p('y'), 10).diagram
    const back = applyConversion(there, n, p('(\\x. x) y'), 10).diagram
    expect(diagramFingerprint(back)).toBe(diagramFingerprint(d))
  })

  it('rejects non-convertible terms by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    expect(() => applyConversion(d, n, p('\\x. \\y. x'), 10))
      .toThrowError(/not βη-convertible/)
  })

  it('reports fuel exhaustion by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x x) (\\x. x x)'))
    const d = h.build()
    expect(() => applyConversion(d, n, p('\\x. x'), 5))
      .toThrowError(/undecided under fuel 5/)
  })

  it('rejects atoms and unknown nodes with the right vocabulary', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)
    const a = h.atom(bub, bub)
    const d = h.build()
    expect(() => applyConversion(d, a, p('y'), 10)).toThrowError(/term nodes/)
    let caught: unknown
    try { applyConversion(d, 'ghost', p('y'), 10) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('rejects attachments naming ports that are not newly added', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    let caught: unknown
    try { applyConversion(d, n, p('y'), 10, { y: 'w0' }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })

  it('works inside nested regions: fresh wires at the node region, not root', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const inner = h.cut(cut)
    const n = h.termNode(inner, p('y'))
    const d = h.build()
    const out = applyConversion(d, n, p('(\\x. y) z'), 10).diagram
    const newWires = Object.keys(out.wires).filter((id) => d.wires[id] === undefined)
    expect(newWires).toHaveLength(1)
    expect(out.wires[newWires[0]!]?.scope).toBe(inner)
  })
})

describe('applyConversionByCertificate', () => {
  it('replays a stored certificate without fuel and rejects forged ones by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\x. x) y'))
    const d = h.build()
    const { certificate } = applyConversion(d, n, p('y'), 10)
    const replayed = applyConversionByCertificate(d, n, p('y'), certificate)
    expect(replayed.nodes[n]?.kind).toBe('term')
    const forged = { leftSteps: [], rightSteps: [] }
    expect(() => applyConversionByCertificate(d, n, p('y'), forged))
      .toThrowError(/certificate rejected/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/conversion.test.ts`
Expected: FAIL — cannot resolve `rules/conversion`.

- [ ] **Step 3: Implement**

`src/kernel/rules/access.ts`:

```ts
import type { Diagram, DiagramNode, NodeId, Port, WireId } from '../diagram/diagram'
import { DiagramError, portKey } from '../diagram/diagram'
import { RuleError } from './error'

/** The node, required to be a term node: unknown id is malformed input, an atom is a refusal. */
export function termNodeAt(d: Diagram, nodeId: NodeId): Extract<DiagramNode, { kind: 'term' }> {
  const node = d.nodes[nodeId]
  if (node === undefined) throw new DiagramError(`unknown node '${nodeId}'`)
  if (node.kind !== 'term') throw new RuleError(`this rule applies to term nodes; '${nodeId}' is an atom`)
  return node
}

/**
 * The unique wire holding (node, port). The port-partition invariant of
 * mkDiagram guarantees existence for every required port of a validated
 * diagram, so a miss means the caller asked about a port the node lacks.
 */
export function wireAt(d: Diagram, node: NodeId, p: Port): WireId {
  const key = portKey(p)
  for (const [id, w] of Object.entries(d.wires)) {
    for (const ep of w.endpoints) {
      if (ep.node === node && portKey(ep.port) === key) return id
    }
  }
  throw new DiagramError(`no wire holds port '${key}' of node '${node}'`)
}
```

`src/kernel/rules/conversion.ts`:

```ts
import type { Term } from '../term/term'
import { freePorts } from '../term/term'
import { printTerm } from '../term/print'
import { convertible } from '../term/convert'
import type { ConversionCertificate } from '../term/certificate'
import { checkConversion } from '../term/certificate'
import type { Diagram, DiagramNode, Endpoint, NodeId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt } from './access'

/**
 * Swap a term node's term for a βη-equal one (callers have already verified
 * equality). When t ≈βη t′, any port column absent from t′ was already
 * unconstrained in t (o =βη t ⟺ o =βη t′ pointwise), so detaching a vanished
 * port's endpoint and attaching an added port's endpoint to ANY wire are both
 * equivalences. Vanished ports trim their wires (which survive, possibly
 * endpoint-less); added ports attach to the named wire or a fresh singleton
 * at the node's region.
 */
function replaceNodeTerm(
  d: Diagram,
  nodeId: NodeId,
  node: Extract<DiagramNode, { kind: 'term' }>,
  newTerm: Term,
  attachments: Readonly<Record<string, WireId>>,
): Diagram {
  const oldPorts = new Set(freePorts(node.term))
  const newPorts = new Set(freePorts(newTerm))
  for (const [name, w] of Object.entries(attachments)) {
    if (oldPorts.has(name) || !newPorts.has(name)) {
      throw new DiagramError(`attachment for port '${name}', which is not a newly added free port of the replacement term`)
    }
    if (d.wires[w] === undefined) throw new DiagramError(`unknown wire '${w}'`)
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = {
      scope: w.scope,
      endpoints: w.endpoints.filter(
        (ep) => !(ep.node === nodeId && ep.port.kind === 'freeVar' && !newPorts.has(ep.port.name)),
      ),
    }
  }
  for (const name of newPorts) {
    if (oldPorts.has(name)) continue
    const ep: Endpoint = { node: nodeId, port: { kind: 'freeVar', name } }
    const target = attachments[name]
    if (target !== undefined) {
      const w = wires[target]!
      wires[target] = { scope: w.scope, endpoints: [...w.endpoints, ep] }
    } else {
      const fresh = freshId(new Set(Object.keys(wires)), `${nodeId}_${name}`)
      wires[fresh] = { scope: node.region, endpoints: [ep] }
    }
  }
  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nodeId]: { kind: 'term', region: node.region, term: newTerm },
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

export type ConversionResult = {
  readonly diagram: Diagram
  readonly certificate: ConversionCertificate
}

/**
 * Rule 5 (spec §3.1), interactive form: replace a node's term by a
 * βη-convertible one, searching under the fuel budget. Equivalence — no
 * polarity gate. The certificate is returned for proof storage (§3.7).
 */
export function applyConversion(
  d: Diagram,
  nodeId: NodeId,
  newTerm: Term,
  fuel: number,
  attachments: Readonly<Record<string, WireId>> = {},
): ConversionResult {
  const node = termNodeAt(d, nodeId)
  const r = convertible(node.term, newTerm, fuel)
  if (r.status === 'fuel-exhausted') {
    throw new RuleError(`conversion is undecided under fuel ${fuel}: ${r.detail}; supply a certificate or raise the fuel`)
  }
  if (r.status === 'not-convertible') {
    throw new RuleError(`'${printTerm(node.term)}' and '${printTerm(newTerm)}' are not βη-convertible`)
  }
  return { diagram: replaceNodeTerm(d, nodeId, node, newTerm, attachments), certificate: r.certificate }
}

/** Rule 5, replay form: fuel-free, checks a stored certificate mechanically. */
export function applyConversionByCertificate(
  d: Diagram,
  nodeId: NodeId,
  newTerm: Term,
  certificate: ConversionCertificate,
  attachments: Readonly<Record<string, WireId>> = {},
): Diagram {
  const node = termNodeAt(d, nodeId)
  const check = checkConversion(node.term, newTerm, certificate)
  if (!check.ok) throw new RuleError(`conversion certificate rejected: ${check.reason}`)
  return replaceNodeTerm(d, nodeId, node, newTerm, attachments)
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/access.ts src/kernel/rules/conversion.ts tests/kernel/rules/conversion.test.ts
git commit -m "feat(kernel): βη-conversion rule with certificates and port surgery"
```

---

### Task 3: Fusion + fission

**Files:**
- Create: `src/kernel/rules/fusion.ts`
- Test: `tests/kernel/rules/fusion.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/fusion.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { app, port, termEq } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyFusion, applyFission } from '../../../src/kernel/rules/fusion'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applyFusion', () => {
  it('inlines a producer along a two-endpoint wire (one-point rule)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const b = h.termNode(h.root, p('q y'))
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = h.build()
    const out = applyFusion(d, w)
    expect(out.nodes[a]).toBeUndefined()
    expect(out.wires[w]).toBeUndefined()
    const merged = out.nodes[b]
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(\\x. x) y')))
  })

  it('migrates the producer ports onto the consumer, sharing wires where they already share', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y z'))
    const b = h.termNode(h.root, p('q y'))
    const shared = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = h.build()
    const out = applyFusion(d, w)
    const merged = out.nodes[b]
    // y shared the same wire: no rename, single y port carried by b's old endpoint
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(y z) y')))
    expect(out.wires[shared]?.endpoints).toHaveLength(1)
    expect(out.wires[shared]?.endpoints[0]?.node).toBe(b)
  })

  it('freshens colliding ports wired differently', () => {
    // builder auto-singleton wires: a.y and b.y are DIFFERENT wires, so the
    // producer's y must be freshened to y_0 (compare via constructors — the
    // parser need not accept underscores in identifiers)
    const h2 = new DiagramBuilder()
    const a2 = h2.termNode(h2.root, p('y'))
    const b2 = h2.termNode(h2.root, p('q y'))
    const w2 = h2.wire(h2.root, [
      { node: a2, port: { kind: 'output' } },
      { node: b2, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d2 = h2.build()
    const out = applyFusion(d2, w2)
    const merged = out.nodes[b2]
    expect(merged?.kind === 'term' && termEq(merged.term, app(port('y_0'), port('y')))).toBe(true)
  })

  it('rejects wires of the wrong shape, self-loops, and displaced producers, by name', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const b = h.termNode(h.root, p('\\x. \\y. x'))
    const w3 = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    expect(() => applyFusion(d, w3)).toThrowError(/one output endpoint and one freeVar endpoint/)

    const h2 = new DiagramBuilder()
    const n = h2.termNode(h2.root, p('q'))
    const loop = h2.wire(h2.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d2 = h2.build()
    expect(() => applyFusion(d2, loop)).toThrowError(/cannot inline a node into itself/)

    const h3 = new DiagramBuilder()
    const cut = h3.cut(h3.root)
    const a3 = h3.termNode(cut, p('\\x. x'))
    const b3 = h3.termNode(cut, p('q'))
    const w4 = h3.wire(h3.root, [
      { node: a3, port: { kind: 'output' } },
      { node: b3, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d3 = h3.build()
    expect(() => applyFusion(d3, w4)).toThrowError(/producing node to sit at the wire's scope/)
  })
})

describe('applyFission', () => {
  it('extracts a bvar-closed subterm to a new node; fusion inverts it (fingerprint)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('(\\x. x) y'))
    const d = h.build()
    const split = applyFission(d, n, ['fn'])
    const producer = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
    expect(split.nodes[producer]?.kind).toBe('term')
    const newWire = Object.keys(split.wires).find(
      (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
    )!
    expect(split.wires[newWire]?.scope).toBe(cut)
    expect(diagramFingerprint(applyFusion(split, newWire))).toBe(diagramFingerprint(d))
  })

  it('keeps shared ports attached on both nodes', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y ((\\x. x) y)'))
    const d = h.build()
    const split = applyFission(d, n, ['arg'])
    const yWire = Object.entries(split.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.port.kind === 'freeVar' && ep.port.name === 'y'))![1]
    expect(yWire.endpoints).toHaveLength(2)
  })

  it('rejects subterms that reference outer binders, by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x y'))
    const d = h.build()
    expect(() => applyFission(d, n, ['body']))
      .toThrowError(/bvar-closed subterm/)
  })

  it('rejects invalid paths as malformed input', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const d = h.build()
    expect(() => applyFission(d, n, ['fn'])).toThrowError(/invalid path/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/fusion.test.ts`
Expected: FAIL — cannot resolve `rules/fusion`.

- [ ] **Step 3: Implement**

`src/kernel/rules/fusion.ts`:

```ts
import type { Term } from '../term/term'
import { freePorts, port } from '../term/term'
import type { PathSeg } from '../term/reduce'
import { subtermAt, replaceSubtermAt, isBvarClosed, substPort, freshPortName } from '../term/path'
import type { Diagram, DiagramNode, Endpoint, NodeId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { termNodeAt, wireAt } from './access'

/**
 * Rule 6a (spec §3.1), fusion: inline a producer node along its output wire
 * into the single consumer — the one-point rule ∃w (w = t ∧ Φ(w)) ⟺ Φ(t).
 * Requirements: the wire has exactly the producer's output endpoint and one
 * consumer freeVar endpoint (nothing else observes w); the producer sits AT
 * the wire's scope (the equation must be a conjunct at the quantifier's
 * location); producer ≠ consumer (a self-loop is a recursive equation).
 * Equivalence — no polarity gate. Producer ports colliding with the
 * consumer's residual ports are freshened unless both sides already share
 * the same wire.
 */
export function applyFusion(d: Diagram, wireId: WireId): Diagram {
  const w = d.wires[wireId]
  if (w === undefined) throw new DiagramError(`unknown wire '${wireId}'`)
  if (w.endpoints.length !== 2) {
    throw new RuleError(`fusion requires a wire with exactly two endpoints; '${wireId}' has ${w.endpoints.length}`)
  }
  let producerId: NodeId | undefined
  let consumerId: NodeId | undefined
  let consumedPort: string | undefined
  for (const ep of w.endpoints) {
    if (ep.port.kind === 'output') producerId = ep.node
    else if (ep.port.kind === 'freeVar') { consumerId = ep.node; consumedPort = ep.port.name }
  }
  if (producerId === undefined || consumerId === undefined || consumedPort === undefined) {
    throw new RuleError(`fusion requires one output endpoint and one freeVar endpoint on wire '${wireId}'`)
  }
  if (producerId === consumerId) {
    throw new RuleError(`fusion cannot inline a node into itself ('${producerId}'); the equation is recursive`)
  }
  const a = termNodeAt(d, producerId)
  const b = termNodeAt(d, consumerId)
  if (a.region !== w.scope) {
    throw new RuleError(
      `fusion requires the producing node to sit at the wire's scope; node '${producerId}' is in '${a.region}' but wire '${wireId}' is scoped at '${w.scope}'`,
    )
  }

  const residual = new Set(freePorts(b.term))
  residual.delete(consumedPort)
  const taken = new Set<string>([...freePorts(a.term), ...freePorts(b.term)])
  let producerTerm = a.term
  // endpoints to add to the consumer, on the producer's old wires
  const migrations: { readonly wire: WireId; readonly portName: string }[] = []
  for (const n of freePorts(a.term)) {
    const wa = wireAt(d, producerId, { kind: 'freeVar', name: n })
    if (residual.has(n)) {
      const wb = wireAt(d, consumerId, { kind: 'freeVar', name: n })
      if (wa === wb) continue // the consumer's existing endpoint carries the merged port
      const fresh = freshPortName(taken, n)
      taken.add(fresh)
      producerTerm = substPort(producerTerm, n, port(fresh))
      migrations.push({ wire: wa, portName: fresh })
    } else {
      migrations.push({ wire: wa, portName: n })
    }
  }
  const mergedTerm = substPort(b.term, consumedPort, producerTerm)

  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id === producerId) continue
    nodes[id] = id === consumerId ? { kind: 'term', region: b.region, term: mergedTerm } : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wv] of Object.entries(d.wires)) {
    if (id === wireId) continue
    const kept = wv.endpoints.filter((ep) => ep.node !== producerId)
    const adds = migrations
      .filter((m) => m.wire === id)
      .map((m): Endpoint => ({ node: consumerId!, port: { kind: 'freeVar', name: m.portName } }))
    wires[id] = { scope: wv.scope, endpoints: [...kept, ...adds] }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Rule 6b, fission: extract a bvar-closed subterm to a fresh producer node
 * wired to a fresh port of the residual — fusion's exact inverse. The new
 * node and wire live at the host node's region so applyFusion can undo it.
 */
export function applyFission(d: Diagram, nodeId: NodeId, path: readonly PathSeg[]): Diagram {
  const node = termNodeAt(d, nodeId)
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (!isBvarClosed(sub)) {
    throw new RuleError(`fission requires a bvar-closed subterm; the subterm at [${path.join(', ')}] references binders above it`)
  }
  const q = freshPortName(new Set(freePorts(node.term)), 'q')
  const residualTerm = replaceSubtermAt(node.term, path, port(q))
  const residualPorts = new Set(freePorts(residualTerm))
  const producerId = freshId(new Set(Object.keys(d.nodes)), `${nodeId}_fis`)
  const newWireId = freshId(new Set(Object.keys(d.wires)), `${nodeId}_fis`)

  const subPortWires = new Map<string, WireId>()
  for (const n of freePorts(sub)) {
    subPortWires.set(n, wireAt(d, nodeId, { kind: 'freeVar', name: n }))
  }

  const nodes: Record<NodeId, DiagramNode> = {
    ...d.nodes,
    [nodeId]: { kind: 'term', region: node.region, term: residualTerm },
    [producerId]: { kind: 'term', region: node.region, term: sub },
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    const adds: Endpoint[] = []
    for (const [n, wid] of subPortWires) {
      if (wid === id) adds.push({ node: producerId, port: { kind: 'freeVar', name: n } })
    }
    const kept = w.endpoints.filter(
      (ep) => !(ep.node === nodeId && ep.port.kind === 'freeVar' && !residualPorts.has(ep.port.name)),
    )
    wires[id] = { scope: w.scope, endpoints: [...kept, ...adds] }
  }
  wires[newWireId] = {
    scope: node.region,
    endpoints: [
      { node: producerId, port: { kind: 'output' } },
      { node: nodeId, port: { kind: 'freeVar', name: q } },
    ],
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/fusion.ts tests/kernel/rules/fusion.test.ts
git commit -m "feat(kernel): fusion and fission via the one-point rule"
```

---

### Task 4: Definitions — unfold/fold

**Files:**
- Create: `src/kernel/rules/definitions.ts`
- Test: `tests/kernel/rules/definitions.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/definitions.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { DiagramError } from '../../../src/kernel/diagram/diagram'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyUnfold, applyFold, assertWellFormedDefinitions } from '../../../src/kernel/rules/definitions'
import type { Definitions } from '../../../src/kernel/rules/definitions'

const consts = new Set(['I', 'K'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

const defs: Definitions = { I: pp('\\x. x'), K: pp('\\x. \\y. x') }

describe('assertWellFormedDefinitions', () => {
  it('accepts closed bodies and rejects port-bearing or bvar-open ones, by name', () => {
    expect(() => assertWellFormedDefinitions(defs)).not.toThrow()
    expect(() => assertWellFormedDefinitions({ bad: pp('y') }))
      .toThrowError(/free ports/)
    let caught: unknown
    try { assertWellFormedDefinitions({ bad: { kind: 'bvar', index: 0 } }) } catch (e) { caught = e }
    expect(caught).toBeInstanceOf(DiagramError)
  })
})

describe('applyUnfold / applyFold', () => {
  it('unfold replaces a constant by its body; fold inverts it (fingerprint)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyUnfold(d, defs, n, ['fn'])
    const un = unfolded.nodes[n]
    expect(un?.kind === 'term' && printTerm(un.term)).toBe(printTerm(p('(\\x. x) y')))
    const refolded = applyFold(unfolded, defs, n, ['fn'], 'I')
    expect(diagramFingerprint(refolded)).toBe(diagramFingerprint(d))
  })

  it('unfold works under binders (closed bodies need no shifting)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\z. K z'))
    const d = h.build()
    const out = applyUnfold(d, defs, n, ['body', 'fn'])
    const on = out.nodes[n]
    expect(on?.kind === 'term' && printTerm(on.term)).toBe(printTerm(p('\\z. (\\x. \\y. x) z')))
  })

  it('unfold rejects non-constants and unknown definitions, by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    expect(() => applyUnfold(d, defs, n, ['arg'])).toThrowError(/expects a constant/)
    expect(() => applyUnfold(d, { K: defs['K']! }, n, ['fn'])).toThrowError(/no definition for constant 'I'/)
  })

  it('fold demands syntactic equality, pointing at conversion otherwise', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('(\\a. a) y'))
    const d = h.build()
    expect(() => applyFold(d, defs, n, ['fn'], 'I'))
      .toThrowError(/not syntactically the definition/)
  })

  it('fold works inside nested regions, leaving wires untouched', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('(\\x. x) y'))
    const d = h.build()
    const out = applyFold(d, defs, n, ['fn'], 'I')
    const on = out.nodes[n]
    expect(on?.kind === 'term' && printTerm(on.term)).toBe(printTerm(p('I y')))
    expect(Object.keys(out.wires).sort()).toEqual(Object.keys(d.wires).sort())
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/definitions.test.ts`
Expected: FAIL — cannot resolve `rules/definitions`.

- [ ] **Step 3: Implement**

`src/kernel/rules/definitions.ts`:

```ts
import type { Term } from '../term/term'
import { cnst, freePorts, termEq, assertWellFormedTerm } from '../term/term'
import { printTerm } from '../term/print'
import type { PathSeg } from '../term/reduce'
import { subtermAt, replaceSubtermAt } from '../term/path'
import type { Diagram, DiagramNode, NodeId, RegionId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { RuleError } from './error'
import { termNodeAt } from './access'

/**
 * Definition environment for rule 7. Every body must stand alone: bvar-closed
 * (well-formed at depth 0, so substitution under binders needs no shifting)
 * and port-free (a definition cannot capture wiring). Plan 8's theory store
 * owns the environment; the rules just consume it.
 */
export type Definitions = Readonly<Record<string, Term>>

export function assertWellFormedDefinitions(defs: Definitions): void {
  for (const [id, body] of Object.entries(defs)) {
    if (id.length === 0) throw new DiagramError('definition id must be non-empty')
    try {
      assertWellFormedTerm(body)
    } catch (e) {
      throw new DiagramError(`definition '${id}': ${e instanceof Error ? e.message : String(e)}`)
    }
    const ports = freePorts(body)
    if (ports.length > 0) {
      throw new DiagramError(`definition '${id}' has free ports [${ports.join(', ')}]; definitions must be closed`)
    }
  }
}

function swapTerm(d: Diagram, nodeId: NodeId, region: RegionId, term: Term): Diagram {
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [nodeId]: { kind: 'term', region, term } }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires: { ...d.wires } })
}

/** Rule 7a (spec §3.1): replace a defined constant at a path by its body. Equivalence — no polarity gate. */
export function applyUnfold(d: Diagram, defs: Definitions, nodeId: NodeId, path: readonly PathSeg[]): Diagram {
  assertWellFormedDefinitions(defs)
  const node = termNodeAt(d, nodeId)
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (sub.kind !== 'const') {
    throw new RuleError(`unfold expects a constant at [${path.join(', ')}]; found '${sub.kind}'`)
  }
  const body = defs[sub.id]
  if (body === undefined) throw new RuleError(`no definition for constant '${sub.id}'`)
  return swapTerm(d, nodeId, node.region, replaceSubtermAt(node.term, path, body))
}

/** Rule 7b: replace a subterm syntactically equal to a definition body by the constant. */
export function applyFold(
  d: Diagram,
  defs: Definitions,
  nodeId: NodeId,
  path: readonly PathSeg[],
  constId: string,
): Diagram {
  assertWellFormedDefinitions(defs)
  const node = termNodeAt(d, nodeId)
  const body = defs[constId]
  if (body === undefined) throw new RuleError(`no definition for constant '${constId}'`)
  let sub: Term
  try {
    sub = subtermAt(node.term, path)
  } catch (e) {
    throw new DiagramError(`invalid path into node '${nodeId}': ${e instanceof Error ? e.message : String(e)}`)
  }
  if (!termEq(sub, body)) {
    throw new RuleError(
      `subterm '${printTerm(sub)}' at [${path.join(', ')}] is not syntactically the definition of '${constId}' ('${printTerm(body)}'); convert first (rule 5) if they are merely βη-equal`,
    )
  }
  return swapTerm(d, nodeId, node.region, replaceSubtermAt(node.term, path, cnst(constId)))
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/definitions.ts tests/kernel/rules/definitions.test.ts
git commit -m "feat(kernel): unfold/fold over a closed definitions environment"
```

---

### Task 5: Comprehension instantiation

**Files:**
- Create: `src/kernel/rules/comprehension.ts` (instantiate half)
- Test: `tests/kernel/rules/comprehension-instantiate.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/comprehension-instantiate.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyComprehensionInstantiate } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Comprehension of arity 1: "the argument is the identity function". */
function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('applyComprehensionInstantiate', () => {
  it('replaces each atom by a comprehension copy and dissolves the bubble', () => {
    // ¬(∃R. R(v)) instantiated with "is the identity" → ¬(v = λx.x)
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const atom = h.atom(bub, bub)
    const w = h.wire(cut, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())

    const e = new DiagramBuilder()
    const ecut = e.cut(e.root)
    const en = e.termNode(ecut, p('\\x. x'))
    e.wire(ecut, [{ node: en, port: { kind: 'output' } }])
    expect(diagramFingerprint(out)).toBe(diagramFingerprint(e.build()))
  })

  it('duplicates the comprehension across multiple atoms', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const a1 = h.atom(bub, bub)
    const a2 = h.atom(bub, bub)
    const w = h.wire(cut, [
      { node: a1, port: { kind: 'arg', index: 0 } },
      { node: a2, port: { kind: 'arg', index: 0 } },
    ])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())
    expect(Object.values(out.nodes)).toHaveLength(2)
    expect(out.wires[w]?.endpoints).toHaveLength(2)
    expect(out.regions[bub]).toBeUndefined()
  })

  it('with zero atoms it just dissolves the bubble', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 1)
    const n = h.termNode(bub, p('\\x. x'))
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, identityComp())
    expect(out.regions[bub]).toBeUndefined()
    expect(out.nodes[n]?.region).toBe(cut)
  })

  it('rejects positive bubbles, non-bubbles, and arity mismatches, by name', () => {
    const h = new DiagramBuilder()
    const posBub = h.bubble(h.root, 1)
    const cut = h.cut(h.root)
    const negBub = h.bubble(cut, 2)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, posBub, identityComp()))
      .toThrowError(/requires a negative bubble/)
    expect(() => applyComprehensionInstantiate(d, cut, identityComp()))
      .toThrowError(/requires a bubble/)
    expect(() => applyComprehensionInstantiate(d, negBub, identityComp()))
      .toThrowError(/arity mismatch/)
  })

  it('handles atoms with identified arguments: R(x,x)', () => {
    // arity-2 comprehension: "arg0 and arg1 are outputs of one identity node"
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w0 = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    // a second, bare boundary wire for arg 1
    const w1 = b.wire(b.root, [])
    const comp = mkDiagramWithBoundary(b.build(), [w0, w1])

    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const bub = h.bubble(cut, 2)
    const atom = h.atom(bub, bub)
    h.wire(cut, [
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const d = h.build()
    const out = applyComprehensionInstantiate(d, bub, comp)
    // the copy's output landed on the SAME wire both boundary stubs map to
    const termNodes = Object.values(out.nodes).filter((x) => x.kind === 'term')
    expect(termNodes).toHaveLength(1)
  })

  it('instantiates at depth 3 (negative) but not depth 2 (positive)', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const c3 = h.cut(c2)
    const bubDeep = h.bubble(c3, 1)
    const bubShallow = h.bubble(c2, 1)
    const d = h.build()
    expect(() => applyComprehensionInstantiate(d, bubDeep, identityComp())).not.toThrow()
    expect(() => applyComprehensionInstantiate(d, bubShallow, identityComp()))
      .toThrowError(/requires a negative bubble/)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/comprehension-instantiate.test.ts`
Expected: FAIL — cannot resolve `rules/comprehension`.

- [ ] **Step 3: Implement**

`src/kernel/rules/comprehension.ts` (instantiate half; Task 6 appends the abstract half to this file):

```ts
import type { Diagram, DiagramNode, NodeId, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { spliceSubgraph } from '../diagram/subgraph/splice'
import { RuleError } from './error'
import { wireAt } from './access'

/** Remove one node, trimming its endpoints off their wires. */
function dropNode(d: Diagram, nodeId: NodeId): Diagram {
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (id !== nodeId) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    wires[id] = { scope: w.scope, endpoints: w.endpoints.filter((ep) => ep.node !== nodeId) }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

/**
 * Rule 8, instantiation direction (spec §3.1): at a NEGATIVE position,
 * ∃R.φ(R) may be replaced by φ(G) — splice a copy of the comprehension G at
 * every atom the bubble binds (boundary wire i onto the atom's arg-i wire),
 * then dissolve the bubble, promoting its contents to its parent. The gate
 * tests the bubble's own polarity, which equals its parent's: bubbles never
 * flip parity (spec §2.1).
 */
export function applyComprehensionInstantiate(
  d: Diagram,
  bubbleId: RegionId,
  comp: DiagramWithBoundary,
): Diagram {
  const bubble = d.regions[bubbleId]
  if (bubble === undefined) throw new DiagramError(`unknown region '${bubbleId}'`)
  if (bubble.kind !== 'bubble') {
    throw new RuleError(`comprehension instantiation requires a bubble; '${bubbleId}' is a ${bubble.kind}`)
  }
  if (polarity(d, bubbleId) !== 'negative') {
    throw new RuleError(`comprehension instantiation requires a negative bubble; '${bubbleId}' is positive`)
  }
  if (comp.boundary.length !== bubble.arity) {
    throw new RuleError(
      `arity mismatch: bubble '${bubbleId}' binds a relation of arity ${bubble.arity}, but the comprehension has ${comp.boundary.length} boundary wires`,
    )
  }
  const atoms = Object.entries(d.nodes).filter(
    (entry): entry is [NodeId, Extract<DiagramNode, { kind: 'atom' }>] =>
      entry[1].kind === 'atom' && entry[1].binder === bubbleId,
  )
  let cur = d
  for (const [atomId, atom] of atoms) {
    const args: WireId[] = []
    for (let i = 0; i < bubble.arity; i++) {
      args.push(wireAt(cur, atomId, { kind: 'arg', index: i }))
    }
    cur = spliceSubgraph(cur, atom.region, comp, args)
    cur = dropNode(cur, atomId)
  }
  // dissolve the bubble: promote child regions, nodes, and wire scopes
  const parent = bubble.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(cur.regions)) {
    if (id === bubbleId) continue
    regions[id] = r.kind !== 'sheet' && r.parent === bubbleId
      ? (r.kind === 'cut' ? { kind: 'cut', parent } : { kind: 'bubble', parent, arity: r.arity })
      : r
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(cur.nodes)) {
    nodes[id] = n.region === bubbleId
      ? (n.kind === 'term'
        ? { kind: 'term', region: parent, term: n.term }
        : { kind: 'atom', region: parent, binder: n.binder })
      : n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(cur.wires)) {
    wires[id] = w.scope === bubbleId ? { scope: parent, endpoints: w.endpoints } : w
  }
  return mkDiagram({ root: cur.root, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/comprehension.ts tests/kernel/rules/comprehension-instantiate.test.ts
git commit -m "feat(kernel): comprehension instantiation at negative bubbles"
```

---

### Task 6: Comprehension abstraction

**Files:**
- Modify: `src/kernel/rules/comprehension.ts` (append the abstract half)
- Test: `tests/kernel/rules/comprehension-abstract.test.ts`

- [ ] **Step 1: Write the failing tests**

`tests/kernel/rules/comprehension-abstract.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyComprehensionAbstract } from '../../../src/kernel/rules/comprehension'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

/** Comprehension of arity 1: "the argument is the identity function". */
function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, p('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('applyComprehensionAbstract', () => {
  it('wraps content in a fresh bubble, replacing the occurrence by an atom', () => {
    // (v = λx.x) ∧ hub(v)  ⟹  ∃R. (R(v) ∧ hub(v))
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const hub = h.termNode(h.root, p('y'))
    const w = h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: hub, port: { kind: 'freeVar', name: 'y' } },
    ])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n, hub], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [occ])

    const e = new DiagramBuilder()
    const bub = e.bubble(e.root, 1)
    const ehub = e.termNode(bub, p('y'))
    const eatom = e.atom(bub, bub)
    e.wire(e.root, [
      { node: ehub, port: { kind: 'freeVar', name: 'y' } },
      { node: eatom, port: { kind: 'arg', index: 0 } },
    ])
    // hub's output wire stays scoped at root in the actual result (the rule
    // never rescopes wires), so the expected diagram pins it there explicitly
    e.wire(e.root, [{ node: ehub, port: { kind: 'output' } }])
    expect(diagramFingerprint(out)).toBe(diagramFingerprint(e.build()))
  })

  it('abstracts several disjoint occurrences consistently', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const w1 = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n1))![0]
    const w2 = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n2))![0]
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n1, n2], wires: [] })
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n1], wires: [] }), args: [w1] },
      { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n2], wires: [] }), args: [w2] },
    ])
    const atoms = Object.values(out.nodes).filter((x) => x.kind === 'atom')
    expect(atoms).toHaveLength(2)
    expect(Object.values(out.nodes).filter((x) => x.kind === 'term')).toHaveLength(0)
  })

  it('rejects occurrences that do not match the comprehension, by fingerprint', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. \\y. x'))
    const d = h.build()
    const w = Object.keys(d.wires)[0]!
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }), args: [w] }
    expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ]))
      .toThrowError(/does not match the comprehension/)
  })

  it('rejects argument-order mismatches: swapped args change the pinned fingerprint', () => {
    // comprehension of arity 2: arg0 is the output, arg1 is the free var y
    const b = new DiagramBuilder()
    const bn = b.termNode(b.root, p('y'))
    const b0 = b.wire(b.root, [{ node: bn, port: { kind: 'output' } }])
    const b1 = b.wire(b.root, [{ node: bn, port: { kind: 'freeVar', name: 'y' } }])
    const comp = mkDiagramWithBoundary(b.build(), [b0, b1])

    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const w0 = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const w1 = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'y' } }])
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const mk = (args: readonly string[]) => ({
      sel: mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] }),
      args,
    })
    expect(() => applyComprehensionAbstract(d, wrap, comp, [mk([w1, w0])]))
      .toThrowError(/does not match the comprehension/)
    expect(() => applyComprehensionAbstract(d, wrap, comp, [mk([w0, w1])])).not.toThrow()
  })

  it('rejects negative wrap regions, overlapping and out-of-wrap occurrences, by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('\\x. x'))
    const outside = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const wN = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === n))![0]
    const wO = Object.entries(d.wires).find(([, w]) => w.endpoints.some((ep) => ep.node === outside))![0]

    const negWrap = mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] })
    const negOcc = { sel: mkSelection(d, { region: cut, regions: [], nodes: [n], wires: [] }), args: [wN] }
    expect(() => applyComprehensionAbstract(d, negWrap, identityComp(), [negOcc]))
      .toThrowError(/requires a positive region/)

    const rootWrap = mkSelection(d, { region: d.root, regions: [], nodes: [], wires: [] })
    const outOcc = { sel: mkSelection(d, { region: d.root, regions: [], nodes: [outside], wires: [] }), args: [wO] }
    expect(() => applyComprehensionAbstract(d, rootWrap, identityComp(), [outOcc]))
      .toThrowError(/outside the wrapped content/)

    const h2 = new DiagramBuilder()
    const m = h2.termNode(h2.root, p('\\x. x'))
    const d2 = h2.build()
    const wM = Object.keys(d2.wires)[0]!
    const wrap2 = mkSelection(d2, { region: d2.root, regions: [], nodes: [m], wires: [] })
    const occ2 = { sel: mkSelection(d2, { region: d2.root, regions: [], nodes: [m], wires: [] }), args: [wM] }
    expect(() => applyComprehensionAbstract(d2, wrap2, identityComp(), [occ2, occ2]))
      .toThrowError(/occurrences overlap/)
  })

  it('with zero occurrences it wraps content in a vacuous bubble', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const wrap = mkSelection(d, { region: d.root, regions: [], nodes: [n], wires: [] })
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [])
    const bub = Object.entries(out.regions).find(([, r]) => r.kind === 'bubble')
    expect(bub).toBeDefined()
    expect(out.nodes[n]?.region).toBe(bub![0])
  })

  it('abstracts inside a doubly-cut (positive) region', () => {
    const h = new DiagramBuilder()
    const c1 = h.cut(h.root)
    const c2 = h.cut(c1)
    const n = h.termNode(c2, p('\\x. x'))
    const d = h.build()
    const w = Object.keys(d.wires)[0]!
    const wrap = mkSelection(d, { region: c2, regions: [], nodes: [n], wires: [] })
    const occ = { sel: mkSelection(d, { region: c2, regions: [], nodes: [n], wires: [] }), args: [w] }
    const out = applyComprehensionAbstract(d, wrap, identityComp(), [occ])
    const bub = Object.entries(out.regions).find(([, r]) => r.kind === 'bubble')!
    expect(bub[1].kind === 'bubble' && bub[1].parent).toBe(c2)
  })
})
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `npx vitest run tests/kernel/rules/comprehension-abstract.test.ts`
Expected: FAIL — `applyComprehensionAbstract` is not exported.

- [ ] **Step 3: Implement** — append to `src/kernel/rules/comprehension.ts` (and extend its imports: add `Endpoint` to the diagram type imports, plus the new modules below):

Extend the import block at the top of the file to:

```ts
import type { Diagram, DiagramNode, Endpoint, NodeId, Region, RegionId, Wire, WireId } from '../diagram/diagram'
import { DiagramError, mkDiagram } from '../diagram/diagram'
import { polarity } from '../diagram/regions'
import type { DiagramWithBoundary } from '../diagram/boundary'
import { mkDiagramWithBoundary } from '../diagram/boundary'
import type { SubgraphSelection } from '../diagram/subgraph/selection'
import { selectionContents } from '../diagram/subgraph/selection'
import { extractSubgraph } from '../diagram/subgraph/extract'
import { spliceSubgraph } from '../diagram/subgraph/splice'
import { boundaryFingerprint } from '../diagram/canonical/fingerprint'
import { freshId } from '../diagram/subgraph/freshId'
import { RuleError } from './error'
import { wireAt } from './access'
```

Then append:

```ts
export type AbstractionOccurrence = {
  readonly sel: SubgraphSelection
  /** Host wire serving as relation argument i — a permutation of the occurrence's attachment wires. */
  readonly args: readonly WireId[]
}

/**
 * Rule 8, abstraction direction: at a POSITIVE region, φ(G) may be replaced
 * by ∃R.φ(R) — wrap the selected content in a fresh bubble (double-cut
 * intro's reparenting, one bubble instead of two cuts; selected top-level
 * wires keep their scope: ∃x ∃R φ ⟺ ∃R ∃x φ) and replace each chosen
 * occurrence of G by an atom whose arg-i port lands on the occurrence's
 * argument-i wire. Consistency is exact: each occurrence's extracted pattern,
 * with its boundary reordered by args, must have the same boundary-pinned
 * fingerprint as the comprehension (equal pinned fingerprints iff isomorphic
 * respecting boundary order).
 */
export function applyComprehensionAbstract(
  d: Diagram,
  wrap: SubgraphSelection,
  comp: DiagramWithBoundary,
  occurrences: readonly AbstractionOccurrence[],
): Diagram {
  const wc = selectionContents(d, wrap) // validates the wrap selection loudly
  if (polarity(d, wrap.region) !== 'positive') {
    throw new RuleError(`comprehension abstraction requires a positive region; '${wrap.region}' is negative`)
  }
  const compFp = boundaryFingerprint(comp)
  const seenNodes = new Set<NodeId>()
  const seenRegions = new Set<RegionId>()
  const seenWires = new Set<WireId>()
  occurrences.forEach((occ, k) => {
    const c = selectionContents(d, occ.sel)
    if (!(occ.sel.region === wrap.region || wc.allRegions.has(occ.sel.region))) {
      throw new RuleError(`occurrence ${k} is anchored at '${occ.sel.region}', outside the wrapped content`)
    }
    for (const n of c.allNodes) {
      if (!wc.allNodes.has(n)) throw new RuleError(`occurrence ${k} node '${n}' is outside the wrapped content`)
      if (seenNodes.has(n)) throw new RuleError(`occurrences overlap at node '${n}'`)
      seenNodes.add(n)
    }
    for (const r of c.allRegions) {
      if (!wc.allRegions.has(r)) throw new RuleError(`occurrence ${k} region '${r}' is outside the wrapped content`)
      if (seenRegions.has(r)) throw new RuleError(`occurrences overlap at region '${r}'`)
      seenRegions.add(r)
    }
    for (const w of c.internalWires) {
      if (seenWires.has(w)) throw new RuleError(`occurrences overlap at wire '${w}'`)
      seenWires.add(w)
    }
    const { pattern, attachments } = extractSubgraph(d, occ.sel)
    if (occ.args.length !== attachments.length) {
      throw new RuleError(`occurrence ${k} has ${attachments.length} attachment wires but ${occ.args.length} argument positions`)
    }
    if (new Set(occ.args).size !== occ.args.length) {
      throw new RuleError(`occurrence ${k} argument wires are not distinct`)
    }
    const reordered = occ.args.map((a) => {
      const j = attachments.indexOf(a)
      if (j === -1) throw new RuleError(`occurrence ${k} argument wire '${a}' is not one of its attachment wires`)
      return pattern.boundary[j]!
    })
    const fp = boundaryFingerprint(mkDiagramWithBoundary(pattern.diagram, reordered))
    if (fp !== compFp) {
      throw new RuleError(`occurrence ${k} does not match the comprehension (boundary-pinned fingerprints differ)`)
    }
  })
  occurrences.forEach((occ, k) => {
    if (occ.sel.region !== wrap.region && seenRegions.has(occ.sel.region)) {
      throw new RuleError(`occurrence ${k} is anchored inside another occurrence's content ('${occ.sel.region}')`)
    }
  })

  const bubbleId = freshId(new Set(Object.keys(d.regions)), 'cm')
  const selectedRoots = new Set(wrap.regions)
  const regions: Record<RegionId, Region> = {
    [bubbleId]: { kind: 'bubble', parent: wrap.region, arity: comp.boundary.length },
  }
  for (const [id, r] of Object.entries(d.regions)) {
    if (seenRegions.has(id)) continue
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut'
        ? { kind: 'cut', parent: bubbleId }
        : { kind: 'bubble', parent: bubbleId, arity: r.arity }
    } else {
      regions[id] = r
    }
  }
  const selectedNodes = new Set(wrap.nodes)
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (seenNodes.has(id)) continue
    nodes[id] = selectedNodes.has(id)
      ? (n.kind === 'term'
        ? { kind: 'term', region: bubbleId, term: n.term }
        : { kind: 'atom', region: bubbleId, binder: n.binder })
      : n
  }
  const takenNodeIds = new Set(Object.keys(d.nodes))
  const atomIds = occurrences.map(() => {
    const id = freshId(takenNodeIds, 'cmAtom')
    takenNodeIds.add(id)
    return id
  })
  occurrences.forEach((occ, k) => {
    const anchor = occ.sel.region === wrap.region ? bubbleId : occ.sel.region
    nodes[atomIds[k]!] = { kind: 'atom', region: anchor, binder: bubbleId }
  })
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (seenWires.has(id)) continue
    const adds: Endpoint[] = []
    occurrences.forEach((occ, k) => {
      occ.args.forEach((a, i) => {
        if (a === id) adds.push({ node: atomIds[k]!, port: { kind: 'arg', index: i } })
      })
    })
    wires[id] = { scope: w.scope, endpoints: [...w.endpoints.filter((ep) => !seenNodes.has(ep.node)), ...adds] }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}
```

- [ ] **Step 4: Verify PASS, full suite, typecheck**

- [ ] **Step 5: Commit**

```bash
git add src/kernel/rules/comprehension.ts tests/kernel/rules/comprehension-abstract.test.ts
git commit -m "feat(kernel): comprehension abstraction at positive regions"
```

---

### Task 7: Barrel + cross-rule gate battery

**Files:**
- Modify: `src/kernel/rules/index.ts`
- Test: `tests/kernel/rules/equational-gates.test.ts`

- [ ] **Step 1: Write the battery** (must pass against Tasks 1–6; failures are rule bugs to fix test-first)

`tests/kernel/rules/equational-gates.test.ts`:

```ts
import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import {
  applyConversion, applyFusion, applyFission, applyUnfold, applyFold,
  applyComprehensionInstantiate, applyComprehensionAbstract,
} from '../../../src/kernel/rules/index'
import type { Definitions } from '../../../src/kernel/rules/index'

const consts = new Set(['I'])
const p = (s: string) => parseTerm(s, consts)
const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)
const defs: Definitions = { I: pp('\\x. x') }

function identityComp() {
  const b = new DiagramBuilder()
  const n = b.termNode(b.root, pp('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

describe('equational rules are polarity-free at depths 0..3', () => {
  for (let depth = 0; depth <= 3; depth++) {
    it(`depth ${depth}: conversion, fission/fusion, unfold/fold all apply`, () => {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, p('I ((\\x. x) y)'))
      const d = h.build()

      expect(() => applyUnfold(d, defs, n, ['fn'])).not.toThrow()
      expect(() => applyFold(applyUnfold(d, defs, n, ['fn']), defs, n, ['fn'], 'I')).not.toThrow()
      expect(() => applyConversion(d, n, p('I y'), 10)).not.toThrow()

      const split = applyFission(d, n, ['arg'])
      const newWire = Object.keys(split.wires).find(
        (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
      )!
      expect(diagramFingerprint(applyFusion(split, newWire))).toBe(diagramFingerprint(d))
    })
  }
})

describe('comprehension gates mirror insertion/erasure parity', () => {
  for (let depth = 0; depth <= 3; depth++) {
    const positive = depth % 2 === 0
    it(`depth ${depth} (${positive ? 'positive' : 'negative'}): abstract ${positive ? 'allowed' : 'rejected'}, instantiate ${positive ? 'rejected' : 'allowed'}`, () => {
      const h = new DiagramBuilder()
      let region = h.root
      for (let i = 0; i < depth; i++) region = h.cut(region)
      const n = h.termNode(region, pp('\\x. x'))
      const bub = h.bubble(region, 1)
      const d = h.build()
      const w = Object.entries(d.wires).find(([, wv]) => wv.endpoints.some((ep) => ep.node === n))![0]
      const wrap = mkSelection(d, { region, regions: [], nodes: [n], wires: [] })
      const occ = { sel: mkSelection(d, { region, regions: [], nodes: [n], wires: [] }), args: [w] }
      if (positive) {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ])).not.toThrow()
        expect(() => applyComprehensionInstantiate(d, bub, identityComp()))
          .toThrowError(/requires a negative bubble/)
      } else {
        expect(() => applyComprehensionAbstract(d, wrap, identityComp(), [occ]))
          .toThrowError(/requires a positive region/)
        expect(() => applyComprehensionInstantiate(d, bub, identityComp())).not.toThrow()
      }
    })
  }
})

describe('cross-rule composition', () => {
  it('unfold → convert → fold normalizes through a definition', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('I y'))
    const d = h.build()
    const unfolded = applyUnfold(d, defs, n, ['fn'])
    const { diagram: converted } = applyConversion(unfolded, n, p('y'), 10)
    const back = applyConversion(converted, n, p('(\\x. x) y'), 10).diagram
    expect(diagramFingerprint(applyFold(back, defs, n, ['fn'], 'I'))).toBe(diagramFingerprint(d))
  })
})
```

- [ ] **Step 2: Run; all must pass.** Any failure: investigate, fix test-first, report prominently.

- [ ] **Step 3: Extend the barrel** — `src/kernel/rules/index.ts` becomes:

```ts
export { RuleError } from './error'
export { applyInsertion, applyWireJoin } from './insertion'
export { applyErasure, applyWireSever } from './erasure'
export { applyIteration, applyDeiteration } from './iteration'
export { applyDoubleCutIntro, applyDoubleCutElim } from './doublecut'
export type { ConversionResult } from './conversion'
export { applyConversion, applyConversionByCertificate } from './conversion'
export { applyFusion, applyFission } from './fusion'
export type { Definitions } from './definitions'
export { applyUnfold, applyFold, assertWellFormedDefinitions } from './definitions'
export type { AbstractionOccurrence } from './comprehension'
export { applyComprehensionInstantiate, applyComprehensionAbstract } from './comprehension'
```

- [ ] **Step 4: Full gate** — `npx vitest run && npx tsc --noEmit`; verify every export exists.

- [ ] **Step 5: Commit**

```bash
git add tests/kernel/rules/equational-gates.test.ts src/kernel/rules/index.ts
git commit -m "test(kernel): equational gate battery; full rule surface"
```

---

## Completion criteria for this plan

- `npx vitest run` green, `npx tsc --noEmit` clean.
- Demonstrated in tests: conversion with same/vanished/added ports including named attachments and fresh singleton wires at the node's region (not root), fuel honesty, certificate replay and forged-certificate rejection; fusion's one-point-rule gates (two endpoints, output+freeVar shape, no self-loop, producer at the wire's scope) with shared-wire port merging and collision freshening; fission's bvar-closure gate and fission→fusion fingerprint identity at a nested region; unfold/fold round-trip with syntactic-match refusal pointing at rule 5; comprehension instantiation gated negative (copies per atom incl. identified arguments R(x,x), bubble dissolution, zero-atom case) and abstraction gated positive (pinned-fingerprint consistency incl. argument-order refusal, disjointness, wrap containment, nested-region bubble parent).
- Every rule follows the Plan 6 vocabulary invariant (RuleError ⇔ gate refusal on a real referent) and the root-bias lesson (each rule has at least one nested-region test).

## Carried obligations (forward)

- Plan 8: proof objects must store conversion certificates (`ConversionResult.certificate`); the theory store owns the `Definitions` environment and named comprehensions.
- Abstraction cannot express occurrences using one host wire as two relation arguments (extraction yields one stub per touching wire); instantiation handles that shape. Revisit if a proof needs the abstract direction with identified arguments.
- Plan 9 (or earlier if a second package appears): mechanical forbidden-import check (spec §4.2).
- Matcher symmetry-quotient + bare-wire pairing completeness wart (Plan 6 final review) if workloads hit them.
