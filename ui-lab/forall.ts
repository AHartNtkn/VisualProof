/**
 * LAW DEMO — first-order universal quantification. ∀x (P(x) ∧ Q(x)) is
 * ¬∃x ¬(P(x) ∧ Q(x)): the individual's line is quantified in the annulus
 * between the two cuts while both its ports sit inside the inner one.
 * USER rendering rule: the line connects its ports naturally and a dangling
 * ∃ node homed at the SCOPE carries the quantifier — the line never contorts
 * through the annulus. Compare the plain ∃ next to it: same two predicates
 * on the sheet, loose end quantified right there.
 */
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { boot, installBrush } from './shared'

boot('Law demo — ∀ via the dangling ∃', '∀x (P x ∧ Q x): the line lives in the inner cut, its ∃ dangles in the annulus; beside it, a plain sheet-level ∃', (lab) => {
  installBrush(lab)
}, () => {
  const b = new DiagramBuilder()
  // ∀x (P(x) ∧ Q(x)) — double cut, ports inside, wire scoped at the annulus
  const c1 = b.cut(b.root)
  const c2 = b.cut(c1)
  const pn = b.ref(c2, 'P', 1)
  const qn = b.ref(c2, 'Q', 1)
  b.wire(c1, [
    { node: pn, port: { kind: 'arg', index: 0 } },
    { node: qn, port: { kind: 'arg', index: 0 } },
  ])
  // ∃x (P(x) ∧ Q(x)) — same shape on the sheet, quantified where it lives
  const pn2 = b.ref(b.root, 'P', 1)
  const qn2 = b.ref(b.root, 'Q', 1)
  b.wire(b.root, [
    { node: pn2, port: { kind: 'arg', index: 0 } },
    { node: qn2, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), boundary: [] }
})
