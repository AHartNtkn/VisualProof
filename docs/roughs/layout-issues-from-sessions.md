# Layout issues from the 2026-07-28 sessions

Source: two incomplete sessions in the signature-indexed-wires worktree
(`~/.claude/projects/-home-ahart-Documents-VisualProofAssistant--worktrees-signature-indexed-wires/`):

- `311c20c3-7169-425c-8db2-b67049d69898.jsonl`
- `43a62de3-6d36-483b-af49-57142d3222de.jsonl`

## Session 311c20c3 — animation-system issues

1. **No energy penalty for wires entering cuts they are never inside of.** Wires
   sometimes settle in positions where they enter and exit a cut they do not
   belong to.
2. **Jerky wire animation.** Everything else animates smoothly toward new
   configurations, but wires snap to new positions quickly, or lag at old
   positions and then snap to catch up.

The session ended mid-diagnosis ("Now the animation probe") — a background run of
`scratchpad/probe-wirejerk.ts` was killed (exit 143). No fix was made.

## Session 43a62de3 — annealing search issues

1. **Global-only acceptance scrambles organized regions.** The searcher accepts a
   hop when total energy drops, even when one region gets scrambled to organize
   another. Measured in that session: reverting the parts a move never touched
   beats the accepted state on ~40% of accepted hops.
2. **Large scenes stall for minutes in their initial configuration.** Measured
   cause (end of session): the searcher never reaches annealing at all — one
   `settleStep` on the 70-body scene (`successorShiftCarrierInductive@219`,
   1260 drawn segments) takes 75 s. The cost is the acceptance gate: the
   coordinate fallback in `operatorStep` (relax.ts, ~1345–1358 at that commit)
   calls whole-scene `wireEnergy + contentEnergy` (~84 ms) once per coordinate
   per trust-region rung ≈ ~890 whole-scene routed evaluations per settle step.
   With `RELAX_PUBLISH_STEPS = 50`, one publish quantum of the initial descent is
   ~1 hour on that scene.
3. **Diagnosed direction, not implemented:** standard Metropolis evaluates the
   energy change over the affected neighborhood only; here every acceptance
   decision (descent gate and hop test alike) is a whole-scene evaluation, so
   per-decision cost is O(scene) and explodes with graph size.

Other measured scenes: `associativityCarrierHereditary@166` (896 segments,
20.4 s/step), `plusComm@53` (770 segments, 13.8 s/step).

## Related uncommitted material

The signature-indexed-wires worktree has uncommitted diagnostic probes in
`scratchpad/` (`probe-wirejerk.ts`, `probe-stall.ts`, `probe-falserest.ts`,
`probe-blockdelta.ts`, …). They are not on the branch this worktree was cut
from; copy them over if needed.
