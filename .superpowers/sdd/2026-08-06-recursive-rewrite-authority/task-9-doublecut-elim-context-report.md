# Task 9 DoubleCut elimination context report

Status: `DONE`

## Outcome

Added the structural whole-open nested elimination owner
`VisualProof/Refinement/Implementation/DoubleCutElimContext.lean`.

For a successful concrete elimination trace whose target is not the source root,
the public `nested_rule` theorem constructs the canonical raw-source to promoted-
target `Rule.DoubleCut`. The source endpoint is the checked source open diagram;
the target endpoint is the checked promoted target open diagram with its boundary
interface reconstructed in the original order. Receipt transport remains outside
this owner.

## Structural construction

The proof reconstructs source and target together along the unique distinguished
route:

- `RouteAlignment` pairs the source route with the promoted target route and
  proves completeness of the target route;
- surviving cut and bubble ancestors are rebuilt frame by frame, while sibling
  occurrences are transported by the promotion compiler and its local wire and
  occurrence equivalences;
- `compilerTraceContextIso` recurses only through the distinguished child and
  discharges cut/cut and bubble/bubble frames, with mixed constructors excluded
  by the promoted-region equations;
- `focusRuleAlignment` invokes the committed `DoubleCutElimCompile.focus` theorem
  at the terminal site and transports its hole relation through the paired leaf
  presentations;
- the root cut and bubble frames reconstruct both checked-open roots, including
  the ordered exposed and hidden interface wires; and
- `nested_rule` packages the source occurrence, target replacement context,
  boundary classes, and the polarity-selected orientation of the structural
  DoubleCut step.

The shared compiler owner now exports its canonical local wire and occurrence
equivalences and their specification theorems. Their sufficient hypothesis is
the exact surviving-region inequality needed by the paired route compiler;
existing compiler consumers continue to derive that inequality from their
stronger ancestry premise.

## RED/GREEN

The proof was developed through bounded owning-theorem stages. At every RED
compile, the single remaining production-theorem hole was the current owning
theorem; each stage was made kernel-checked before the next theorem was stated:

- paired descendant compiler trace alignment;
- terminal focused rule alignment;
- paired open-root trace alignment; and
- the final public `nested_rule` theorem.

GREEN: the shared compiler owner and the new context owner contain no `sorry`,
`admit`, or `axiom` declaration.

## Validation

- `lake env lean VisualProof/Refinement/Implementation/DoubleCutElimCompiler.lean`
- `lake env lean VisualProof/Refinement/Implementation/DoubleCutElimContext.lean`
- `lake build VisualProof.Refinement.Implementation.DoubleCutElimCompiler VisualProof.Refinement.Implementation.DoubleCutElimContext`
- `scripts/audit-lean-authority.sh roster`
- `scripts/audit-lean-authority.sh rules`
- `scripts/audit-lean-authority.sh implementation`
- `scripts/audit-lean-authority.sh proof`
- focused hole, forbidden-source, semantic-authority, and declaration-prefix
  scans
- `git diff --check`

All commands passed. The focused build and strict context compile emit non-failing
linter warnings only.

## Concerns

None.
