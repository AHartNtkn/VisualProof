# T003 structural proof closure

## Controlling rule

Each structural owner must be a coherent port of one completed predecessor
operation and its complete proof dependency chain. Existing code is retained
only after substantive declaration comparison. Greenfield operation,
factorization, compiler-simulation, carrier, contraction, transport, or
embedding machinery is forbidden when a predecessor already owns the
responsibility.

## Owner map

| Production owner | Selected completed predecessor | Permitted changes | Status |
|---|---|---|---|
| `atomSpawn_sound` | SO structural insertion/compiler simulation, with the completed HO atom insertion semantic kernel | Recursive signatures and the existing head-wire endpoint; remove lambda, relation-binder, named-reference, receipt, and normalization cases | GREEN |
| `identityInsert_sound` | Same SO structural insertion/compiler simulation, with the completed HO identity insertion semantic kernel | Identity content and recursive signatures; remove obsolete content/wrappers | GREEN |
| `erasure_sound` | SO selection/removal/compiler projection and HO erasure direction | Atom/identity/cut specialization and ordered-open boundary | GREEN |
| `iteration_sound` | HO `CheckedOrdinaryIteration` extraction, raw splice, insertion/factorization, equivalence, and soundness chain | Current macro-free atom/identity/cut representation; remove definition/ref/normalization/provenance/transport/checker packaging not owning mathematics | RED |
| `deiteration_sound` | Re-audit after iteration against HO `CheckedOrdinaryDeiteration` and SO reinsertion | Select one chain before porting | RED |
| `doubleCutIntro_sound`, `doubleCutElim_sound` | SO intrinsic double-cut and modal compiler simulation | Recursive signatures and macro-free content | RED |

Iteration is governed by
`notes/iteration-declaration-audit.md`. The abandoned signature-indexed HO
implementation is the selected iteration proof architecture. The SO tree is
used only for localized current representation facts.

## Retained shared ports

- `ConcreteElaboration.SiteFrame`, `compileRootFrame?`, its generated/complete
  equations, and the cut-depth equation are the macro-free SO compiler-context
  route.
- `Region.Context.denote_plug_iff` is the SO contextual semantic lift.
- iteration-owned extraction, splice/insertion, factorization, and semantic
  declarations are not currently classified as retained. Each must be
  re-audited against one exact HO declaration after the bespoke `copySelection`
  operation is removed.
- `Region.adjoinAt` and its semantic declarations must likewise be retained only
  if direct comparison establishes an exact selected-HO downstream use.
- intrinsic double-cut semantics is already the direct SO port.

## Deleted path

The prior deletion of `OpenCompilation`, `SpliceRaw`, and `Factorization*` was
not evidence that their mathematical kernels were obsolete. Those kernels are
selected predecessor work and must be ported where the terminal dependency
chain consumes them. Only excluded wrappers and unrelated macro consumers stay
deleted.

## Completion condition

`iteration_sound` must be GREEN with a kernel-checked proof obtained from the
coherent HO operation and complete terminal dependency chain. Then run the focused
dependency build, full build, axiom audit, exact sorry inventory, source-size
gate, displaced-architecture scan, fixture/example/check scan, and diff-hygiene
checks. If an exact HO declaration cannot be adapted, record its exact statement
and the precise incompatible hypothesis or conclusion before any alternative is
written.
