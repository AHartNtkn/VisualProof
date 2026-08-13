# Task 3B splice graft production report

## Outcome

`CompiledSite.splice` now constructs the canonical
`Diagram.ContextReplacement` for every successful `spliceRaw` execution and
packed receipt. Its only additional semantic input is
`Splice.Input.AttachmentConsistent`; executable admissibility is derived from
the successful operation.

The theorem derives both source focuses canonically, constructs the actual
target `CompiledRegion` under the receipt's root compiler call, and identifies
that result with `receipt.target.checked.compilation` by the two exact compiler
equations. The returned replacement projects to the source host context and
body and to the canonical `Region.spliceAt` graft.

## Responsibility model

- `CompilerCall` and `CompiledRegion` remain the only compiler authority.
- `CompiledSite.focus` remains the only source navigation authority.
- `compileAlongZipper` is one structural fold over that focus. Its recursive
  result contains the exact target compiler computation and one
  `DiagramContextIso`; it contains no target focus, route, occurrence search,
  or alternate target presentation.
- Each enclosing cut or bubble compiles its nonfocused siblings and adds one
  aligned `DiagramContextIso` frame. Prefix sequences and wire-length
  normalization remain local to that constructor.
- The endpoint construction owns the concrete four-block compiler order and
  its single braid to `Region.spliceAt`.
- `DiagramContextIso.fill` applies the endpoint `RegionIso` once after the fold;
  the root packages the resulting body isomorphism once.

## Supporting boundaries

`DiagramContextIso.cutCompilerFrame` and `bubbleCompilerFrame` accept the
compiler-native full-context equivalence and eliminate their outer/local
length equalities internally. This keeps dependent wire-index normalization
out of the recursive state.

`CompiledSite.splice_context`, `splice_before`, and `splice_after` expose
ordinary projection equations for consumers.

## Complexity audit

Essential state carried by the fold is limited to:

- the source compiler call and result selected by the canonical zipper;
- the target call's outer/local contexts and binders;
- exact lexical/compiler evidence for that call; and
- the endpoint graft maps and canonical local body.

Derived and constructor-local values include sibling blocks, target items,
wire equivalences, and context frames. No prefix, split equality, or prefix
isomorphism crosses the recursive boundary. Cut and bubble are the two direct
grammar cases of the single fold rather than separate root/region traversals.

The implementation has no target search, target route, configurable
simulation, recursive callback API, compiled-result cast, `HEq` boundary, or
raised elaboration limits. Default heartbeat and recursion limits are part of
the architecture gate: exceeding them is treated as evidence that recursive
state or dependent bookkeeping has leaked across the context boundary.

## Validation

Seven production modules were checked directly with warnings as errors and
zero diagnostics. The focused `CompiledSite.splice`/elaboration/encode build
passed 54 jobs, and the full project build passed 103 jobs. The task closure
was scanned for admissions and scaffolding, forbidden target-navigation and
simulation authorities, result-tree casts, and elaboration-limit overrides.
All three repository authority audits and `git diff --check` passed.
