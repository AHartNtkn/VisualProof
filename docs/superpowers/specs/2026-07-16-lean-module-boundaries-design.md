# Lean Module Boundary Reconstruction

## Outcome

Every maintained source file is at most 3,000 physical lines. The existing Lean
formalization remains the mathematical authority, all declarations retain one
implementation owner, and the former public monolith paths remain available only
as thin import umbrellas.

## Alternatives considered

1. Fixed-size line slicing was rejected. It would reduce file sizes but preserve
   accidental ownership and make imports encode arbitrary chronology.
2. A complete API redesign was rejected. The existing proved declaration surface
   is useful; replacing it would add semantic risk unrelated to the size defect.
3. Responsibility modules with dependency-chain imports is selected. It preserves
   theorem statements and declaration order while giving each file one coherent
   reason to change.

## Architecture

`Concrete/Subgraph/Splice.lean` becomes an import-only umbrella. Its
implementation moves beneath `Concrete/Subgraph/Splice/`:

- compiler traces and focused views;
- input quotienting and admissibility;
- plug-layout core, host transport, pattern transport, root compiler, occurrence
  compiler, and nested compiler;
- executable source/open correspondence;
- canonical reassembly;
- removal/plug commutation;
- examples;
- route and compiler alignment;
- focused environments and paired-presentation structure;
- paired compiler/context transport;
- intrinsic pattern simulation;
- final root and nested semantic soundness.

`Rule/Structural.lean` becomes an import-only umbrella. Spawn construction,
spawn semantic transport, open-root spawn lifting, wire operations,
double-cut/vacuous operations, iteration/erasure, and semantic laws receive
separate owners.

`Concrete/Elaboration/Compile.lean` becomes an import-only umbrella. The
executable occurrence compiler, region/root compiler, checked elaboration API,
certified beta-eta equivariance, public occurrence lifting, and examples receive
separate owners.

The new modules form explicit acyclic chains. A later module imports the narrow
earlier module it needs. No implementation is copied into the umbrella files.

## Enforcement

`scripts/check-source-size.mjs` recursively scans every repository-owned text
artifact, including ignored workflow artifacts. It excludes only version-control
metadata, external dependencies, compiler caches, and derived build directories,
and fails if any file has more than 3,000 physical lines.
`scripts/check-formalization.mjs` invokes it before the Lean build.

## Validation

- source-size audit reports zero violations;
- the three former monoliths contain imports only;
- every moved declaration occurs once;
- `lake build` succeeds;
- placeholder/axiom audit succeeds;
- proof-step correspondence and TypeScript typecheck succeed;
- active splice root soundness continues in the dedicated soundness module.

## Scope

This reconstruction changes module ownership and validation only. It does not
change diagram semantics, rule semantics, matcher scope, serialized proof-step
coverage, or completeness claims.
