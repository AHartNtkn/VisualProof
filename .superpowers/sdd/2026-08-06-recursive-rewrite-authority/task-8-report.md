# Task 8 report: concrete representation laws

## Outcome

- `Concrete.checkOpen` validates the exact raw open input: it runs the existing
  flat well-formedness checker, validates every ordered boundary position as
  root-scoped, and returns a proof-carrying `OpenValidation` indexed by that
  input.
- `Concrete.translate` is exactly validation followed by the checked-open
  elaborator. `translate_checked` proves its checked-input computation law.
- `Concrete.encode` is a total recursive allocation into `Concrete.State`. Its
  boundary is generated position-by-position from the source boundary, so
  repeated positions retain their aliases.
- The encoder uses proof-carrying finite references. Its recursive allocation
  invariants prove well-formedness, exact region/wire ownership, binder scope,
  direct-occurrence provenance, and the local compiler inverse without a
  fallback index.
- Encoded elaboration is propositionally isomorphic to the source open diagram.
  The proof constructs the external-class equivalence from exposed-wire order,
  the root hidden-wire equivalence from the encoded local slice, and recursive
  `RegionIso`/`ItemSeqIso` witnesses from exact compiler success equations.
- `Represents` is successful `Concrete.translate` modulo
  `OpenDiagram.Isomorphic`; state representation, checked representation,
  uniqueness, and unconditional completeness use that single authority.
- Plan corrections `9aec272b` and `e2fccde6` precede this implementation and
  supply the exact-input `OpenValidation` and propositional isomorphism sorts.

## Theorem-driven development

- Encoded round trip RED: `Concrete.encode_elaborate_isomorphic` elaborated
  with its exact propositional statement and the owning proof as the only
  hole. GREEN: the recursive compiler inverse and root witness are
  kernel-checked with no hole.
- `encode_represents`, `checked_represents`, `represents_unique`, and
  `representation_complete` each passed an independent RED compile with its
  exact production declaration as the sole source `sorry`, followed by a
  strict GREEN compile after restoring the kernel-checked proof.

## Validation

- Strict owner compilation passed with empty output:
  - `lake env lean -DwarningAsError=true VisualProof/Concrete/Translate.lean`
  - `lake env lean -DwarningAsError=true VisualProof/Concrete/Encode.lean`
  - `lake env lean -DwarningAsError=true VisualProof/Refinement/Represents.lean`
- A direct audit imported `VisualProof.Refinement.Represents`, checked all
  validator, translator, encoder, state-translation, and representation
  signatures, and checked axioms for the public laws.
- `#print axioms` reported only Lean's standard `propext` and `Quot.sound`; no
  project axiom or `sorryAx` is present.
- `lake build` passed for the complete 307-job project graph. Existing
  non-strict lint warnings were replayed from other modules.
- Authority scans found one `Represents`, one `StateRepresents`, and the sole
  raw translation definition in `Concrete/Translate.lean`; the representation
  module refers to `Concrete.translate` rather than validation or elaboration
  as a second raw authority.
- Task-owner scans found no `sorry`, `admit`, `axiom`, matcher, candidate
  enumeration, occurrence search, compatibility representation, or
  `Concrete.elaborate` alias.
- `git diff --check` passed.

## Concerns

None.
