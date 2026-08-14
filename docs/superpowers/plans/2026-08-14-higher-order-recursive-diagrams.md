# Higher-Order Recursive Diagrams Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace second-order relation binders with recursively typed wires while preserving the recursive diagram decomposition, deriving every wire scope as the deepest common ancestor of its actual port occurrences, and migrating the existing relations and executable runners without changing their proof architecture.

**Architecture:** `Region`, `Item`, and `ItemSeq` remain the sole recursive syntax. A region receives an inherited typed wire context and introduces typed local wires; atoms and identities refer to those wires, cuts recurse, and there is no relation-context or bubble constructor. Recursive occurrence paths compute DCA, while `Region.Canonical` proves that each local wire is introduced at exactly that computed DCA; `OpenDiagram` bundles this evidence. There is no whole-diagram wire table, stored scope field, alternate syntax, or compatibility representation.

**Tech Stack:** Lean 4.30.0, Lake, recursive indexed inductives, theorem-driven RED/GREEN.

## Global Constraints

- Preserve the recursive `Region` / `Item` / `ItemSeq` ownership structure.
- Signatures are exactly `Sig.iota | Sig.rel (arguments : List Sig)`.
- Do not copy the TypeScript storage representation; use it only as semantic evidence.
- Do not retain `RelCtx`, `RelVar`, `RelationRenaming`, relation bubbles, or compatibility APIs.
- Do not add rule families. Migrate erasure, wire sever, iteration, double cut, vacuity, and comprehension.
- Scope is computed from recursive port-occurrence paths. A comment, naming convention, or unchecked local declaration is not scope evidence.
- Every locally introduced wire must have at least one occurrence and must have DCA equal to its introducing region.
- Existing semantic and rule-soundness proofs retain their recursive induction and case structure, with the bubble case removed and typed environments substituted for numeric environments.
- Every executable runner remains a direct computable definition. Proofs may be noncomputable.
- Do not add target search, occurrence discovery, raised heartbeat or recursion limits, `HEq` reconciliation APIs, parallel authorities, aliases, adapters, or fallbacks.
- If a migrated proof requires a new traversal rather than its existing structural induction, stop that task and revise the syntax boundary before proceeding.
- Every changed Lean module must pass `-DwarningAsError=true`; the full `lake build` and repository audits must pass before completion.

## Complexity Ledger

| Category | Selected responsibility |
|---|---|
| Essential behavior | Recursive diagrams, signature-correct ports, DCA wire scope, existing relations, direct runners |
| Essential state | Recursive items/cuts, inherited wire interface, locally introduced typed wires, port attachments, open boundary |
| Integrity constraints | Port signatures match wires; local wires are used; each local wire is introduced at its occurrence DCA; boundary wires occur at the root |
| Derived data | Port-occurrence paths, DCA, absolute scope path, scope depth/polarity, typed environments |
| Accidental state to remove | Relation contexts, relation variables, bubble binders, stored or asserted scope values |
| Accidental control to reject | Whole-diagram wire traversal, target search, proof-specific routing, reconciliation passes |
| Power leaks to reject | Generic global wire maps where recursive inherited/local renaming suffices; compatibility representations |

## Architecture Acceptance Gates

1. `Region.Canonical` must reject a parent-local wire whose occurrences are confined to one cut child.
2. It must accept a local wire used directly in its region or across distinct child cuts.
3. `OpenDiagram.scopePath` must be defined by DCA over actual occurrences, not by returning the declaration path.
4. The owner theorem must prove the computed scope of every internal wire equals its recursive owner path; boundary wires compute to the root because the boundary is surjective.
5. `Region.renameWires_id`, `RegionIso.refl`, and `denoteRegion_renameWires` must use the same structural recursors as the second-order versions, minus the bubble branch.
6. Failure of any gate blocks downstream migration and requires revising Task 1 rather than adding transport infrastructure.
7. Every current runner must construct a canonical target directly from its exact index. If an operation needs a separate wire-rehoming or scope-normalization traversal, the selected representation is rejected before that runner is migrated.

---

### Task 1: Define recursive typed syntax and prove DCA scope

**Files:**
- Create: `VisualProof/Theory/Signature.lean`
- Modify: `VisualProof/Diagram/Core.lean`
- Create: `VisualProof/Diagram/Scope.lean`
- Modify: `VisualProof/Diagram/Boundary.lean`

**Interfaces:**
- Produces `Sig`, `Var`, `Vars`, `WireRenaming`, recursive typed diagram syntax, recursive port paths, `Region.Canonical`, hierarchical wire identities, and computed `OpenDiagram.scopePath`.
- Does not expose a global wire context shared by every nested region.

- [ ] **Step 1: Add recursive signatures and typed variables**

  Implement:

  ```lean
  inductive Sig where
    | iota
    | rel (arguments : List Sig)

  structure Var (context : List Sig) (signature : Sig) where
    index : Fin context.length
    hasSignature : context.get index = signature

  def Vars (context : List Sig) : List Sig → Type
    | [] => PUnit
    | signature :: rest => Var context signature × Vars context rest

  structure WireRenaming (source target : List Sig) where
    apply : {signature : Sig} → Var source signature → Var target signature
  ```

  Add `Vars.get`, `Vars.map`, append-left/right embeddings, identity/composition laws, and `Sig.denote`/typed value declarations only when required by Task 3. Do not introduce numeric aliases for typed wires.

- [ ] **Step 2: Replace the recursive syntax in place**

  Define exactly:

  ```lean
  mutual
    inductive Region : List Sig → Type
      | mk {outer : List Sig} (locals : List Sig)
          (items : ItemSeq (outer ++ locals)) : Region outer

    inductive Item : List Sig → Type
      | atom {wires arguments : List Sig}
          (head : Var wires (.rel arguments))
          (ports : Vars wires arguments) : Item wires
      | identity {wires : List Sig} (signature : Sig) (arity : Nat)
          (ports : Fin arity → Var wires signature) : Item wires
      | cut {wires : List Sig} (body : Region wires) : Item wires

    inductive ItemSeq : List Sig → Type
      | nil : ItemSeq wires
      | cons : Item wires → ItemSeq wires → ItemSeq wires
  end
  ```

  Preserve `Region.localCount` only as the derived `locals.length` projection where a theorem genuinely needs a natural number. Do not store it independently.

- [ ] **Step 3: Define actual recursive port-occurrence paths**

  In `Scope.lean`, define `RegionPath := List Nat`, where each entry is the item index of a traversed cut. Define mutually recursive `Region.wirePaths`, `Item.wirePaths`, and `ItemSeq.wirePathsFrom` from atom-head, atom-argument, identity, and cut incidences. Direct node incidences contribute `[]`; entering a cut at item index `i` prefixes `i`.

  Define:

  ```lean
  def commonPrefix : RegionPath → RegionPath → RegionPath
  def deepestCommonAncestor : List RegionPath → RegionPath

  mutual
    def Region.Canonical : Region outer → Prop
    def Item.ChildrenCanonical : Item wires → Prop
    def ItemSeq.ChildrenCanonical : ItemSeq wires → Prop
  end
  ```

  For `.mk locals items`, require for every `local : Fin locals.length` that its embedded wire paths are nonempty and their DCA is `[]`, and require every cut child to be canonical.

- [ ] **Step 4: Bundle canonical open diagrams and compute scopes**

  Replace the numeric-arity boundary with:

  ```lean
  structure OpenDiagram (boundary : List Sig) where
    external : List Sig
    boundaryWire : Vars external boundary
    boundarySurjective : ∀ wire : Fin external.length,
      ∃ position : Fin boundary.length,
        (boundaryWire.get position).index = wire
    body : Region external
    canonical : body.Canonical
  ```

  Define hierarchical `OpenDiagram.Wire`: an external typed wire or a local typed wire identified recursively through cut ownership. Define `wireOccurrencePaths` from boundary and port incidences. Define `scopePath` only as `deepestCommonAncestor (wireOccurrencePaths wire)`.

- [ ] **Step 5: Prove the DCA owner theorems RED then GREEN**

  Enter only these owning theorem proofs as RED:

  ```lean
  theorem OpenDiagram.scopePath_external
      (diagram : OpenDiagram boundary) (wire : Var diagram.external sig) :
      diagram.scopePath (.external wire) = []

  theorem OpenDiagram.scopePath_internal
      (diagram : OpenDiagram boundary)
      (wire : diagram.body.InternalWire sig) :
      diagram.scopePath (.internal wire) = wire.ownerPath
  ```

  Prove them from `boundarySurjective` and `canonical`; do not define either theorem by owner-path projection. Add focused examples only as executable `decide` tests if the propositions are not already directly covered by these theorems.

- [ ] **Step 6: Run the foundation and adversarial architecture gates**

  Run:

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Theory/Signature.lean
  lake env lean -DwarningAsError=true VisualProof/Diagram/Core.lean
  lake env lean -DwarningAsError=true VisualProof/Diagram/Scope.lean
  lake env lean -DwarningAsError=true VisualProof/Diagram/Boundary.lean
  rg -n 'RelCtx|RelVar|RelationRenaming|bubble|scope[[:space:]]*:' \
    VisualProof/Theory/Signature.lean VisualProof/Diagram/Core.lean \
    VisualProof/Diagram/Scope.lean VisualProof/Diagram/Boundary.lean
  git diff --check
  ```

  The scan must find no displaced syntax or stored scope field. Review the three DCA acceptance cases before committing.

- [ ] **Step 7: Commit the foundation**

  ```bash
  git add VisualProof/Theory/Signature.lean VisualProof/Diagram/Core.lean \
    VisualProof/Diagram/Scope.lean VisualProof/Diagram/Boundary.lean
  git commit -m "replace relation bubbles with canonical typed wires"
  ```

### Task 2: Migrate recursive structural algebra without changing proof shape

**Files:**
- Modify: `VisualProof/Diagram/Rename.lean`
- Modify: `VisualProof/Diagram/Environment.lean`
- Modify: `VisualProof/Diagram/Context.lean`
- Modify: `VisualProof/Diagram/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Algebra.lean`
- Modify: `VisualProof/Diagram/RenamingIsomorphism.lean`
- Modify: `VisualProof/Diagram/ContextPathIsomorphism.lean`
- Modify: `VisualProof/Diagram/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Occurrence.lean`
- Modify: `VisualProof/Diagram/Replacement.lean`
- Modify: `VisualProof/Diagram/NestedOccurrence.lean`
- Modify: `VisualProof/Diagram/PortPartition.lean`

**Interfaces:**
- Consumes typed inherited/local wire contexts and `Region.Canonical`.
- Produces one typed renaming algebra, recursive cut-only contexts, recursive isomorphisms, contextual replacement, and typed port partitions.

- [ ] **Step 1: Replace numeric wire extension with typed append extension**

  Implement `WireRenaming.appendRight`, which maps inherited variables through the supplied renaming and local variables identically. Port the identity and composition theorems. Define `Region.renameWires`, `Item.renameWires`, and `ItemSeq.renameWires` with the existing mutual recursion and no bubble/relation branch.

- [ ] **Step 2: Prove the proof-shape sample gate**

  Port `Region.renameWires_id`, `Item.renameWires_id`, `ItemSeq.renameWires_id`, and composition using the current mutual recursor structure. If these require a whole-diagram traversal, a second wire representation, or heterogeneous reconciliation, stop and revise Task 1.

- [ ] **Step 3: Replace contexts and algebra structurally**

  `DiagramContext` has only `.hole` and `.cut` frames. Keep its inherited/local typed contexts and existing `fill`, `comp`, polarity, path, and replacement operations. Port `blank`, `conjoin`, `adjoinAt`, and `spliceAt` with typed wire renamings and no relation renaming parameter.

- [ ] **Step 4: Replace isomorphism data with typed wire equivalences**

  Define `WireEquiv source target` as a signature-preserving finite equivalence. Keep the existing region/item/item-sequence isomorphism constructors and recursive refl/symm/trans proofs, removing only relation equality and bubble cases. Prove that isomorphism preserves `Region.Canonical` and maps hierarchical wire identities while preserving computed scope depth and polarity.

- [ ] **Step 5: Migrate occurrences, replacements, and port partitions**

  Update `Occurrence`, `ContextReplacement`, `NestedOccurrence`, and port partitions to use typed contexts. Every body replacement must include or derive `Region.Canonical`; do not add an unchecked `withBody` entry point.

- [ ] **Step 6: Validate the structural closure and commit**

  Run strict checks in import order, then:

  ```bash
  lake build VisualProof.Diagram.PortPartition
  lake build VisualProof.Diagram.NestedOccurrence
  rg -n 'RelCtx|RelVar|RelationRenaming|Item\.bubble|DiagramContext\.bubble' \
    VisualProof/Diagram
  rg -n 'set_option (maxHeartbeats|maxRecDepth)' VisualProof/Diagram
  git diff --check
  ```

  Commit the green structural closure with `git commit -m "migrate recursive diagram algebra to typed wires"`.

### Task 3: Migrate higher-order semantics with the existing inductions

**Files:**
- Modify: `VisualProof/Model.lean`
- Modify: `VisualProof/Diagram/Semantics.lean`
- Modify: `VisualProof/Diagram/Semantics/Context.lean`
- Modify: `VisualProof/Diagram/Semantics/Isomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics/OpenIsomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics/ContextPathIsomorphism.lean`
- Modify: `VisualProof/Diagram/Semantics/ContextReachability.lean`
- Modify: `VisualProof/Diagram/Semantics/Algebra.lean`

**Interfaces:**
- Produces full recursively typed wire semantics and the existing semantic transport theorems.
- Uses no relation environment; relation values are ordinary values of relation signature wires.

- [ ] **Step 1: Define typed values and environments**

  Implement mutually:

  ```lean
  def Sig.denote (carrier : Type u) : Sig → Type u
    | .iota => carrier
    | .rel arguments => Values carrier arguments → Prop

  def Values (carrier : Type u) : List Sig → Type u
    | [] => PUnit
    | signature :: rest =>
        Sig.denote carrier signature × Values carrier rest
  ```

  Define `Env carrier context := Values carrier context`, typed lookup, append, renaming, and their identity/composition laws.

- [ ] **Step 2: Replace denotation directly**

  Keep the existing recursion:

  - `Region.mk locals items` existentially chooses `Env carrier locals` once;
  - `Item.atom head ports` applies the looked-up relation value to the looked-up typed argument tuple;
  - `Item.identity` requires all typed port values equal;
  - `Item.cut` negates recursive region denotation;
  - item sequences remain conjunction.

  There is no replacement case for bubble denotation because relation-signature locals use the same regional existential as every other wire.

- [ ] **Step 3: Port semantic transport theorem-by-theorem**

  For renaming, context, isomorphism, reachability, and algebra, retain each existing theorem’s mutual induction or context induction. Remove the bubble case and replace numeric environment extension with typed append. Do not introduce a compiler, normalization pass, or scope traversal into semantic proofs.

- [ ] **Step 4: Run the semantic architecture gate**

  Run:

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Diagram/Semantics.lean
  lake env lean -DwarningAsError=true VisualProof/Diagram/Semantics/Context.lean
  lake env lean -DwarningAsError=true VisualProof/Diagram/Semantics/Isomorphism.lean
  lake build VisualProof.Diagram.Semantics.Algebra
  rg -n 'RelEnv|bubble_denotes|set_option (maxHeartbeats|maxRecDepth)|HEq' \
    VisualProof/Diagram/Semantics.lean VisualProof/Diagram/Semantics
  git diff --check
  ```

  Commit with `git commit -m "interpret recursive signature wires directly"` only if the proof-shape gate passes.

### Task 4: Migrate the five recursive rule families and runners

**Files:**
- Modify: `VisualProof/Rule/Relation.lean`
- Modify: `VisualProof/Rule/Erasure.lean`
- Modify: `VisualProof/Rule/WireSever.lean`
- Modify: `VisualProof/Rule/Iteration.lean`
- Modify: `VisualProof/Rule/DoubleCut.lean`
- Modify: `VisualProof/Rule/Vacuity.lean`
- Modify: `VisualProof/Rule/Executable/Erasure.lean`
- Modify: `VisualProof/Rule/Executable/WireSever.lean`
- Modify: `VisualProof/Rule/Executable/Iteration.lean`
- Modify: `VisualProof/Rule/Executable/DoubleCut.lean`
- Modify: `VisualProof/Rule/Executable/Vacuity.lean`
- Modify: `VisualProof/Rule/Soundness/Erasure.lean`
- Modify: `VisualProof/Rule/Soundness/WireSever.lean`
- Modify: `VisualProof/Rule/Soundness/Iteration.lean`
- Modify: `VisualProof/Rule/Soundness/DoubleCut.lean`
- Modify: `VisualProof/Rule/Soundness/Vacuity.lean`
- Modify: `VisualProof/Rule/Step.lean`
- Modify: `VisualProof/Rule/Executable.lean`
- Modify: `VisualProof/Rule/Soundness.lean`

**Interfaces:**
- Retains the five `Rule.Step` constructors and both direct executable directions for each family.
- Replaces numeric wire maps by signature-preserving maps and derives scope checks from `OpenDiagram.scopePath`.

- [ ] **Step 1: Replace the generic rule boundary**

  Define:

  ```lean
  abbrev LocalRule : Type :=
    ∀ {wires : List Sig}, Region wires → Region wires → Prop

  abbrev Rule : Type :=
    ∀ {boundary : List Sig},
      OpenDiagram boundary → OpenDiagram boundary → Prop
  ```

  Preserve `Contextual`, `NestedContextual`, polarity handling, and isomorphism transport. Thread canonicality only where a new open diagram is constructed.

- [ ] **Step 2: Migrate structural rule statements**

  Erasure, iteration, double cut, and vacuity keep their recursive region replacements. Wire sever/join keeps the existing port-partition construction but partitions typed wires only within the affected recursive contexts. Every polarity condition reads the computed DCA scope; no index stores a scope.

  Represent vacuous introduction/elimination by the zero-port typed identity item at the selected region. Do not manufacture an unused local wire, because `Region.Canonical` correctly rejects one.

- [ ] **Step 3: Migrate direct runners**

  Keep each existing forward/backward index shape except for replacing numeric wires/scopes with exact typed hierarchical wire or occurrence witnesses. Each `run source index` must remain a direct computation with no search and return the exact constructed target.

- [ ] **Step 4: Port soundness and exact/isomorphic coverage**

  Retain each family’s current structural proof strategy. Update only typed wire plumbing and canonicality preservation. Keep the established coverage requirement: every relational instance is isomorphic to the result of the corresponding runner at an exact index, and runner outputs satisfy the relation.

- [ ] **Step 5: Validate and commit the five-family closure**

  Run strict checks for every family, then:

  ```bash
  lake build VisualProof.Rule.Executable
  lake build VisualProof.Rule.Soundness
  rg -n 'RelCtx|RelVar|RelationRenaming|Item\.bubble|scope[[:space:]]*:' VisualProof/Rule
  rg -n 'find\?|search|set_option (maxHeartbeats|maxRecDepth)' \
    VisualProof/Rule/Executable VisualProof/Rule/Soundness
  git diff --check
  ```

  Commit with `git commit -m "migrate recursive rules to computed wire scopes"`.

### Task 5: Replace comprehension by local relation-wire instantiation

**Files:**
- Modify: `VisualProof/Rule/Comprehension/Relation.lean`
- Modify: `VisualProof/Rule/Soundness/Comprehension.lean`
- Modify: `VisualProof/Rule/Laws.lean`

**Interfaces:**
- A quantified relation is a local wire with signature `.rel arguments` whose canonical DCA is the selected region.
- Comprehension replaces every head occurrence of that selected wire by a boundary-typed open pattern and removes the selected local wire.
- Non-head uses of the selected relation wire are excluded by the instantiation evidence.

- [ ] **Step 1: Define the selected local-wire boundary**

  Represent a selected local relation wire by a local-context split:

  ```lean
  before ++ Sig.rel arguments :: after
  ```

  The quantified region is:

  ```lean
  Region.mk (before ++ Sig.rel arguments :: after) quantifiedItems
  ```

  where `quantifiedItems` is indexed by the inherited wires appended with that local context. This identifies one exact rule instance without search.

- [ ] **Step 2: Port the mutual instantiation relation**

  Replace relation-environment mapping with typed wire substitution. Preserve the existing `RegionResult`, `ItemsResult`, and `ItemResult` recursion:

  - an atom headed by the selected local relation wire becomes the supplied open pattern with its ordered boundary attached to the atom arguments;
  - an atom headed by another relation wire is retained under the selected-wire removal renaming;
  - identities are retained only when none of their ports is the selected relation wire;
  - cuts recurse;
  - sequences conjoin results.

  The result owns its new typed local context and canonicality proof. Do not add a general substitution compiler.

- [ ] **Step 3: State and prove the local rule**

  Define `Comprehension.Local specialized quantified` from one `Instantiation.RegionResult`. Define `Comprehension := Contextual Comprehension.Local` with the same direction as the existing relation. Prove `Comprehension.iso` through `Contextual.iso`.

- [ ] **Step 4: Port comprehension soundness using typed semantics**

  Keep the current mutual semantic induction over instantiation evidence. The selected relation-wire value is the denotation of the supplied pattern; the atom-head case applies the boundary substitution theorem, and all remaining cases reuse the structural semantic lemmas from Task 3.

- [ ] **Step 5: Validate and commit comprehension**

  Run:

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Rule/Comprehension/Relation.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Soundness/Comprehension.lean
  lake build VisualProof.Rule.Soundness.Comprehension
  rg -n 'RelCtx|RelVar|RelationRenaming|Item\.bubble|Mapping\.lift' \
    VisualProof/Rule/Comprehension VisualProof/Rule/Soundness/Comprehension.lean
  git diff --check
  ```

  Commit with `git commit -m "replace comprehension bubbles with relation wires"`.

### Task 6: Remove displaced authority and validate the integrated calculus

**Files:**
- Remove: `VisualProof/Theory/Relation.lean`
- Modify: `VisualProof.lean`
- Modify: `VisualProof/Audit.lean`
- Modify: `VisualProof/ComputabilityAudit.lean`
- Modify: aggregate imports affected by Tasks 1–5

**Interfaces:**
- Leaves one recursive typed syntax, one computed scope function, one semantic interpretation, and the existing rule/executable families.

- [ ] **Step 1: Remove obsolete imports and authorities**

  Remove the relation-context module after the final consumer is migrated. Update aggregate imports and audits to name typed signature-wire declarations and computed scope theorems.

- [ ] **Step 2: Run strict owner checks and full validation**

  Run:

  ```bash
  lake env lean -DwarningAsError=true VisualProof/Diagram/Scope.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Soundness.lean
  lake env lean -DwarningAsError=true VisualProof/Rule/Executable.lean
  lake env lean -DwarningAsError=true VisualProof/ComputabilityAudit.lean
  lake build
  scripts/audit-lean-authority.sh roster
  scripts/audit-lean-authority.sh implementation
  scripts/audit-lean-authority.sh documentation
  rg -n 'RelCtx|RelVar|RelationRenaming|Item\.bubble|DiagramContext\.bubble' VisualProof
  rg -n 'set_option (maxHeartbeats|maxRecDepth)|HEq|compat|legacy' \
    VisualProof/Diagram VisualProof/Rule
  git diff --check
  ```

  All strict checks, the full build, and authority audits must pass. The displaced-model scans must be empty.

- [ ] **Step 3: Review the complexity ledger against the final code**

  Verify:

  - recursive local ownership remains the only wire ownership model;
  - DCA is computed from port paths and justified by canonicality;
  - no stored scope or global wire table exists;
  - semantic and soundness proofs retain their structural inductions;
  - no runner performs search;
  - no runner performs wire rehoming or scope normalization after constructing its target;
  - no parallel authority or compatibility surface remains.

- [ ] **Step 4: Commit the integration**

  ```bash
  git add VisualProof VisualProof.lean
  git commit -m "complete recursive higher-order diagram migration"
  ```

## Self-Review

- **Spec coverage:** Recursive typed syntax, bubble removal, DCA scope, unchanged rule families, two executable directions, isomorphism transport, and comprehension are assigned to Tasks 1–6.
- **Type consistency:** `List Sig` is the sole wire-context index; `Region outer`, `Item wires`, `OpenDiagram boundary`, `WireRenaming`, and typed environments use that same index throughout.
- **Architecture consistency:** Scope computation uses actual occurrences; canonicality is proof, not convention. Existing structural recursors remain the proof authority.
- **Rollback triggers:** New whole-diagram traversal in semantic/rule proofs, stored scope, target search, reconciliation APIs, or raised limits stop the active task and force reconsideration of the immediately preceding boundary.
