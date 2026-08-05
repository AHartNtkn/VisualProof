# Whole-Development Two-Predecessor Audit

## Authority and classifications

- Complete second-order authority: Git commit `2bddfe4`.
- Abandoned signature-indexed authority:
  `/tmp/vpa-current-lean-code-20260804-XO7NPu`.
- Current production tree: the only target architecture.

Every production responsibility is classified below as one of:

- **completed port**: the current GREEN owner already implements the same
  responsibility after deleting obsolete representation cases;
- **minor port pending**: a complete predecessor construction or proof exists,
  and only current representation and wrapper removal may change;
- **partial predecessor**: completed cases exist, but a named theorem or bridge
  is honestly unfinished;
- **new**: the responsibility is absent from both predecessors.

Constructor deletion, recursive signatures, removed definition indices, and
replacement of receipts by direct accepted candidates are porting changes.
They do not authorize a new proof design. Receipts, normalization,
canonicalizer orchestration, provenance ledgers, generic public transport,
search, atlases, fixtures, macros, and public compilers are not production
owners.

## Full-surface re-audit checkpoint (2026-08-05)

This checkpoint was performed after extraction exposed a broader process
failure: predecessor comparison had to govern the whole development, not only
the module currently blocking a proof.  The current production tree contains
68 Lean modules and 35 `sorry` occurrences. Every `sorry` is an owning
production theorem and is reconciled below.  No remaining definition is an
authorized implementation task.

### Current production-module coverage

| Current owner group | SO comparison surface | Abandoned HO comparison surface | Re-audit result |
|---|---|---|---|
| import barrels `VisualProof.lean`, `Diagram/Concrete.lean`, `Diagram/Concrete/Subgraph.lean`, `Rule/Structural.lean`, and `Rule/Operations.lean` | corresponding SO barrels | corresponding HO import surfaces where present | **completed dependency surface**; these add no independent mathematical owner |
| `Data/Finite.lean` | same module | same module | **completed shared port**; retain the current finite-carrier utilities |
| `Sig.lean`, `Model.lean` | old second-order indices and `LambdaModel` provide architecture only | same modules provide recursive signatures, typed variables, full models, and carrier nonemptiness | **completed HO port**; no implementation remains |
| intrinsic `Diagram/{Core,Semantics,Rename,Algebra,Context,Boundary,Isomorphism,OpenIsomorphism}.lean` | same modules provide the recursion, renaming algebra, one-hole contexts, parity, and isomorphism proofs | `Core`, `Semantics`, `Context`, `ContextOuter`, and `ContextZipper` provide signature-indexed atom/identity/cut cases | **completed combined port**; only obsolete lambda, binder-constructor, named/ref, and definition cases were removed |
| checked graph `Concrete/{Core,WellFormed,Open,Semantics,Isomorphism}.lean` | same checked-graph and denotation architecture | same or corresponding dense/open isomorphism modules provide signature-indexed carriers | **completed combined port**; current ordered boundary and `CheckedIso.denote_iff` are GREEN |
| elaboration `Concrete/Elaboration{,/Compile,/Context,/Simulation}.lean` | complete generic simulation architecture | selected HO site/relative-frame and insertion-compilation owners | current shared declarations require exact HO downstream-use audit before iteration reuse |
| occurrence and subgraph `Selection`, `Extract`, `Extraction`, `Reindex`, `Remove`, `Copy` | localized current-representation evidence | selected HO `CheckedExtraction`, raw splice, insertion, and factorization chain | removal retains its separate audit; current iteration copy/extraction declarations remain only when the HO declaration audit proves equivalence |
| iteration splice owner | localized public-surface and representation evidence | completed HO `ConcreteSpliceAttachment`, `spliceRaw`, `InsertionCompilation`, `Factorization*`, and `CheckedOrdinaryIteration.equivalence`/`.sound` | **HO port in progress**: `IterationSplice` is the audited canonical-extraction specialization of the raw carrier/result and is GREEN; the copied-fragment simulation remains displaced; insertion/factorization and terminal owners remain to port |
| `Theory/Semantics.lean` | same open implication/equivalence semantics | same semantic responsibility with obsolete definition indices | **completed macro-free port** |
| `Rule/{Core,Operations,Step}.lean` and `Rule/Soundness/Core.lean` | rule orientation, application, step, and semantic-soundness architecture | `Orientation`, `Tag`, `Step`, structural and wire operation dispatchers | **completed reconstruction** of the exact 31-rule macro-free surface |
| `Rule/Structural/{Spawn,Identity,Iteration,Modal}.lean` | localized structural architecture | completed insertion, identity, and `CheckedOrdinaryIteration` kernels | spawn, identity, erasure, and modal operations retain their separate audit results; iteration must be replaced by the selected HO chain |
| `Rule/Structural/Semantics.lean` and `Rule/Soundness/{IdentityInsertion,VacuousElaboration*}.lean` | structural semantic lemmas, generic compiler simulation, modal/vacuous proof closure | insertion, modal/vacuous, and factorization semantic closures | **partially completed minor ports**: double-cut intrinsic semantics, vacuous soundness, directional simulation, and identity site projection are GREEN; terminal ordinary structural owners remain the named ports below |
| `Rule/WirePrimitive{,/Partition,/Content,/ArgumentsArity,/ArgumentsPermute,/ArgumentsCore,/ArgumentsDropExtend,/Leaves,/Operations}.lean` | only older structural or bubble-era architectural precedents | same family modules contain the exact completed signature-indexed transformations and terminal soundness proofs | **all nineteen operation definitions completed**; only their proof closures and terminal owners remain minor ports |
| `Rule/Soundness/{Structural,Identity,WirePrimitive}.lean` and aggregate `Rule/Soundness.lean` | complete ordinary structural and dispatcher architecture | complete signature-indexed structural, identity-transformation, and wire-primitive terminal kernels | **26 RED delegated owners plus a GREEN exhaustive 31-case dispatcher**; every delegated proof is a predecessor port |
| `Proof/{Replay,Theorem,Theory}.lean` | same complete induction/composition proofs | replay/program composition confirms the dependent-chain kernel | **five RED minor mechanical ports**; remove definition/citation parameters, not the proof architecture |
| `Formula/{Syntax,Semantics,Soundness}.lean` | explicit absence | explicit absence | **genuinely new family**; syntax and semantics definitions are complete, and only `semantically_complete` remains RED |
| `Rule/WirePrimitive/Direct.lean` | occurrence/extraction/removal mathematics only | monolithic join/sever raw carrier equations | **completed representation-independent specification port**; no checker/compiler API is required |
| `Rule/WirePrimitive/Program.lean` | replay induction | `runPrimitiveProgram_sound` | **one RED minor mechanical port** |
| `Rule/WirePrimitive/Adequacy.lean` | reusable occurrence/extraction/removal kernels | completed residual/plumbing/inversion/landing cases, but `compiled_join_redundant` and `compiled_sever_redundant` are themselves `sorry` | **two RED partial-predecessor owners**; reuse completed cases and prove only the named bridge, totality, and landing gaps |

The file-name comparison is not treated as proof of equivalence.  Current
modules whose names do not occur in one predecessor are mapped to the exact
responsibility owners in the other column.  In particular, current
`Subgraph/Extraction.lean`, `Subgraph/Copy.lean`, and the split soundness files
do not become greenfield work merely because the predecessor packaged the
same mathematics under `Extract`, splice/factorization, receipt, or monolithic
modules.

### Exact current RED reconciliation

| Count | Current owning theorems | Classification |
|---:|---|---|
| 4 | `iteration_sound`, `deiteration_sound`, `doubleCutIntro_sound`, `doubleCutElim_sound` | minor structural ports from the exact SO/HO owners below; `atomSpawn_sound`, `identityInsert_sound`, and `erasure_sound` are GREEN |
| 3 | `identityDegeneracy_sound`, `identityCollapse_sound`, `identityFusion_sound` | minor HO transformation-proof ports |
| 19 | every theorem in `Rule/Soundness/WirePrimitive.lean` | minor HO terminal-proof ports |
| 3 | `replay_sound`, `replay_forward_sound`, `replay_backward_sound` | minor SO replay-induction ports |
| 1 | `checkedTheorem_sound` | minor SO composition port |
| 1 | `verifiedTheory_sound` | minor SO verified-list induction port |
| 1 | `WirePrimitive.Program.sound` | minor HO `runPrimitiveProgram_sound` port |
| 2 | `relationSubstitution_complete`, `relationComprehension_complete` | partial predecessor; completed construction cases plus named missing terminal bridges |
| 1 | `Formula.semantically_complete` | genuinely new existential theorem |
| **35** | complete current `sorry` inventory | no other RED or implementation owner exists |

### Live predecessor revalidation

The whole-tree comparison was rerun on 2026-08-05 against the actual three
surfaces, not inferred from filenames or the extraction audit:

- current production: 68 Lean modules and the 35 RED declarations listed
  above;
- SO `2bddfe4`: 362 Lean modules; the named structural, replay, checked-theorem,
  and verified-theory proof files contain no `sorry`;
- abandoned HO backup: 178 Lean modules below `VisualProof/`, plus the root
  `VisualProof.lean` barrel; the named structural, identity, and nineteen
  wire-primitive proof files and their mathematical lower closures contain no
  `sorry`.

The abandoned HO backup has exactly six `sorry` declarations. Two are the
terminal `compiled_join_redundant` and `compiled_sever_redundant` declarations;
their two semantic corollaries are consequently also RED, and the fifth is an
excluded receipt owner for the old macro-bearing `ProofStep`. The separate RED
`insertion_redundant` theorem is the sixth; it is in an excluded
macro/derived-rule file and is
not a predecessor for any current owner. This confirms that R5 is only a
partial-predecessor port while the primitive operation and primitive soundness
families themselves are complete. Searches of both predecessors still find no
formula syntax, semantics, or semantic-expressiveness theorem. Thus the
classification boundary remains: completed current owners are retained; 32
remaining declarations are minor predecessor ports; two R5 declarations reuse
partial predecessor work with named gaps; and one formula theorem is genuinely
new. No definition or operation is pending reimplementation.

Before any one of these owners is changed, its row below is the mandatory
starting point. If the named kernel does not adapt, the failure record must
identify the exact incompatible hypothesis or conclusion; a different proof
construction is not the default response.

This gate also applies below the terminal RED declarations. A new helper is
authorized only as a current-representation statement of a named predecessor
premise, or as a projection/equation exposing an already-completed current
operation to that premise. Existing GREEN code is retained only after the
same responsibility comparison; compilation and current consumers alone are
not reuse evidence.

### Responsibility-level lower-closure audit

The audit unit is the mathematical responsibility, not the filename or final
one-line theorem. In particular, the abandoned HO terminal wire theorems are
short because their completed proofs are stored in lower construction,
factorization, semantic-ledger, inverse, and denotation modules. Those lower
proofs are predecessor work. Their absence from the current tree never
authorizes a fresh construction.

| Current responsibility | Completed SO material to adapt | Completed abandoned-HO material to adapt | Disposition |
|---|---|---|---|
| intrinsic syntax, denotation, renaming, contexts, and polarity | `Diagram/Core.lean`, `Semantics.lean`, `Rename.lean`, `Algebra.lean`, and `Context.lean` | `Sig.lean`, `Model.lean`, `Diagram/Core.lean`, `Semantics.lean`, `Context.lean`, `ContextOuter.lean`, and `ContextZipper.lean` | current GREEN combined port; retain atom/identity/cut and existential-local kernels, delete lambda, bind-constructor, named/ref, and definition indices |
| checked graph, open denotation, elaboration, and isomorphism | SO `Diagram/Concrete/{Core,WellFormed,Open,Semantics,Isomorphism}.lean` and `Elaboration/**` | HO `Concrete/{Core,WellFormed,OpenCompilation,Isomorphism,OpenIsomorphism}.lean` and `Elaboration{Kernel,Support,Completion,NodeCompletion,Denotation,Invariance,Transport}.lean` | current GREEN combined port; any additional simulation lemma must be a specialization of these owners |
| selection, extraction, removal, copy, and structural factorization | SO modules provide localized current-representation evidence | HO `CheckedExtraction`, `OpenCompilation`, `ConcreteSpliceAttachment`, `SpliceRaw`, `Factorization*`, and structural equivalence kernels | HO is the coherent iteration basis; current iteration declarations are displaced unless exact HO equivalence and downstream use are established |
| atom spawn and identity insertion | SO `SpawnCore.lean`, `SpawnOpen.lean`, `SpawnTransport.lean`, compiler simulation, and terminal structural soundness | HO `StructuralInsertionInput`, `checkStructuralInsertion`, `StructuralInsertionReceipt.negative_splice_sound`, and `.sound` | operation and terminal proofs already GREEN; retained as audited adaptations |
| erasure | SO removal, compiler projection, polarity, reassembly, and terminal `applyErasure_sound` | HO `StructuralErasureInput`, `StructuralErasureReceipt`, and `.sound` | operation and terminal proof already GREEN; retained as audited adaptation |
| iteration/deiteration | SO supplies localized public-surface and region representation facts | HO `CheckedOrdinaryIteration` and `CheckedOrdinaryDeiteration` complete operation and semantic chains | iteration ports the HO graph as one unit with obsolete wrappers removed; deiteration is re-audited separately after iteration |
| double cut and vacuous wire | SO modal compiler/focused/root/boundary simulations and terminal owners | HO intrinsic `doubleCut`, `denote_doubleCut`, `CheckedDoubleCut.equivalence`, `.intro_sound`, `.elim_sound`, and vacuous counterparts | vacuous is GREEN; double-cut landing and two terminal owners are minor ports |
| identity degeneracy/collapse/fusion | no authoritative SO transformations | HO `IdentityIncidence.lean`, `IdentityNormalizationCore.lean`, and the three `IdentityNormalization{Drop,Collapse,Fusion}{WellFormed,Semantics}.lean` families | current candidates are completed transformation-only adaptations; port the completed proof chains, never the canonicalizer, normalization loop, or transport layer |
| wire sever/join | only generic SO wire/context architecture | HO `Concrete/WirePartition.lean`, `WirePartitionIsomorphism.lean`, `WirePartitionSemantics.lean`, and `Rule/WirePrimitive/Partition.lean` | current raw candidates are completed carrier-level adaptations; the construction/isomorphism/denotation chain and terminal proofs are a minor port |
| cut wrap/absorb, parallel split/fuse, ends delete/spawn | only generic SO removal/context architecture | HO raw `WirePrimitive/Content.lean`, `Content{Alignment,EmptyCore,EmptySemantics,EndsSemantics,Origin,Semantics,ShapeSemantics}.lean`, `ExhaustedWireEquivalence.lean`, `UniformSiteFactorization.lean`, `Rule/WirePrimitive/{Content,ContentWitnesses}.lean` | current candidates choose simpler current carriers but implement the same transformations; port the completed semantic and inverse kernels rather than rebuilding them |
| arity shift/unshift, permutation, duplicate/contract, drop/extend | only generic SO context/renaming architecture | HO `Arguments{CommonCore,Construction,ConstructionCore,ConstructionNaturality,Operations,Semantics,TupleSemantics,FixedSemantics,FrameNaturality,SiteFactorization}.lean`, the `ArgumentsCylindrification*` family, and the five `Rule/WirePrimitive/Arguments*.lean` owners | current in-place candidates are completed carrier adaptations of the predecessor replacement construction; every semantic, inverse, and terminal obligation is a minor port |
| formal/identity leaf and abstraction | no exact SO rule inventory | HO raw `WirePrimitive/{Leaves,LeavesSemantics}.lean` and `Rule/WirePrimitive/Leaves.lean` | current macro-free candidates retain formal and identity cases and delete ref cases; proof closure is a minor port |
| aggregate step, replay, checked theorem, verified theory, and primitive program | SO exhaustive structural dispatcher plus `Proof/{Replay,Theorem,Theory}.lean` | HO exhaustive primitive dispatch and `runPrimitiveProgram_sound` | retain the completed dependent inductions/compositions after deleting citation, definition context, normalization, and receipt transport |
| direct substitution/comprehension adequacy | SO occurrence/extraction/removal kernels only | HO `CompilerTermination.lean`, completed construction cases in `Compiler.lean`, inverse-step and raw landing tables; terminal redundancy theorems remain RED | reuse the completed proof-local construction; new work is only the named bridge, totality, and exact landing gaps |
| formula semantic expressiveness | absent | absent | sole wholly new theorem family |

For each pending rule family, implementation must begin by tracing the exact
predecessor theorem dependency chain through the lower-closure row above. A
current helper is permitted only when it is the current representation of one
of those premises or exposes a field of an already-completed current
candidate. It is not enough to cite the terminal theorem and independently
prove whatever lies beneath it.

### Declaration-level execution gate

The following is the exhaustive disposition of the unfinished production
surface. It is the required starting point for implementation, not a suggested
source list.

| Current declaration(s) | Exact completed predecessor owner | Retained kernel and permitted delta |
|---|---|---|
| `iteration_sound` | Selected HO graph rooted at `ConcreteSpliceAttachment`, `RawConcreteSpliceResult`, `spliceRaw`, `InsertionCompilation`, `Factorization*`, and the local kernel used by `CheckedOrdinaryIteration.equivalence`; SO `iterationInput`/`applyIteration_sound` verify the public responsibility | Specialize the HO fragment/attachment input by canonical selection extraction, use the pre-normalization raw factorization, delete definition/ref/receipt/closed wrappers, and apply the same local equivalence pointwise over the current ordered boundary. |
| `deiteration_sound` | SO `deiteration_sound_of_reinsert` and `applyDeiteration_sound`; HO `CheckedOrdinaryDeiteration.sound` and `.equivalence` | Re-audit after the shared iteration replacement; select one inverse/reinsertion architecture and do not depend on the displaced `copySelection` path. |
| `doubleCutIntro_sound`, `doubleCutElim_sound` | SO `doubleCut_equiv`, modal compiler simulation, and terminal `applyDoubleCutIntro_sound`/`applyDoubleCutElim_sound`; HO `CheckedDoubleCut.equivalence`, `.intro_sound`, `.elim_sound` | Retain the intrinsic double-cut equivalence and existing-compiler landing. Replace receipt/open-transport wrappers by current candidates and `CheckedOpenDiagram.denote`; remove lambda and definition parameters. |
| three identity soundness declarations | HO `dropDegenerate_sound`, `collapseOnePoint_sound`, `fuseSameRegion_sound`, with their candidate well-formedness owners | Retain the exact transformation and semantic proofs; project them onto current accepted candidates. Delete canonicalizer enumeration, iteration, orchestration, and normalization transport. |
| nineteen wire soundness declarations | HO terminal theorems `wire_sever_sound` through `identity_abstract_sound` in the seven named operation families | Retain each completed construction/semantic-ledger proof and its direction/parity argument. Replace definition-indexed checked diagrams and opaque applied receipts by current macro-free checked-open candidates; omit ref cases and normalization composition. |
| `Proof.Program.replay_sound` and two directional corollaries | SO `Proof.replay_sound`, `forward_replay_sound`, `backward_replay_sound`; HO `Proof.replay_sound` confirms the dependent composition | Retain nil reflexivity and cons composition through aggregate step soundness. Current programs are already total dependent chains, so executable checker and boundary-receipt transport are deleted. |
| `checkedTheorem_sound` | SO `checkedTheorem_sound` | Retain left replay, checked-isomorphism transfer, and right replay. Remove definition contexts, registration, and citation. |
| `verifiedTheory_sound` | SO verified-prefix/context-valid induction | Retain list induction over independently checked members. Remove prior-prefix registration and citation authority. |
| `WirePrimitive.Program.sound` | HO `runPrimitiveProgram_sound` | Retain the dependent nil/cons induction and dispatch each cons through its already-GREEN primitive owner. Remove compiler step receipts and normalization. |
| two direct adequacy declarations | HO `Compiler.lean` and `CompilerTermination.lean` construction cases; terminal `compiled_join_redundant` and `compiled_sever_redundant` are incomplete | Reuse only completed residual, plumbing, connective, leaf, inverse, termination, and carrier-landing work. New proof is restricted to the current-input and empty-request bridges, failure-free totality, and exact current landing. No compiler definition or API is authorized. |
| `Formula.semantically_complete` | absent from both predecessors | Sole greenfield theorem. Keep the witness existential and proof-local. |

The current iteration declaration families are retained only under the exact
HO-owner mapping in `iteration-declaration-audit.md`. The prior deletion of
`OpenCompilation`, `SpliceRaw`, and `Factorization*` removed files, not the
selected mathematical responsibilities consumed by the terminal theorem.

## R1: semantic and checked-diagram core

| Current responsibility | SO evidence at `2bddfe4` | Abandoned HO evidence | Classification and exact delta |
|---|---|---|---|
| `Sig`, typed `Var`/`Vars`, relation-wire signatures | SO has the indexed logical architecture but only the old second-order signature representation | `Sig.lean` has recursive `Sig`, typed `Var`, `Vars`, and nonemptiness | **completed HO port**; remove old definition-indexed vocabulary and retain recursive signature typing |
| full `Model`, `Assignment`, carrier nonemptiness, relation application | SO semantics is tied to `LambdaModel` and the second-order signature | `Model.lean` has the recursive-signature full model, `reify`, environments, and all-signature inhabitation | **completed HO port**; current `Model` exposes only the full-model fields actually used by R1-R5 |
| intrinsic atom/identity/cut syntax and denotation | `Diagram/Core.lean`, `Semantics.lean`, `Rename.lean`, and `Context.lean` own the complete recursion and context polarity architecture | the same files contain recursive-signature atom/identity/cut cases plus obsolete bind/ref/definition cases | **completed combined port**; region locals replace the old explicit bind constructor, while lambda, named/ref, and definition cases are deleted |
| concrete graph, open boundary, well-formedness, occurrence, elaboration, and ordered isomorphism | `Diagram/Concrete/**` supplies the complete checked architecture | `Concrete/Core.lean`, `WellFormed.lean`, `Elaboration*.lean`, `OpenCompilation.lean`, and `Isomorphism.lean` supply recursive-signature implementations | **completed combined port**; current owners remove `CNode.ref`, definition indices, receipts, search, and alternate elaborators |
| intrinsic one-hole context and concrete site compilation | SO `Diagram/Context.lean` and `Concrete/Elaboration/Context.lean` | `Diagram/Context.lean`, `ContextOuter.lean`, `ContextZipper.lean`, and the `SiteCompilation` family | core context compilation is GREEN; the hybrid relative-frame extension is deleted; shared `SiteFrame.visible` remains only because non-iteration proof owners consume it |
| generic concrete semantic simulation | `Concrete/Elaboration/Simulation.lean` defines `SimulationDirection`, context relations, item/region simulation, `ConcreteSemanticSimulation`, root simulation, and `elaborateOpen_denote`; structural and modal proofs import it | HO factorization and structural receipts specialize the same responsibility through exact intrinsic landing equations | **reusable architecture, not obsolete congruence**. The old module itself is deleted because its lambda/binder/named/definition types no longer exist, but every required simulation kernel must be ported or discharged by a substantively equivalent current specialization. Current `VacuousElaboration` is one completed specialization. |
| selection and canonical extraction | localized selection/region evidence | HO `CheckedExtraction` and its compilation | retain only declarations mapped exactly to the selected HO extraction chain |
| removal and iteration insertion | SO removal remains separate localized evidence | HO raw-splice/insertion/factorization chain | removal retains its audit result; iteration replaces the current selection-copy architecture with the selected HO owners |
| checked concrete isomorphism denotation | SO concrete/open isomorphism modules | HO `DenseIsomorphism.lean`, `Isomorphism.lean`, and `OpenIsomorphism.lean` | **completed port** as current `ConcreteIso`, `CheckedIso`, ordered boundary fields, and `CheckedIso.denote_iff` |

The selected HO extraction, splice/insertion, factorization, containment, and
semantic-equivalence declarations are the iteration closure. SO declarations
are used only for localized current-representation facts.

## R2: the exact 31 rules

### Completed operation definitions

| Current operation family | SO construction | Abandoned HO construction | Classification |
|---|---|---|---|
| atom spawn and identity insertion | `Rule/Structural/SpawnCore.lean`, `SpawnOpen.lean`, and `SpawnTransport.lean` | `StructuralInsertionInput`, `checkStructuralInsertion`, and `StructuralInsertionReceipt` in `Rule/Structural.lean` | **completed adaptation** as current `atomSpawnCandidate`, `identityInsertCandidate`, and their accepted `apply*` owners in `Structural/Spawn.lean`; no operation reimplementation is authorized |
| erasure | `Subgraph/Remove.lean` and `applyErasure` | `StructuralErasureInput`/`Receipt` | **completed adaptation** in current `Structural/Iteration.lean` |
| iteration/deiteration | localized public-surface and region facts | `CheckedOrdinaryIteration` and `CheckedOrdinaryDeiteration` | replace the current extraction/copy closure with a coherent port of the selected HO iteration chain; re-audit deiteration afterward |
| double cut and vacuous wire | SO `Rule/Structural/Modal.lean` and modal soundness construction modules | `CheckedDoubleCut` and `Rule/Vacuous.lean` | **completed adaptation** in current `Structural/Modal.lean` |
| identity degeneracy/collapse/fusion | not authoritative for these three transformations | `IdentityNormalizationCore.dropCandidate`, `collapseCandidate`, and `fusionCandidate`, with their completed well-formedness modules | **completed transformation-only adaptation** as current `degeneracyCandidate`, `collapseCandidate`, and `fusionCandidate` in `Structural/Identity.lean`; no canonicalizer exists in Lean |
| wire sever/join | old iota partition is only architectural precedent | raw `Concrete/WirePartition.wireSeverCandidate`/`wireJoinCandidate`, checked `severWire`/`joinWires`, and `Rule/WirePrimitive/Partition.lean` | **completed HO carrier adaptation** as current `wireSeverCandidate`/`wireJoinCandidate` and accepted `applyWireSever`/`applyWireJoin` |
| cut wrap/absorb, parallel split/fuse, ends delete/spawn | absent as this exact inventory | the six raw named candidates and checked operations in `Concrete/WirePrimitive/Content.lean`, plus `Rule/WirePrimitive/Content.lean` | **completed HO carrier adaptation** as the six current named candidates and accepted operations; current carriers keep an isomorphic survivor in place where the predecessor removed and re-added it |
| arity shift/unshift | absent as this exact inventory | `arityShiftSpec`/`arityUnshift` and `replaceAppliedEnds` in `Concrete/WirePrimitive/ArgumentsOperations.lean`, plus `Rule/WirePrimitive/ArgumentsArity.lean` | **completed HO carrier adaptation** as current `shiftCandidate`/`unshiftCandidate` and accepted operations |
| argument permute | deleted bubble-era precedent only | `argPermute` through `replaceAppliedEnds` plus `Rule/WirePrimitive/ArgumentsPermute.lean` | **completed HO carrier adaptation** as current `candidate` and accepted operation |
| argument duplicate/contract | deleted bubble-era precedent only | `argDuplicate`/`argContract` through `replaceAppliedEnds` plus `Rule/WirePrimitive/ArgumentsCore.lean` | **completed HO carrier adaptation** as current `duplicateCandidate`/`contractCandidate` and accepted operations |
| argument drop/extend | absent as this exact inventory | `argDrop`/`argExtend` through `replaceAppliedEnds` plus `Rule/WirePrimitive/ArgumentsDropExtend.lean` | **completed HO carrier adaptation** as current `dropCandidate`/`extendCandidate` and accepted operations |
| formal apply/abstract and identity leaf/abstract | absent as this exact inventory | raw `leafCandidate`/`abstractCandidate` and four checked operations in `Concrete/WirePrimitive/Leaves.lean`, plus `Rule/WirePrimitive/Leaves.lean` | **completed HO carrier adaptation** as current `leafCandidate`/`abstractCandidate` and four accepted operations; ref leaf/abstract cases are deleted |

Current operations are complete only where their individual audits establish
substantive predecessor equivalence. The iteration mismatch is recorded and
authorizes its complete replacement; no unrelated operation is reopened.

### Structural soundness: selected predecessor ports

| Current owner | Complete SO owner/closure | Complete HO owner/closure | Allowed work |
|---|---|---|---|
| `atomSpawn_sound` | `spawnNodeRaw_compileRoot_route_kernel`, `spawnNodeRawOpen_projects`, and `spawn_context_sound` | `StructuralInsertionReceipt.negative_splice_sound` and `.sound` | **completed port** through the current old-wire/fresh-argument context embedding, recursive `SiteFrame` simulation, root assignment extension, and ordered-boundary handoff; no receipt, normalization, alternate compiler, or transport API |
| `identityInsert_sound` | `spawnNodeRaw_compileRoot_route_kernel` plus its away/site/root and ordered-open handoffs | `StructuralInsertionReceipt.negative_splice_sound` and `.sound` | **completed port** through current `SiteFrame`; no canonicalizer, receipt, transport object, or alternate compiler |
| `erasure_sound` | `positive_erasure_sound`, `negative_insertion_sound`, `applyErasure_sound`, and actual splice reassembly dependencies | `StructuralErasureReceipt.sound` | **completed port** through stable removal-origin equations, the established compiler-projection recursion, contravariant assignment extension, ordered-boundary correspondence, and cut-parity direction; no extraction redesign, decomposition owner, splice API, receipt, normalization, or alternate compiler |
| `iteration_sound` | localized public responsibility and current-representation facts | HO `CheckedExtraction`, site/relative frames, `ConcreteSpliceAttachment`, `spliceRaw`, `InsertionCompilation`, `Factorization*`, intrinsic containment, and `CheckedOrdinaryIteration.equivalence`/`.sound` | port the complete HO chain and remove the current copy/compiler-simulation path; do not combine it with the SO route architecture |
| `deiteration_sound` | `applyDeiteration_sound` by reinsertion | `CheckedOrdinaryDeiteration.sound`/`.equivalence` | re-audit after the shared iteration replacement and select one coherent inverse/reinsertion architecture |
| double-cut owners | `doubleCut_equiv`, SO `Rule/Soundness/Modal.lean`, `Modal/Root.lean`, and the `Modal/Elimination*` simulation/root/boundary modules; terminal `applyDoubleCutIntro_sound`/`applyDoubleCutElim_sound` | `CheckedDoubleCut.equivalence`, `.intro_sound`, and `.elim_sound` | adapt the existing candidate simulation or exact intrinsic landing; no independent concrete proof design |
| vacuous owners | SO `Modal/Vacuous*` and terminal vacuous soundness | HO `CheckedVacuous.equivalence`, `.intro_sound`, `.elim_sound` | **already GREEN** as the current macro-free `VacuousElaboration` specialization; no further work |

The SO `Concrete/Elaboration/Simulation.lean` responsibility remains a valid
port source for structural candidate simulation. Its deletion as a historical
file did not delete its mathematics or authorize reimplementation.

### Identity soundness: minor HO ports only

| Current owner | Exact complete HO source |
|---|---|
| `identityDegeneracy_sound` | `IdentityNormalizationDropWellFormed.dropCandidate_wellFormed` and `IdentityNormalizationDropSemantics.dropDegenerate_sound` |
| `identityCollapse_sound` | `IdentityNormalizationCollapseWellFormed.collapseCandidate_wellFormed` and `IdentityNormalizationCollapseSemantics.collapseOnePoint_sound` |
| `identityFusion_sound` | `IdentityNormalizationFusionWellFormed.fusionCandidate_wellFormed` and `IdentityNormalizationFusionSemantics.fuseSameRegion_sound` |

Only these transformation proofs port. `normalizeIdentities_sound`, candidate
enumeration, repeated normalization, and normalization transport do not.

### Nineteen wire-primitive soundness owners: minor HO ports only

| Current owner(s) | Exact complete HO theorem(s) | Required lower closure |
|---|---|---|
| `wireSever_sound`, `wireJoin_sound` | `wire_sever_sound`, `wire_join_sound` in `Rule/WirePrimitive/Partition.lean` | signature-indexed wire-partition construction and denotation ledgers |
| `cutWrap_sound`, `cutAbsorb_sound` | `cut_wrap_sound`, `cut_absorb_sound` in `Content.lean` | content construction/semantic ledger and inverse landing |
| `parallelSplit_sound`, `parallelFuse_sound` | `parallel_split_sound`, `parallel_fuse_sound` in `Content.lean` | same content ledger closure |
| `endsDelete_sound`, `endsSpawn_sound` | `ends_delete_sound`, `ends_spawn_sound` in `Content.lean` | end-set ledger and polarity closure |
| `arityShift_sound`, `arityUnshift_sound` | `arity_shift_sound`, `arity_unshift_sound` in `ArgumentsArity.lean` | cylindrification construction and denotation ledger |
| `argPermute_sound` | `arg_permute_sound` in `ArgumentsPermute.lean` | permutation construction and denotation ledger |
| `argDuplicate_sound`, `argContract_sound` | `arg_duplicate_sound`, `arg_contract_sound` in `ArgumentsCore.lean` | diagonal construction and inverse ledger |
| `argDrop_sound`, `argExtend_sound` | `arg_drop_sound`, `arg_extend_sound` in `ArgumentsDropExtend.lean` | drop/extend construction, polarity, and denotation ledgers |
| `applyFormal_sound`, `abstractFormal_sound` | `apply_formal_sound`, `abstract_formal_sound` in `Leaves.lean` | leaf construction, full-model application witness, and inverse landing |
| `identityLeaf_sound`, `identityAbstract_sound` | `identity_leaf_sound`, `identity_abstract_sound` in `Leaves.lean` | identity-leaf construction/equality semantics and inverse landing |

The final HO `CompiledPrimitiveStep.sound` case split is also complete, but
its trailing automatic `normalizeIdentities_sound` composition is excluded.
Current `applyStep_sound` is already the completed direct 31-case adaptation;
it becomes axiom-free when the delegated owners become GREEN.

## R3: primitive replay and certification

| Current owner | Complete predecessor | Classification |
|---|---|---|
| `Proof.Program.replay_sound` and directional corollaries | SO `Proof/Replay.replay_sound` and forward/backward corollaries; HO `runPrimitiveProgram_sound` gives the same dependent induction | **minor mechanical port**: nil reflexivity and cons composition through current `applyStep_sound` |
| `checkedTheorem_sound` | SO `Proof/Theorem.checkedTheorem_sound` | **minor mechanical port**: keep two replay directions plus `CheckedIso.denote_iff`; remove definitions, registration, and citation context |
| `verifiedTheory_sound` | SO verified-prefix induction | **minor mechanical port**: each current stored schema already carries its independent `CheckedTheorem`; remove prior-prefix citation |

No replay checker, theorem registry, theorem step, receipt transport, or macro
authority is required.

## R4: formula semantic expressiveness

Search of both predecessors finds no `Formula` language, `Formula.denote`, or
semantic-expressiveness theorem. Current `Formula` definitions are complete,
including same-signature equality. `Formula.semantically_complete` is the sole
**wholly new theorem family**. It is existential and exposes no compiler.

## R5: direct substitution/comprehension adequacy

### Completed current specification owners

Current `DirectSubstitutionInput`, `DirectSubstitution`,
`DirectComprehensionInput`, and `DirectComprehension` are
representation-independent reformulations of the abandoned
`MonolithicRelationJoinInput`/`AcceptedMonolithicRelationJoin` and
`MonolithicRelationSeverInput`/`AppliedMonolithicRelationSever` raw carrier
equations. They remove checker state, definitions, refs, normalization, and
compiler receipts while preserving positional attachments and exact raw
carrier/boundary equations. These definitions are complete and are not to be
reimplemented.

### Exact direct primitive basis

The direct program may use the nineteen wire primitives plus vacuous
introduction/elimination. It excludes atom spawn, identity insertion,
identity degeneracy/collapse/fusion, structural copy/erasure/double cut,
canonicalization, and normalization.

`identityLeaf` and `identityAbstract` must be included. They are members of the
specified nineteen wire primitives, not identity-normalization rules. The
abandoned compiler's intrinsic `.identity` case terminates with
`runIdentityLeaf`; reversed sever compilation maps that step to
`identityAbstract`. Omitting them makes arbitrary atom/identity/cut content
outside the claimed primitive basis.

### Reusable compiler proof material and the honest gap

The abandoned `Compiler.lean` and `CompilerTermination.lean` completely
implement:

- residual syntax and the well-founded measure;
- plumbing plans for extend/drop/permute/duplicate;
- connective cases for quantifier, parallel, cut, empty, atom/formal, and
  identity leaves;
- dependent primitive-program composition;
- inverse-step construction for sever;
- raw origin tables and `ConcreteIso.ofEquivs` landing construction.

Macro/ref cases are deleted. The compiler's `compileRawIdentityPrefix` is not
ported as a direct-adequacy mechanism. For current substitution inputs,
`DirectSubstitutionInput.attachment_alias` supplies exactly the coherence
hypothesis of
`RelationJoinStep.identityRequests_eq_nil_of_sourceAttachments_coherent`, so
`rawIdentityInsertionPlans` is empty. The proof must establish that bridge and
start from the identity-free residual construction.

The predecessor terminal theorems `compiled_join_redundant` and
`compiled_sever_redundant` are `sorry`; their semantic corollaries are also
`sorry`. Therefore only the completed construction cases may be reused. The
honest pending work is:

1. bridge the current mathematical direct inputs to the reusable residual and
   inverse constructions, including the empty identity-request fact;
2. prove that every recursive construction call succeeds for every legal
   current input; and
3. prove the final current raw target equations and `ConcreteIso`, whose
   boundary field preserves ordered positions and repeated aliases.

This is **partial predecessor work**, not a completed compiler theorem and not
a greenfield compiler project. The construction stays proof-local; no public
compiler API, monolithic rule, search, receipt, or normalization surface is
introduced.

`WirePrimitive.Program.sound` is a **minor mechanical port** of HO
`runPrimitiveProgram_sound` or a specialization of current replay.

## Final authorization ledger

| Classification | Owners |
|---|---|
| completed ports to retain | R1 semantic/checked core except iteration-owned declarations rejected by the completed audit, removal, separately audited non-iteration operations, two vacuous owners, exhaustive dispatcher, direct relation definitions |
| pending coherent predecessor ports | iteration operation-to-terminal HO closure; afterward deiteration and double-cut structural owners |
| pending minor ports only | three identity owners, nineteen wire owners, replay and directional corollaries, checked theorem, verified theory, primitive-program soundness |
| partial predecessor plus named missing proof | two direct adequacy theorems |
| wholly new | formula semantic expressiveness only |

No other current or future production owner is authorized as greenfield work.
If a named port fails, record the exact predecessor declaration, current target
declaration, and untransportable hypothesis or conclusion before proposing a
new construction.
