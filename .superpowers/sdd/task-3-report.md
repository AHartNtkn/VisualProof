# T004 progress receipt — rule soundness

## Current result

Double-cut introduction is now proved end to end, for nested and sheet-root
focuses and for every ordered open boundary. The public
`applyDoubleCutIntro_sound` theorem contains no admission.

The proof covers:

- exact combinatorial characterization of retained and selected occurrences;
- inversion of the target compiler into retained material and two nested cuts;
- pointwise semantic transport for term, atom, named, cut, and bubble
  occurrences, including reparented selected children;
- recursive compiler simulation at the actual target fuel below both inserted
  cuts;
- source conjunction permutation into retained and selected subsequences;
- zero-wire semantics for the two fresh cut regions;
- intrinsic double-negation equivalence for the selected conjunction; and
- forward and backward local valuation transport through `finishRegion`;
- direct focused-item compilation from an arbitrary exact lexical context;
- root compiler transport, including a focus at the sheet root;
- exposed and hidden root-wire witness transport; and
- receipt normalization from the exact operational graph to the checked
  result.

The shared concrete-simulation callback now carries the target child fuel
explicitly. This is required for retained material compiled beneath freshly
inserted wrappers and is checked by all downstream simulation consumers.

Double-cut elimination now has a typed executor trace exposing the two cut
identities, empty outer annulus, and exact promotion result. The trace shows
that elimination is not merely an inverse introduction isomorphism: wires
scoped by the inner cut are promoted to its parent. The remaining local
semantic obligation is therefore the equivalence obtained by moving those
existential wire witnesses across double negation.

That intrinsic obligation is now proved as
`adjoin_doubleCutRegion_equiv`: host-local witnesses remain outside the
double cut and visible to both retained and selected material, while
selected-local witnesses move with the selected body through double
negation. The elimination module also proves:

- distinctness and survival of the outer, inner, and target regions;
- uniqueness of the inner child and emptiness of the outer annulus;
- exact promoted node-owner, wire-scope, and region-parent
  classifications at the promoted focus;
- the promoted focus partition into retained and selected occurrences; and
- exact correspondence between selected promoted occurrences and the
  original inner-cut occurrences;
- exact local-occurrence and wire-scope correspondence for every regular
  surviving region;
- survivor-origin preservation of regular nodes, child wrappers, and bubble
  binders; and
- port-resolution correspondence under wire identity, including contexts
  where promoted inner wires are present only on the source side.

The focused elimination semantics are also complete independently of the
compiler partitioning layer. In particular, the proof now provides:

- recursive occurrence compilation for promoted term, atom, named, cut, and
  bubble occurrences;
- a context invariant proving that the only possible source-only wires are
  original inner-cut witnesses;
- canonical forward extraction and backward reconstruction of target and
  inner witness environments by concrete wire identity;
- normalization of the compiled target focus into retained items plus the
  actual nested double cut, with nonempty inner wire scope; and
- a bidirectional `focusedPartition_regionSimulation` theorem transporting
  retained and selected compiled subsequences through that double cut.

Double-cut elimination is now proved end to end as well. The public
`applyDoubleCutElim_sound` theorem contains no admission. Its proof layer
provides:

- `focusedItems_regionSimulation`, which connects the actual source and target
  compiler outputs to the kept/selected partition theorem and transports back
  across both occurrence permutations;
- regular-region valuation transport in both directions, including source-only
  inner witnesses;
- the complete `DoubleCutElimTrace.semanticSimulation` instance, covering
  regular wrappers, nodes, binders, recursive regions, and the distinguished
  focus without admissions; and
- the ordered-open root prerequisites: promoted root-scope transport, checked
  source/target open diagrams, combined root context evidence, regular hidden
  wire equality, root environment decomposition, the selected root context,
  and the target root double-cut denotation law;
- bidirectional focused-root witness reconstruction when promoted inner wires
  become hidden root witnesses;
- compiler transport for the actual root occurrence order, not only the
  kept/selected semantic partition;
- a complete regular/focused `RootContextSimulation` and ordered boundary
  witness; and
- normalization of the executor's raw promotion result and interface transport
  to the exact checked open diagram used by the semantic simulation.

## Evidence

Changed theorem-bearing files include:

- `VisualProof/Rule/Soundness/Modal.lean`
- `VisualProof/Rule/Soundness/Modal/FocusedItems.lean`
- `VisualProof/Rule/Soundness/Modal/Root.lean`
- `VisualProof/Rule/Soundness/Modal/Elimination.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationCompiler.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationFocusedItems.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationFocusedTransport.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationFocusedCompiler.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationSimulation.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationRoot.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationRootTransport.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationRootCompiler.lean`
- `VisualProof/Rule/Soundness/Modal/EliminationRootSimulation.lean`
- `VisualProof/Rule/Soundness/Structural.lean`
- `VisualProof/Rule/Structural/Modal.lean`
- `VisualProof/Diagram/Concrete/Elaboration/Simulation.lean`

Validation:

```text
lake env lean VisualProof/Rule/Soundness/Modal/FocusedItems.lean
lake env lean VisualProof/Rule/Soundness/Modal/Root.lean
lake env lean VisualProof/Rule/Soundness/Structural.lean
lake env lean VisualProof/Rule/Structural/Modal.lean
lake env lean VisualProof/Rule/Soundness/Modal/Elimination.lean
lake env lean VisualProof/Rule/Soundness/Modal/EliminationCompiler.lean
lake env lean VisualProof/Rule/Soundness/Modal/EliminationFocusedItems.lean
lake env lean VisualProof/Rule/Soundness/Modal/EliminationFocusedTransport.lean
All completed successfully.

lake build VisualProof.Rule.Soundness.Modal.EliminationFocusedTransport
Build completed successfully (87 jobs).

lake build VisualProof.Rule.Soundness.Modal.EliminationSimulation
Build completed successfully (89 jobs).

lake build VisualProof.Rule.Soundness.Modal.EliminationRoot
Build completed successfully (90 jobs).

lake env lean VisualProof/Rule/Soundness/Modal/EliminationRootTransport.lean
Completed successfully.

lake build VisualProof.Rule.Soundness.Modal.EliminationRootCompiler
Build completed successfully (92 jobs).

lake build VisualProof.Rule.Soundness.Modal.EliminationRootSimulation
Build completed successfully (93 jobs).

lake build VisualProof.Rule.Soundness.Structural
Build completed successfully (95 jobs).

rg -n "sorry|trace_state" VisualProof/Rule/Soundness/Modal.lean \
  VisualProof/Rule/Soundness/Modal/FocusedItems.lean \
  VisualProof/Rule/Soundness/Modal/Root.lean \
  VisualProof/Rule/Soundness/Modal/Elimination*.lean
No matches.
```

The public rule-soundness admission count is 11:

- equational: 5;
- structural: 4;
- high-level comprehension: 2.

No new admission or project axiom was introduced. The modal module is 2,638
lines; every theorem-bearing file remains below 3,000 lines.

## Next proof slice

Prove vacuous-bubble introduction and elimination as the next modal pair,
including their executor receipt and ordered-open boundary bridges. Then close
iteration/deiteration before returning to the remaining equational and
high-level forms.

Foundation record:
`/tmp/visualproof-foundation-20260716-t004-rule-soundness-v28.xml`.

## Iteration/deiteration progress

The iteration proof now has the intrinsic contraction law and the concrete
anchor/extraction bridge required to instantiate it:

- `ancestorSpliceCopy_sound` proves contraction at a descendant splice site
  while the copied occurrence remains available as a separate ancestor
  conjunct;
- `iterationCoalescedFrameIso` proves that iteration's attachment quotient is
  discrete and its coalesced frame is exactly the input frame;
- `keptRoute_complete` constructs the compiler path from the retained anchor
  block to every admissible unselected target without rebinding anchor-local
  wire witnesses;
- `compilerLeaf_selection_factor` factors the authoritative anchor compiler
  semantically into the retained route block and selected ancestor resource;
- `extractionHostOccurrenceMap_terminal_perm_selected` identifies the
  extracted terminal occurrences with exactly the selected anchor occurrences;
- `fragmentWireOrigin_scope_encloses_anchor` and
  `extractionContextEnvironmentsAgree` prove the exact lexical wire transport
  from the extracted terminal body to the host anchor; and
- `extractionTerminalBinder_is_proxy` plus
  `extractionTerminalRelationRenaming_lookup` prove that every extracted
  terminal relation coordinate is supplied by the corresponding external host
  binder.

The remaining iteration obligation is to lift these wire and binder facts
through the recursive occurrence compiler, then instantiate
`ancestorSpliceCopy_sound` and the successful-receipt bridge. Deiteration will
reuse the inverse occurrence transport and the same ancestor factorization.

That recursive and executable transport layer is now closed. In particular:

- `partitionedRoute_copyTransport` transports the selected ancestor resource
  through every retained descendant environment;
- `partitionedRoute_splice_equiv` instantiates the intrinsic contraction law
  at the route's terminal focus;
- `properRoute_actualSpliceIso` proves that the route-native splice and the
  executor's exact host splice are intrinsically isomorphic, including the
  concrete wire substitution and lexical relation substitution;
- `partitionedRoute_leaf_equiv` lifts contraction back to the authoritative
  compiler leaf after the selected/retained occurrence partition;
- `RegionIso.ContextPathAlignment` transports proof-relevant focused paths
  through compiler item permutations; and
- `Region.ContextPath.nest` and `DiagramContext.comp` provide the intrinsic
  composition law needed to lift the anchor-relative target path to the whole
  root and ordered-open boundary;
- `compilerLeaf_routePath_complete` constructs the authoritative full-leaf
  compiler witness at the concrete route's exact position list; and
- `iterationAnchorRoute_hostPath` proves that composing the root-to-anchor
  path with the anchor-to-target route gives exactly the executor's canonical
  host path.

The remaining iteration obligation is therefore the whole-open compiler
context identification and receipt normalization. It is no longer a missing
logical rule or a missing wire/binder transport theorem. Deiteration remains
next and will use the resulting equivalence in reverse.

Validation:

```text
lake build VisualProof.Rule.Soundness.Iteration.AncestorFactor
Build completed successfully (86 jobs).

lake build VisualProof.Rule.Soundness.Iteration.ExtractionContext
Build completed successfully (87 jobs).

lake env lean VisualProof/Rule/Soundness/Iteration/ExtractionBinder.lean
Completed successfully.

lake build VisualProof.Rule.Soundness.Iteration.CanonicalContraction
Build completed successfully (106 jobs).

lake build VisualProof.Diagram.Algebra
Build completed successfully (15 jobs).
```

No admission or project axiom was added.

## Vacuous pair progress

The vacuous-introduction proof now has a checked combinatorial/compiler base:

- `Modal/Vacuous.lean` proves the exact raw cardinalities, roots, wires,
  parent maps, empty bubble scope, selected/kept occurrence partitions, and
  local-occurrence equations for the bubble, selected anchor, and every
  regular region;
- it also proves regular and selected node/region shapes plus endpoint-owner
  and port-resolution preservation;
- `Modal/VacuousCompiler.lean` proves relation-binder transport through both
  ordinary nested bubbles and the newly introduced fresh binder; and
- its generic occurrence compiler theorem transports terms, atoms, named
  nodes, cuts, and bubbles under an arbitrary relation renaming, including
  recursively lifted renamings; and
- `Modal/VacuousSimulation.lean` now supplies the checked semantic reduction
  of the compiled zero-wire bubble item to its fresh-relation body.

Validation:

```text
lake build VisualProof.Rule.Soundness.Modal.Vacuous
Build completed successfully (82 jobs).

lake env lean VisualProof/Rule/Soundness/Modal/VacuousCompiler.lean
Completed successfully.

lake build VisualProof.Rule.Soundness.Modal.VacuousCompiler
Build completed successfully (83 jobs).

lake env lean VisualProof/Rule/Soundness/Modal/VacuousSimulation.lean
Completed successfully.

wc -l VisualProof/Rule/Soundness/Modal/Vacuous.lean \
  VisualProof/Rule/Soundness/Modal/VacuousCompiler.lean
887 and 408 lines respectively.
```

No admission was added. The remaining introduction work is the focused
item-sequence equivalence, the generic simulation instance, and the
ordered-open receipt bridge; elimination will then reuse the same vacuity
kernel over its promotion trace.

## Vacuous pair completion

Both vacuous rules are now proved through the public receipt-soundness API.
For elimination, the proof covers promotion of bubble-local nodes, regions,
and wires into the parent; compiler-order permutations; arbitrary inherited
relation renamings; the target bubble's fresh existential relation; ordinary
and distinguished recursive regions; root-local versus exposed-wire
transport; and the interface-transport isomorphism from the promoted diagram
to the executor receipt.

New elimination modules:

- `Modal/VacuousElimination.lean`
- `Modal/VacuousEliminationCompiler.lean`
- `Modal/VacuousEliminationFocusedItems.lean`
- `Modal/VacuousEliminationFocusedTransport.lean`
- `Modal/VacuousEliminationFocusedCompiler.lean`
- `Modal/VacuousEliminationSimulation.lean`
- `Modal/VacuousEliminationRoot.lean`
- `Modal/VacuousEliminationRootTransport.lean`
- `Modal/VacuousEliminationRootCompiler.lean`
- `Modal/VacuousEliminationRootSimulation.lean`

Validation:

```text
lake build VisualProof.Rule.Soundness.Modal.VacuousEliminationRootSimulation
Build completed successfully (100 jobs).

lake build VisualProof.Rule.Soundness.Structural
Build completed successfully (109 jobs).

rg -n '\bsorry\b|\badmit\b' \
  VisualProof/Rule/Soundness/Modal/VacuousElimination*.lean
No matches.
```

The only remaining public structural admissions are `applyIteration_sound`
and `applyDeiteration_sound`. Every vacuous-elimination module is below 1,900
lines; the proof is split by semantic responsibility rather than accumulated
in a monolith.

## Iteration extraction compiler bridge

The iteration proof now has the exact semantic transport needed below the
combinatorial extraction certificate:

- `ExtractionContext.lean` proves equality of terminal lexical wire contexts
  under the authoritative fragment-to-host wire provenance map;
- `ExtractionBinder.lean` constructs the corresponding relation-variable
  renaming from the extracted proxy spine into the host anchor context;
- `ExtractionNode.lean` proves exact port lookup transport, owner and binder
  provenance, copied-node shape, and backward semantic simulation for every
  compiled term, named node, and atom; and
- `ExtractionRegion.lean` begins the recursive lift by proving that copied
  material regions and their exact local wires preserve and reflect their
  unique host provenance, including existence of an extracted preimage for
  every host-local selected wire.

Validation:

```text
lake build VisualProof.Rule.Soundness.Iteration.ExtractionNode
Build completed successfully (89 jobs).

lake build VisualProof.Rule.Soundness.Iteration.ExtractionRegion
Build completed successfully (90 jobs).
```

No admission was added. The next proof step is the recursive material-region
compiler simulation, followed by the terminal occurrence permutation and the
public iteration/deiteration receipt theorems.

Further recursive infrastructure now checked:

- material-region local occurrences map bijectively to host local
  occurrences, with a proved compiler-order permutation;
- copied material ancestry reflects host ancestry;
- context membership and port resolution remain exact after recursively
  extending both lexical contexts;
- copied proxy/material bubble binders preserve arity and visibility; and
- `ExtractionBinderWitness` carries one coherent relation renaming through
  cut children and lifts it through bubble children, including exact lookup
  and ancestry proofs.

```text
lake build VisualProof.Rule.Soundness.Iteration.ExtractionRegionWitness
Build completed successfully (95 jobs).

rg -n '\bsorry\b|\badmit\b|^axiom ' \
  VisualProof/Rule/Soundness/Iteration \
  VisualProof/Rule/Structural/Semantics.lean \
  VisualProof/Diagram/Concrete/Subgraph/Extract.lean
No matches.
```
