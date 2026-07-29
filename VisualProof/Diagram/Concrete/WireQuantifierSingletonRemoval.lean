import VisualProof.Diagram.Concrete.WireQuantifier
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport

namespace VisualProof

universe u

/-!
Compiler decomposition for the singleton-node removal used by relation join.

This helper is deliberately independent of relation semantics.  It exposes
the exact conjunction represented by deleting one member of an executable
`compileNodes?` input; the relation-specific bridge supplies the denotation of
that singleton only after the dying relation variable has been instantiated.
-/

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

/-- A checked target whose concrete value is the canonical dense erasure. -/
structure CheckedErasure
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) where
  target : CheckedDiagram definitions
  generated :
    target.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed

namespace CheckedErasure

theorem candidate_wellFormed
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    (erasure : CheckedErasure source removed) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed).WellFormed definitions := by
  rw [← erasure.generated]
  exact erasure.target.property

end CheckedErasure

/--
A compiled node sequence denotes exactly when every executable singleton
compilation drawn from its source node list denotes.
-/
theorem denote_compileNodes_iff_singletons
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ node, node ∈ nodes →
        ∃ item,
          ConcreteElaboration.compileNodes? definitions diagram context
              [node] =
            some (.cons item .nil) ∧
          denoteItem pre definitionEnv env item := by
  induction nodes generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?] at compiled
      have itemsEmpty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled,
          itemsEquation⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions diagram context head tail items compiled
      subst items
      rw [denoteItemSeq_cons, induction restItems restCompiled]
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ candidate member
        rcases List.mem_cons.mp member with equality | tailMember
        · subst candidate
          exact ⟨headItem, headCompiled, headDenotes⟩
        · exact tailDenotes candidate tailMember
      · intro each
        obtain ⟨actualHead, actualCompiled, headDenotes⟩ :=
          each head (by simp)
        have actualEquality : actualHead = headItem :=
          ItemSeq.cons.inj
            (Option.some.inj
              (actualCompiled.symm.trans headCompiled)) |>.1
        subst actualHead
        exact
          ⟨headDenotes, fun candidate tailMember =>
            each candidate (List.mem_cons_of_mem head tailMember)⟩

/-- Recover one generated singleton compilation from a compiled node list. -/
theorem compileNodes_singleton_of_member
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items)
    (node : diagram.NodeId)
    (member : node ∈ nodes) :
    ∃ item,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some (.cons item .nil) := by
  induction nodes generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled, _⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions diagram context head tail items compiled
      rcases List.mem_cons.mp member with equality | tailMember
      · subst node
        exact ⟨headItem, headCompiled⟩
      · exact induction restItems restCompiled tailMember

/--
Deleting one named member from an executable node list isolates exactly its
compiled singleton conjunct.  No logical assumption about that singleton is
used here.
-/
theorem denote_compileNodes_filter_and_singleton
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (nodes : List diagram.NodeId)
    (removed : diagram.NodeId)
    (removedMember : removed ∈ nodes)
    (fullItems filteredItems : ItemSeq definitions context.sigs)
    (fullCompiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some fullItems)
    (filteredCompiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (nodes.filter fun candidate => decide (candidate ≠ removed)) =
        some filteredItems)
    (removedItem : Item definitions context.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          [removed] =
        some (.cons removedItem .nil)) :
    denoteItemSeq pre definitionEnv env fullItems ↔
      denoteItem pre definitionEnv env removedItem ∧
        denoteItemSeq pre definitionEnv env filteredItems := by
  rw [
    denote_compileNodes_iff_singletons definitions diagram context pre
      definitionEnv env nodes fullItems fullCompiled,
    denote_compileNodes_iff_singletons definitions diagram context pre
      definitionEnv env
      (nodes.filter fun candidate => decide (candidate ≠ removed))
      filteredItems filteredCompiled]
  constructor
  · intro each
    constructor
    · obtain ⟨actual, actualCompiled, actualDenotes⟩ :=
        each removed removedMember
      have same : actual = removedItem :=
        ItemSeq.cons.inj
          (Option.some.inj
            (actualCompiled.symm.trans removedCompiled)) |>.1
      simpa [same] using actualDenotes
    · intro candidate member
      exact each candidate (List.mem_filter.mp member).1
  · rintro ⟨removedDenotes, eachRetained⟩ candidate member
    by_cases same : candidate = removed
    · subst candidate
      exact ⟨removedItem, removedCompiled, removedDenotes⟩
    · exact
        eachRetained candidate
          (List.mem_filter.mpr
            ⟨member, decide_eq_true same⟩)

private def retainedNodes
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    List source.val.NodeId :=
  ConcreteDiagram.IdentityNormalizationCore.retainedNodes
    source.val [removed]

/-- The count-preserving image of one wire in the raw erase candidate. -/
def targetWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed).WireId :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
    source removed wire

@[simp] private theorem wiresList_get_targetWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    source.val.wiresList.get (targetWire source removed wire) = wire := by
  apply Fin.ext
  simp [targetWire,
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire,
    ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]

@[simp] theorem targetWire_signature
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).wires
      (targetWire source removed wire)).sig =
      (source.val.wires wire).sig := by
  change
    (source.val.wires
      (source.val.wiresList.get
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
          source removed wire))).sig =
      (source.val.wires wire).sig
  congr 2
  apply Fin.ext
  simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire,
    ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]

private theorem targetWire_injective
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    Function.Injective (targetWire source removed) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire_injective
    source removed

/-- The count-preserving image of one region in the raw erase candidate. -/
def targetRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed).RegionId :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
    source removed region

@[simp] private theorem targetRegion_val
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (targetRegion source removed region).val = region.val :=
  rfl

@[simp] private theorem targetRegion_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    targetRegion source removed region = region := by
  apply Fin.ext
  rfl

private theorem targetRegion_injective
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    Function.Injective (targetRegion source removed) := by
  intro left right same
  apply Fin.ext
  exact congrArg Fin.val same

private theorem target_childrenOf
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).childrenOf
        (targetRegion source removed region) =
      (source.val.childrenOf region).map
        (targetRegion source removed) := by
  change
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed).childrenOf region =
      (source.val.childrenOf region).map (targetRegion source removed)
  have mappedIdentity :
      (source.val.childrenOf region).map (targetRegion source removed) =
        source.val.childrenOf region := by
    induction source.val.childrenOf region with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.map_cons, targetRegion_eq, induction]
  rw [mappedIdentity]
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  apply List.filter_congr
  intro child _
  generalize dataEquation : source.val.regions child = data
  cases data <;>
    simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate,
      dataEquation]

private theorem all_targetWires
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    Data.Finite.allFin source.val.wiresList.length =
      (Data.Finite.allFin source.val.wireCount).map
        (targetWire source removed) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  apply List.ext_get
  · simp only [List.length_finRange, List.length_map]
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  · intro index leftBound rightBound
    apply Fin.ext
    simp only [List.get_eq_getElem, List.getElem_map]
    simp [targetWire,
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire,
      ConcreteDiagram.wiresList]

private theorem target_wiresAt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).wiresAt
        (targetRegion source removed region) =
      (source.val.wiresAt region).map (targetWire source removed) := by
  unfold ConcreteDiagram.wiresAt
  change
    (Data.Finite.allFin source.val.wiresList.length).filter
        (fun wire =>
          (source.val.wires (source.val.wiresList.get wire)).scope ==
            region) =
      ((Data.Finite.allFin source.val.wireCount).filter
        (fun wire => (source.val.wires wire).scope == region)).map
          (targetWire source removed)
  rw [all_targetWires source removed, List.filter_map]
  apply congrArg (List.map (targetWire source removed))
  apply List.filter_congr
  intro wire _
  exact congrArg
    (fun data => data.scope == region)
    (congrArg source.val.wires
      (wiresList_get_targetWire source removed wire))

/-- The dense target index of one retained source node. -/
def targetNode
    (source : CheckedDiagram definitions)
    (removed sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ removed) :
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed).NodeId :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
    source removed sourceNode (by
      apply List.mem_filter.mpr
      exact
        ⟨Data.Finite.mem_allFin _, by
          simp [ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
            survives]⟩)

private def targetEndpoint
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (survives : endpoint.node ≠ removed) :
    CEndpoint
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).nodeCount :=
  ⟨targetNode source removed endpoint.node survives, endpoint.port⟩

private theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (removed sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ removed)
    (port : CPort)
    (wire : source.val.WireId)
    (incident :
      (⟨sourceNode, port⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires wire).endpoints) :
    (⟨targetNode source removed sourceNode survives, port⟩ :
      CEndpoint
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).nodeCount) ∈
      ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).wires
        (targetWire source removed wire)).endpoints := by
  apply List.mem_filterMap.mpr
  refine
    ⟨(⟨sourceNode, port⟩ :
      CEndpoint source.val.nodeCount), ?_, ?_⟩
  · apply List.mem_filter.mpr
    constructor
    · rw [wiresList_get_targetWire]
      exact incident
    · simp [survives]
  · unfold ConcreteDiagram.IdentityNormalizationCore.reindexEndpoint?
    have present :
        Data.Finite.indexOf?
            (ConcreteDiagram.IdentityNormalizationCore.retainedNodes
              source.val [removed]) sourceNode =
          some (targetNode source removed sourceNode survives) := by
      unfold targetNode
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
      exact (Option.some_get _).symm
    rw [present]
    rfl

/-- Visible-wire context induced by dense singleton-node deletion. -/
def targetContext
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed) :=
  ⟨context.ids.map (targetWire source removed)⟩

theorem targetContext_sigs
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val) :
    (targetContext source removed context).sigs = context.sigs := by
  unfold targetContext ConcreteElaboration.WireContext.sigs
  rw [List.map_map]
  apply List.map_inj_left.mpr
  intro wire _
  exact targetWire_signature source removed wire

private theorem targetContext_extend
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    targetContext source removed (context.extend region) =
      (targetContext source removed context).extend
        (targetRegion source removed region) := by
  cases context
  simp only [targetContext, ConcreteElaboration.WireContext.extend,
    target_wiresAt, List.map_append]

private def mappedHere
    (signature : targetSig = sourceSig) :
    Var (targetSig :: tail) sourceSig :=
  signature ▸ (Var.here : Var (targetSig :: tail) targetSig)

@[simp] private theorem origin_mappedHere
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (ids : List diagram.WireId)
    (signature : (diagram.wires wire).sig = sourceSig) :
    ConcreteElaboration.WireContext.origin diagram (wire :: ids)
        (mappedHere
          (tail := ids.map fun candidate =>
            (diagram.wires candidate).sig)
          signature) =
      wire := by
  cases signature
  rfl

private def contextRenamingFor
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (ids : List source.val.WireId) :
    WireRenaming
      (ids.map fun wire => (source.val.wires wire).sig)
      ((ids.map (targetWire source removed)).map fun wire =>
        ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).wires wire).sig) :=
  match ids with
  | [] => fun value => nomatch value
  | head :: tail =>
      fun value =>
        match value with
        | Var.here =>
            mappedHere
              (tail :=
                (tail.map (targetWire source removed)).map fun wire =>
                  ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                    source removed).wires wire).sig)
              (targetWire_signature source removed head)
        | Var.there value =>
            Var.there
              (contextRenamingFor source removed tail value)
termination_by ids

/-- Exact intrinsic renaming induced on a visible source context. -/
def contextRenaming
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming context.sigs
      (targetContext source removed context).sigs :=
  contextRenamingFor source removed context.ids

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there value =>
          exact List.mem_cons_of_mem head (induction value)

private def sourceWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WireId) :
    source.val.WireId :=
  ⟨wire.val, by
    simpa [ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate,
      ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange] using wire.isLt⟩

@[simp] private theorem sourceWire_targetWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire : source.val.WireId) :
    sourceWire source removed (targetWire source removed wire) = wire := by
  apply Fin.ext
  rfl

@[simp] private theorem targetWire_sourceWire
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (wire :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WireId) :
    targetWire source removed (sourceWire source removed wire) = wire := by
  apply Fin.ext
  rfl

private def varForMember
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId) :
    (ids : List diagram.WireId) →
      wire ∈ ids →
      Var (ids.map fun candidate => (diagram.wires candidate).sig)
        (diagram.wires wire).sig
  | [], member => by simp at member
  | head :: tail, member =>
      if equality : wire = head then
        equality ▸ .here
      else
        .there (varForMember diagram wire tail (by
          simpa [equality] using member))

@[simp] private theorem origin_varForMember
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (ids : List diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (varForMember diagram wire ids member) =
      wire := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      unfold varForMember
      split
      · rename_i equality
        subst head
        rfl
      · simp only [ConcreteElaboration.WireContext.origin]
        exact induction _

private def castVar
    (equality : sourceSig = targetSig)
    (value : Var context sourceSig) :
    Var context targetSig :=
  equality ▸ value

@[simp] private theorem origin_castVarFor
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sourceSig targetSig : Sig}
    (equality : sourceSig = targetSig)
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sourceSig) :
    ConcreteElaboration.WireContext.origin diagram ids
        (castVar equality value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases equality
  rfl

/-- The inverse intrinsic renaming for a visible erase-candidate context. -/
def contextSection
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming (targetContext source removed context).sigs
      context.sigs := fun {sig} value =>
  let targetOrigin :=
    ConcreteElaboration.WireContext.origin
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed)
      (targetContext source removed context).ids value
  let original := sourceWire source removed targetOrigin
  let sourceMember : original ∈ context.ids := by
    have targetMember :=
      origin_mem
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed) value
    rcases List.mem_map.mp targetMember with
      ⟨wire, member, equality⟩
    have originalEquality : original = wire := by
      rw [← sourceWire_targetWire source removed wire, equality]
    exact originalEquality.symm ▸ member
  let sourceVar :=
    varForMember source.val original context.ids sourceMember
  let signature : (source.val.wires original).sig = sig :=
    (targetWire_signature source removed original).symm.trans
      ((congrArg
        (fun wire =>
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).wires wire).sig)
        (targetWire_sourceWire source removed targetOrigin)).trans
      (ConcreteElaboration.WireContext.origin_signature
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed context).ids value))
  castVar signature sourceVar

private theorem contextSection_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    {sig : Sig}
    (value :
      Var (targetContext source removed context).sigs sig) :
    ConcreteElaboration.WireContext.origin source.val context.ids
        (contextSection source removed context value) =
      sourceWire source removed
        (ConcreteElaboration.WireContext.origin
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed context).ids value) := by
  unfold contextSection
  dsimp only
  exact
    (origin_castVarFor source.val context.ids _ _).trans
      (origin_varForMember _ _ _ _)

private theorem contextSection_action
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    {sig : Sig}
    (value :
      Var (targetContext source removed context).sigs sig) :
    targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val context.ids
          (contextSection source removed context value)) =
      ConcreteElaboration.WireContext.origin
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed context).ids value := by
  rw [contextSection_origin, targetWire_sourceWire]

private theorem origin_injective_of_nodup
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId}
    (nodup : ids.Nodup)
    {sig : Sig}
    (left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig)
    (sameOrigin :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  induction ids with
  | nil => exact nomatch left
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have member := origin_mem diagram right
              have equality :
                  head =
                    ConcreteElaboration.WireContext.origin
                      diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [← equality] at member
              exact (nodup.1 member).elim
      | there left =>
          cases right with
          | here =>
              have member := origin_mem diagram left
              have equality :
                  ConcreteElaboration.WireContext.origin
                      diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [equality] at member
              exact (nodup.1 member).elim
          | there right =>
              exact congrArg Var.there
                (induction nodup.2 left right (by
                  simpa [ConcreteElaboration.WireContext.origin] using
                    sameOrigin))

theorem contextRenaming_action
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val) :
    ∀ {sig} (value : Var context.sigs sig),
      ConcreteElaboration.WireContext.origin
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed context).ids
          (contextRenaming source removed context value) =
        targetWire source removed
          (ConcreteElaboration.WireContext.origin
            source.val context.ids value) := by
  intro sig value
  cases context with
  | mk ids =>
      induction ids with
      | nil => nomatch value
      | cons head tail induction =>
          cases value with
          | here =>
              simp only [contextRenaming, targetContext,
                contextRenamingFor,
                ConcreteElaboration.WireContext.origin]
              exact origin_mappedHere
                (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                  source removed)
                (targetWire source removed head)
                (tail.map (targetWire source removed))
                (targetWire_signature source removed head)
          | there value =>
              simpa [contextRenaming, contextRenamingFor, targetContext,
                ConcreteElaboration.WireContext.origin] using induction value

private theorem contextRenaming_section
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (targetNodup : (targetContext source removed context).ids.Nodup)
    {sig} (value : Var (targetContext source removed context).sigs sig) :
    contextRenaming source removed context
        (contextSection source removed context value) =
      value := by
  apply origin_injective_of_nodup
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed) targetNodup
  rw [contextRenaming_action, contextSection_action]

private theorem contextSection_renaming
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (sourceNodup : context.ids.Nodup)
    {sig} (value : Var context.sigs sig) :
    contextSection source removed context
        (contextRenaming source removed context value) =
      value := by
  apply origin_injective_of_nodup source.val sourceNodup
  apply targetWire_injective source removed
  rw [contextSection_action, contextRenaming_action]

private theorem environment_roundtrip_source
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (sourceNodup : context.ids.Nodup)
    (pre : PreModel)
    (env : Env pre context.sigs) :
    Env.comp
        (Env.comp env (contextSection source removed context))
        (contextRenaming source removed context) =
      env := by
  funext sig value
  exact congrArg (env sig)
    (contextSection_renaming source removed context sourceNodup value)

private theorem targetContext_nodup
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (nodup : context.ids.Nodup) :
    (targetContext source removed context).ids.Nodup := by
  rw [List.nodup_iff_pairwise_ne] at nodup ⊢
  exact nodup.map (targetWire source removed) (by
    intro left right different equality
    exact different ((targetWire_injective source removed) equality))

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

/-- Pull one dense target node back to its retained source node. -/
def sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).NodeId) :
    source.val.NodeId :=
  (retainedNodes source removed).get target

theorem sourceNode_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).NodeId) :
    sourceNode source removed target ≠ removed := by
  have member := List.get_mem (retainedNodes source removed) target
  exact by
    simpa [sourceNode, retainedNodes,
      ConcreteDiagram.IdentityNormalizationCore.retainedNodes] using
        of_decide_eq_true (List.mem_filter.mp member).2

@[simp] theorem targetNode_sourceNode
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (target :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).NodeId) :
    targetNode source removed (sourceNode source removed target)
        (sourceNode_ne source removed target) =
      target := by
  have nodup : (retainedNodes source removed).Nodup :=
    (Data.Finite.allFin_nodup source.val.nodeCount).filter _
  symm
  apply Data.Finite.indexOf?_unique_of_nodup nodup
  · exact Option.eq_some_of_isSome
      (Data.Finite.indexOf?_isSome_iff.mpr
        (List.get_mem (retainedNodes source removed) target))
  · rfl

/--
The source images of the dense target nodes at one retained region are exactly
the source nodes at that region with the designated singleton filtered out.
-/
theorem erased_nodesAt_sources
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).nodesAt
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
        source removed region)).map
        (sourceNode source removed) =
      (source.val.nodesAt region).filter
        (fun candidate => decide (candidate ≠ removed)) := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (((Data.Finite.allFin (retainedNodes source removed).length).filter
      ((fun candidate =>
        (source.val.nodes candidate).region == region) ∘
          sourceNode source removed)).map
      (sourceNode source removed)) =
      (((Data.Finite.allFin source.val.nodeCount).filter
        (fun candidate =>
          (source.val.nodes candidate).region == region)).filter
        (fun candidate => decide (candidate ≠ removed)))
  rw [← List.filter_map]
  have allSources :
      (Data.Finite.allFin (retainedNodes source removed).length).map
          (sourceNode source removed) =
        retainedNodes source removed := by
    simpa [sourceNode] using map_get_allFin (retainedNodes source removed)
  rw [allSources]
  simp only [retainedNodes,
    ConcreteDiagram.IdentityNormalizationCore.retainedNodes,
    List.filter_filter]
  apply List.filter_congr
  intro candidate _
  simpa using
    (Bool.and_comm
      ((source.val.nodes candidate).region == region)
      (decide (candidate ≠ removed)))

private theorem survivingNode_singleton_natural
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (target :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).NodeId)
    {sourceItems : ItemSeq definitions context.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [sourceNode source removed target] =
        some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions (targetContext source removed context).sigs,
      ConcreteElaboration.compileNodes? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed context) [target] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (contextRenaming source removed context) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    candidateWellFormed
    (targetContext_nodup source removed context contextNodup)
    (contextRenaming source removed context)
    (targetWire source removed)
    (targetWire_signature source removed)
    (contextRenaming_action source removed context)
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
      source removed)
    (sourceNode source removed target)
    target
  · simp only [
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate,
      sourceNode, retainedNodes]
    generalize nodeData :
      source.val.nodes
          ((ConcreteDiagram.IdentityNormalizationCore.retainedNodes
            source.val [removed]).get target) =
        data
    cases data <;> simp
    all_goals apply Fin.ext
    all_goals rfl
  · intro port wire incident
    simpa using
      targetEndpoint_incident source removed
        (sourceNode source removed target)
        (sourceNode_ne source removed target) port wire incident
  · exact sourceCompiled

private theorem compileNodes_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes_filter
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (removed : diagram.NodeId) :
    ∀ (nodes : List diagram.NodeId)
      {items : ItemSeq definitions context.sigs},
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
      ∃ filteredItems,
        ConcreteElaboration.compileNodes? definitions diagram context
            (nodes.filter fun node => decide (node ≠ removed)) =
          some filteredItems := by
  intro nodes
  induction nodes with
  | nil =>
      intro items compiled
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?]⟩
  | cons head tail induction =>
      intro items compiled
      obtain ⟨headItems, tailItems, headCompiled, tailCompiled, _⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions diagram context head tail items compiled
      obtain ⟨filteredTail, filteredTailCompiled⟩ :=
        induction tailCompiled
      by_cases equal : head = removed
      · have rejected : decide (head ≠ removed) = false := by
          simp [equal]
        refine ⟨filteredTail, ?_⟩
        rw [List.filter_cons, rejected]
        simpa using filteredTailCompiled
      · have accepted : decide (head ≠ removed) = true := by
          simp [equal]
        refine
          ⟨(ItemSeq.cons headItems ItemSeq.nil).append filteredTail, ?_⟩
        rw [List.filter_cons, accepted]
        simp only [↓reduceIte]
        calc
          ConcreteElaboration.compileNodes? definitions diagram context
              (head ::
                tail.filter fun node => decide (node ≠ removed)) =
              (do
                let singleton ←
                  ConcreteElaboration.compileNodes? definitions diagram
                    context [head]
                let rest ←
                  ConcreteElaboration.compileNodes? definitions diagram
                    context
                    (tail.filter fun node => decide (node ≠ removed))
                pure (singleton.append rest)) :=
            compileNodes_cons_eq_singleton_bind definitions diagram context
              head (tail.filter fun node => decide (node ≠ removed))
          _ =
              some
                ((ItemSeq.cons headItems ItemSeq.nil).append
                  filteredTail) := by
            rw [headCompiled, filteredTailCompiled]
            rfl

private theorem renameWires_append
    (rho : WireRenaming source target) :
    (left right : ItemSeq definitions source) →
      (left.append right).renameWires rho =
        (left.renameWires rho).append (right.renameWires rho)
  | .nil, _ => rfl
  | .cons head tail, right =>
      congrArg (ItemSeq.cons (head.renameWires rho))
        (renameWires_append rho tail right)

/--
Compile an ordered list of retained dense target nodes by transporting their
source singleton compilations through the exact erase-candidate context.
-/
theorem survivingNodes_natural
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup) :
    ∀ (targets :
        List
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).NodeId)
      {sourceItems : ItemSeq definitions context.sigs},
      ConcreteElaboration.compileNodes? definitions source.val context
          (targets.map (sourceNode source removed)) =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions (targetContext source removed context).sigs,
        ConcreteElaboration.compileNodes? definitions
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed)
            (targetContext source removed context) targets =
          some targetItems ∧
        targetItems =
          sourceItems.renameWires
            (contextRenaming source removed context) := by
  intro targets
  induction targets with
  | nil =>
      intro sourceItems sourceCompiled
      have equality :
          (ItemSeq.nil : ItemSeq definitions context.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?], rfl⟩
  | cons target tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, headCompiled, tailCompiled,
          sourceEquality⟩ :=
        InsertionCompilation.NaturalityInternal.compileNodes_cons_components
          definitions source.val context
          (sourceNode source removed target)
          (tail.map (sourceNode source removed)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        survivingNode_singleton_natural source removed candidateWellFormed
          context contextNodup target headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · calc
          ConcreteElaboration.compileNodes? definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (targetContext source removed context)
              (target :: tail) =
              (do
                let headItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                      source removed)
                    (targetContext source removed context) [target]
                let tailItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                      source removed)
                    (targetContext source removed context) tail
                pure (headItems.append tailItems)) :=
            compileNodes_cons_eq_singleton_bind definitions
              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                source removed)
              (targetContext source removed context) target tail
          _ = some (targetHead.append targetTail) := by
            simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, targetHeadEquality, targetTailEquality]
        rfl

/--
Transport denotation of an ordered retained-node compilation through the exact
dense erase-candidate context.  This theorem changes only the compiler-owned
wire context; it makes no claim about the removed singleton.
-/
theorem survivingNodes_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (targets :
      List
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).NodeId)
    {sourceItems : ItemSeq definitions context.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (targets.map (sourceNode source removed)) =
        some sourceItems)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source removed context).sigs) :
    ∃ targetItems :
        ItemSeq definitions (targetContext source removed context).sigs,
      ConcreteElaboration.compileNodes? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed context) targets =
        some targetItems ∧
      (denoteItemSeq pre definitionEnv targetEnv targetItems ↔
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source removed context))
          sourceItems) := by
  obtain ⟨targetItems, targetCompiled, targetExact⟩ :=
    survivingNodes_natural source removed candidateWellFormed context
      contextNodup targets sourceCompiled
  refine ⟨targetItems, targetCompiled, ?_⟩
  rw [targetExact, denoteItemSeq_renameWires]

/--
The source nodes at one region denote exactly as the erased singleton
conjoined with the dense target's retained nodes.  All target indices and the
environment pullback are determined by the canonical erase candidate.
-/
theorem erasedNodes_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed :
      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (region : source.val.RegionId)
    (removedMember : removed ∈ source.val.nodesAt region)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source removed context).sigs)
    (sourceItems : ItemSeq definitions context.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (source.val.nodesAt region) =
        some sourceItems)
    (targetItems :
      ItemSeq definitions (targetContext source removed context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed context)
          ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).nodesAt
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              source removed region)) =
        some targetItems)
    (removedItem : Item definitions context.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [removed] =
        some (.cons removedItem .nil)) :
    denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (contextRenaming source removed context))
        sourceItems ↔
      denoteItem pre definitionEnv
          (Env.comp targetEnv (contextRenaming source removed context))
          removedItem ∧
        denoteItemSeq pre definitionEnv targetEnv targetItems := by
  obtain ⟨filteredItems, filteredCompiled⟩ :=
    compileNodes_filter definitions source.val context removed
      (source.val.nodesAt region) sourceCompiled
  have sourceTargetsCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
              source removed).nodesAt
            (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
              source removed region)).map
            (sourceNode source removed)) =
        some filteredItems := by
    rw [erased_nodesAt_sources]
    exact filteredCompiled
  obtain ⟨expectedItems, expectedCompiled, targetDenotation⟩ :=
    survivingNodes_denotation source removed candidateWellFormed context
      contextNodup
      ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed).nodesAt
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          source removed region))
      sourceTargetsCompiled pre definitionEnv targetEnv
  have targetEquality : targetItems = expectedItems :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  subst targetItems
  exact
    (denote_compileNodes_filter_and_singleton definitions source.val
      context pre definitionEnv
      (Env.comp targetEnv (contextRenaming source removed context))
      (source.val.nodesAt region) removed removedMember sourceItems
      filteredItems sourceCompiled filteredCompiled removedItem
      removedCompiled).trans
        (and_congr_right fun _ => targetDenotation.symm)

/--
The relation-join checker receipt is already the canonical checked singleton
erasure consumed by this proof owner; no structural choice is reconstructed.
-/
def relationJoinStepErasure
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    CheckedErasure step.prior step.priorApplication where
  target := step.base
  generated := step.base_generated

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
