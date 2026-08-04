import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

/-! ### Generic paired replacement presentation -/

/-- The representative position chosen for an exposed pattern class carries
exactly that exposed wire. -/
theorem PlugLayout.exposedPosition_sound
    (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.pattern.val.boundary.get (layout.exposedPosition external) =
      input.pattern.val.exposedWires.get external := by
  let exposed := input.pattern.val.exposedWires.get external
  let boundary := input.pattern.val.boundary
  have hsome :
      (VisualProof.Data.Finite.indexOf? boundary exposed).isSome = true := by
    rw [VisualProof.Data.Finite.indexOf?_isSome_iff]
    exact (OpenConcreteDiagram.mem_exposedWires _ _).1
      (List.get_mem _ _)
  have hlookup : VisualProof.Data.Finite.indexOf? boundary exposed = some
      ((VisualProof.Data.Finite.indexOf? boundary exposed).get hsome) := by
    obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
    exact hfound.trans (congrArg some
      (Option.get_of_eq_some hsome hfound).symm)
  have hsound := VisualProof.Data.Finite.indexOf?_sound hlookup
  simpa only [PlugLayout.exposedPosition, exposed, boundary] using hsound

/-- Canonical intrinsic boundary substitution for one splice input.  Its
argument vector is positional while its class map identifies exactly the
repeated boundary identities declared by the checked open pattern. -/
def patternAttachmentAssignment
    (input : Input signature) :
    BoundaryAssignment input.pattern.elaborate
      (Fin input.wireQuotient.count) where
  args position := input.quotientWire (input.attachment position)
  classes external := input.plugLayout.exposedAttachment external
  agrees := by
    intro position
    change input.quotientWire
        (input.attachment
          (input.plugLayout.exposedPosition
            (input.pattern.val.boundaryClass position))) =
      input.quotientWire (input.attachment position)
    apply input.equalBoundary_quotientWire_eq
    exact (input.plugLayout.exposedPosition_sound
      (input.pattern.val.boundaryClass position)).trans
        (input.pattern.val.boundaryClass_sound position)

/-- Substituting quotient classes into the intrinsic pattern body is exactly
the open-pattern denotation at the ordered attachment values. -/
theorem denote_patternAttachmentAssignment
    (input : Input signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (values : input.wireQuotient.Carrier → model.Carrier) :
    denoteRegion (relCtx := []) model named values PUnit.unit
        (input.pattern.elaborate.substituteBoundary
          input.patternAttachmentAssignment) ↔
      input.pattern.denote model named
        (fun position =>
          values (input.quotientWire (input.attachment position))) := by
  simpa [patternAttachmentAssignment, Function.comp_def] using
    input.pattern.elaborate.denote_substituteBoundary
      input.patternAttachmentAssignment model named values

/-- Read a wire value from an exact compiler context.  Exactness supplies
existence and nodup makes the result independent of the chosen index. -/
noncomputable def exactContextValue
    {diagram : ConcreteDiagram}
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (env : Fin context.length → D)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope region) : D :=
  env (Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((exact.mem_iff wire).2 visible)))

theorem exactContextValue_eq
    {diagram : ConcreteDiagram}
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (env : Fin context.length → D)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope region)
    (index : Fin context.length)
    (indexWire : context.get index = wire) :
    exactContextValue context region exact env wire visible = env index := by
  unfold exactContextValue
  let chosen : Fin context.length := Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((exact.mem_iff wire).2 visible))
  have chosenLookup : context.lookup? wire = some chosen :=
    Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete
        ((exact.mem_iff wire).2 visible))
  have chosenWire : context.get chosen = wire :=
    ConcreteElaboration.WireContext.lookup?_sound chosenLookup
  have chosenEq : chosen = index := by
    exact (ConcreteElaboration.WireContext.lookup?_unique exact.nodup
      chosenLookup indexWire).symm
  change env chosen = env index
  rw [chosenEq]

/-- The valuation of splice quotient classes induced by an exact compiler
context at the focused site.  Invisible classes are semantically irrelevant
there and receive the supplied fallback; visible classes read the unique
compiler-context value of their plug-layout wire. -/
noncomputable def siteQuotientEnvironment
    (input : Input signature)
    (context : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (exact : context.Exact
      (input.plugLayout.frameRegion input.site))
    (env : Fin context.length → D)
    (fallback : D) :
    input.wireQuotient.Carrier → D :=
  fun quotient =>
    if visible :
        input.plugLayout.plugRaw.Encloses
          (input.plugLayout.plugRaw.wires
            (input.plugLayout.frameWire quotient)).scope
          (input.plugLayout.frameRegion input.site)
    then
      exactContextValue context
        (input.plugLayout.frameRegion input.site) exact env
        (input.plugLayout.frameWire quotient) visible
    else fallback

theorem siteQuotientEnvironment_eq
    (input : Input signature)
    (context : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (exact : context.Exact
      (input.plugLayout.frameRegion input.site))
    (env : Fin context.length → D)
    (fallback : D)
    (quotient : input.wireQuotient.Carrier)
    (visible :
      input.plugLayout.plugRaw.Encloses
        (input.plugLayout.plugRaw.wires
          (input.plugLayout.frameWire quotient)).scope
        (input.plugLayout.frameRegion input.site))
    (index : Fin context.length)
    (indexWire :
      context.get index = input.plugLayout.frameWire quotient) :
    siteQuotientEnvironment input context exact env fallback quotient =
      env index := by
  rw [siteQuotientEnvironment, dif_pos visible]
  exact exactContextValue_eq context
    (input.plugLayout.frameRegion input.site) exact env
    (input.plugLayout.frameWire quotient) visible index indexWire

/-- Every ordered attachment reads its quotient value from the unique
focused compiler-context index carrying that quotient wire. -/
theorem siteQuotientEnvironment_attachment_eq
    (input : Input signature)
    (hadmissible : input.Admissible)
    (context : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (exact : context.Exact
      (input.plugLayout.frameRegion input.site))
    (env : Fin context.length → D)
    (fallback : D)
    (position : Fin input.pattern.val.boundary.length)
    (index : Fin context.length)
    (indexWire :
      context.get index = input.plugLayout.frameWire
        (input.quotientWire (input.attachment position))) :
    siteQuotientEnvironment input context exact env fallback
        (input.quotientWire (input.attachment position)) =
      env index := by
  exact siteQuotientEnvironment_eq input context exact env fallback
    (input.quotientWire (input.attachment position))
    ((input.plugLayout.frameWire_visible_at_region_iff input.site
      (input.quotientWire (input.attachment position))).2
        (input.quotientAttachment_visible hadmissible position))
    index indexWire

/-- The canonical local valuation at an empty-spine focused site.  Retained
frame locals read their quotient value; pattern locals read the existential
hidden-root valuation supplied by the intrinsic open-pattern denotation. -/
noncomputable def focusedLocalEnvironmentOfEmpty
    (input : Input signature)
    (hzero : input.binderSpine.proxyCount = 0)
    (values : input.wireQuotient.Carrier → D)
    (hiddenEnv : Fin input.pattern.val.hiddenWires.length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site)).length → D :=
  fun index =>
    let semantic :=
      (input.plugLayout.siteLocalWireEquivOfEmpty hzero).symm index
    Fin.addCases
      (fun frame =>
        values ((ConcreteElaboration.exactScopeWires
          input.coalesceFrameRaw input.site).get frame))
      hiddenEnv semantic

@[simp] theorem focusedLocalEnvironmentOfEmpty_frame
    (input : Input signature)
    (hzero : input.binderSpine.proxyCount = 0)
    (values : input.wireQuotient.Carrier → D)
    (hiddenEnv : Fin input.pattern.val.hiddenWires.length → D)
    (frame : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv
        (input.plugLayout.siteLocalWireEquivOfEmpty hzero
          (Fin.castAdd input.pattern.val.hiddenWires.length frame)) =
      values ((ConcreteElaboration.exactScopeWires
        input.coalesceFrameRaw input.site).get frame) := by
  simp [focusedLocalEnvironmentOfEmpty,
    FiniteEquiv.symm_apply_apply, extendWireEnv]

@[simp] theorem focusedLocalEnvironmentOfEmpty_hidden
    (input : Input signature)
    (hzero : input.binderSpine.proxyCount = 0)
    (values : input.wireQuotient.Carrier → D)
    (hiddenEnv : Fin input.pattern.val.hiddenWires.length → D)
    (hidden : Fin input.pattern.val.hiddenWires.length) :
    focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv
        (input.plugLayout.siteLocalWireEquivOfEmpty hzero
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires
              input.coalesceFrameRaw input.site).length hidden)) =
      hiddenEnv hidden := by
  simp [focusedLocalEnvironmentOfEmpty,
    FiniteEquiv.symm_apply_apply, extendWireEnv]

/-- The canonical focused valuation realizes the requested quotient value at
every actual compiler-context index carrying a retained-frame wire.  Outer
indices use the caller's agreement hypothesis; exact-site indices use the
retained-frame half of `siteLocalWireEquivOfEmpty`. -/
theorem focusedExtendedEnvironment_frameWire_eq
    (input : Input signature)
    (hzero : input.binderSpine.proxyCount = 0)
    (context : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (outerEnv : Fin context.length → D)
    (values : input.wireQuotient.Carrier → D)
    (hiddenEnv : Fin input.pattern.val.hiddenWires.length → D)
    (outerValues : ∀ quotient index,
      context.get index = input.plugLayout.frameWire quotient →
        outerEnv index = values quotient)
    (quotient : input.wireQuotient.Carrier)
    (index : Fin (context.extend
      (input.plugLayout.frameRegion input.site)).length)
    (indexWire :
      (context.extend
        (input.plugLayout.frameRegion input.site)).get index =
          input.plugLayout.frameWire quotient) :
    ConcreteElaboration.extendedEnvironment context
        (input.plugLayout.frameRegion input.site) outerEnv
        (focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv) index =
      values quotient := by
  let layout := input.plugLayout
  let region := layout.frameRegion input.site
  let split : Fin (context.length +
      (ConcreteElaboration.exactScopeWires layout.plugRaw region).length) :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region) index
  have recover :
      Fin.cast
          (ConcreteElaboration.WireContext.length_extend context region).symm
          split =
        index := by
    apply Fin.ext
    rfl
  rw [← recover] at indexWire ⊢
  revert indexWire
  refine Fin.addCases (fun outer indexWire => ?_)
    (fun localIndex indexWire => ?_) split
  · have outerWire :
        context.get outer = layout.frameWire quotient := by
      have canonicalWire :
          (context.extend region).get
              (Fin.cast
                (ConcreteElaboration.WireContext.length_extend
                  context region).symm
                (Fin.castAdd
                  (ConcreteElaboration.exactScopeWires
                    layout.plugRaw region).length outer)) =
            layout.frameWire quotient := by
        simpa [region] using indexWire
      exact
        (PlugLayout.ConcreteElaboration.WireContext.extend_get_outer
          context region outer).symm.trans canonicalWire
    unfold ConcreteElaboration.extendedEnvironment
    simp only [Function.comp_apply]
    have castEq :
        Fin.cast
            (ConcreteElaboration.WireContext.length_extend context
              (input.plugLayout.frameRegion input.site))
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend context region).symm
              (Fin.castAdd
                (ConcreteElaboration.exactScopeWires layout.plugRaw region).length
                outer)) =
          Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw region).length
            outer := by
      apply Fin.ext
      rfl
    rw [castEq]
    unfold extendWireEnv
    rw [Fin.addCases_left]
    exact outerValues quotient outer outerWire
  · have localWire :
        (ConcreteElaboration.exactScopeWires layout.plugRaw region).get
            localIndex =
          layout.frameWire quotient := by
      simpa only [region,
        PlugLayout.ConcreteElaboration.WireContext.extend_get_local] using
          indexWire
    let coalescedQuotient : Fin input.coalesceFrameRaw.wireCount :=
      Fin.cast input.coalesceFrameRaw_wireCount.symm quotient
    have quotientLocal :
        coalescedQuotient ∈ ConcreteElaboration.exactScopeWires
          input.coalesceFrameRaw input.site := by
      have targetLocal :
          layout.frameWire quotient ∈
            ConcreteElaboration.exactScopeWires layout.plugRaw region := by
        rw [← localWire]
        exact List.get_mem _ localIndex
      have targetScope :=
        (ConcreteElaboration.mem_exactScopeWires layout.plugRaw region
          (layout.frameWire quotient)).1 targetLocal
      change (layout.plugWire (layout.quotientBlockWire quotient)).scope =
        layout.frameRegion input.site at targetScope
      rw [PlugLayout.plugWire_quotientBlockWire] at targetScope
      apply (ConcreteElaboration.mem_exactScopeWires
        input.coalesceFrameRaw input.site coalescedQuotient).2
      simpa [coalescedQuotient] using layout.frameRegion_injective targetScope
    obtain ⟨frame, frameGet⟩ := List.mem_iff_get.mp quotientLocal
    let mapped :=
      layout.siteLocalWireEquivOfEmpty hzero
        (Fin.castAdd input.pattern.val.hiddenWires.length frame)
    have mappedWire :
        (ConcreteElaboration.exactScopeWires layout.plugRaw region).get mapped =
          layout.frameWire quotient := by
      rw [layout.siteLocalWireEquivOfEmpty_host_spec hzero frame]
      apply congrArg layout.frameWire
      apply Fin.ext
      exact congrArg Fin.val frameGet
    have localEq : localIndex = mapped := by
      apply Fin.ext
      exact (List.getElem_inj
        (ConcreteElaboration.exactScopeWires_nodup layout.plugRaw region)).mp
          (localWire.trans mappedWire.symm)
    subst localIndex
    have mappedValue :
        focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv mapped =
          values ((ConcreteElaboration.exactScopeWires
            input.coalesceFrameRaw input.site).get frame) := by
      exact focusedLocalEnvironmentOfEmpty_frame input hzero values
        hiddenEnv frame
    have targetValue :
        focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv mapped =
          values quotient := mappedValue.trans (by
        apply congrArg values
        apply Fin.ext
        exact congrArg Fin.val frameGet)
    simpa [ConcreteElaboration.extendedEnvironment, region, extendWireEnv] using
      targetValue

/-- Intrinsic pattern-root items under the canonical focused-context map
entail the checked pattern at the quotient valuation.  This theorem owns the
environment reconstruction independently of how the root-item denotation was
transported from a concrete focused conjunction. -/
theorem pattern_denote_of_patternRootItems
    (input : Input signature)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (fallback : model.Carrier)
    (patternDenotes :
      let pattern := compiledSpliceOpenRootItems input.pattern
      denoteItemSeq (relCtx := []) model named
        (env ∘ input.plugLayout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf)
        (PUnit.unit : RelEnv model.Carrier []) pattern.items) :
    input.pattern.denote model named (fun position =>
      siteQuotientEnvironment input
        (outputLeaf.inheritedWires.extend
          (input.plugLayout.frameRegion input.site))
        outputLeaf.wiresExact env fallback
        (input.quotientWire (input.attachment position))) := by
  let layout := input.plugLayout
  let context := outputLeaf.inheritedWires.extend
    (layout.frameRegion input.site)
  let values := siteQuotientEnvironment input context
    outputLeaf.wiresExact env fallback
  let assignment := input.patternAttachmentAssignment.map values
  let pattern := compiledSpliceOpenRootItems input.pattern
  let hiddenEnv : Fin input.pattern.val.hiddenWires.length → model.Carrier :=
    fun hidden =>
      env (layout.patternRootWireIndexMap hadmissible hzero
        outputWitness outputLeaf
        (Fin.cast (by simp)
          (Fin.natAdd input.pattern.val.exposedWires.length hidden)))
  have rootEnvironmentEq :
      env ∘ layout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf =
        extendWireEnv assignment.classes hiddenEnv ∘ Fin.cast (by simp) := by
    funext index
    let split : Fin (input.pattern.val.exposedWires.length +
        input.pattern.val.hiddenWires.length) := Fin.cast (by simp) index
    have recover : Fin.cast (by simp) split = index := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun external => ?_) (fun hidden => ?_) split
    · let rootIndex : Fin
          (input.pattern.val.exposedWires ++
            input.pattern.val.hiddenWires).length :=
        Fin.cast (by simp)
          (Fin.castAdd input.pattern.val.hiddenWires.length external)
      have rootWire :
          (input.pattern.val.exposedWires ++
            input.pattern.val.hiddenWires).get rootIndex =
          input.pattern.val.exposedWires.get external := by
        simp [rootIndex]
      have indexWire :
          context.get
              (layout.patternRootWireIndexMap hadmissible hzero
                outputWitness outputLeaf rootIndex) =
            layout.frameWire (layout.exposedAttachment external) := by
        rw [layout.patternRootWireIndexMap_spec hadmissible hzero
          outputWitness outputLeaf, rootWire]
        rw [layout.patternPlugWire_exposed
          (input.pattern.val.exposedWires.get external)
          (List.get_mem _ external)]
        have externalIndex :
            PlugLayout.exposedWireIndex input
                (input.pattern.val.exposedWires.get external)
                (List.get_mem _ external) =
              external := by
          apply PlugLayout.exposedWire_get_injective input
          exact PlugLayout.exposedWireIndex_get input
            (input.pattern.val.exposedWires.get external)
            (List.get_mem _ external)
        rw [externalIndex]
        rfl
      have visible :
          layout.plugRaw.Encloses
            (layout.plugRaw.wires
              (layout.frameWire
                (layout.exposedAttachment external))).scope
            (layout.frameRegion input.site) :=
        (layout.frameWire_visible_at_region_iff input.site
          (layout.exposedAttachment external)).2
          (input.quotientAttachment_visible hadmissible
            (layout.exposedPosition external))
      have valueEq :
          values (layout.exposedAttachment external) =
            env (layout.patternRootWireIndexMap hadmissible hzero
              outputWitness outputLeaf rootIndex) :=
        siteQuotientEnvironment_eq input context outputLeaf.wiresExact env
          fallback (layout.exposedAttachment external) visible
          (layout.patternRootWireIndexMap hadmissible hzero
            outputWitness outputLeaf rootIndex) indexWire
      simpa [split, rootIndex, assignment, patternAttachmentAssignment,
        BoundaryAssignment.map, values, Function.comp_def, extendWireEnv] using
          valueEq.symm
    · simp [split, hiddenEnv, Function.comp_def, extendWireEnv]
  change denoteOpen model named input.pattern.elaborate
    (fun position => values
      (input.quotientWire (input.attachment position)))
  refine ⟨assignment, ?_, ?_⟩
  · rfl
  · rw [pattern.elaborate_body]
    unfold ConcreteElaboration.finishRoot
    refine ⟨hiddenEnv, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires]
    apply (denoteItemSeq_renameWires (relCtx := []) model named
      (Fin.cast (by simp [OpenConcreteDiagram.rootWires]))
      (extendWireEnv assignment.classes hiddenEnv)
      (PUnit.unit : RelEnv model.Carrier []) pattern.items).mpr
    exact Eq.mp
      (congrArg (fun wireEnv :
          Fin input.pattern.val.rootWires.length → model.Carrier =>
        denoteItemSeq (relCtx := []) model named wireEnv
          (PUnit.unit : RelEnv model.Carrier []) pattern.items)
        rootEnvironmentEq)
      patternDenotes

/-- A checked empty-spine pattern denotation exposes the hidden root
valuation and the actual intrinsic item conjunction emitted by the compiler.
The exposed part is the canonical quotient-class assignment used by the
splice input, so the result can be transported occurrence-by-occurrence into
the concrete focused context. -/
theorem patternRootItems_of_pattern_denote
    (input : Input signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (values : input.wireQuotient.Carrier → model.Carrier)
    (denotes : input.pattern.denote model named (fun position =>
      values (input.quotientWire (input.attachment position)))) :
    let pattern := compiledSpliceOpenRootItems input.pattern
    ∃ hiddenEnv : Fin input.pattern.val.hiddenWires.length → model.Carrier,
      denoteItemSeq (relCtx := []) model named
        (extendWireEnv
          (input.patternAttachmentAssignment.map values).classes hiddenEnv ∘
            Fin.cast (by simp [OpenConcreteDiagram.rootWires]))
        (PUnit.unit : RelEnv model.Carrier []) pattern.items := by
  dsimp only
  let pattern := compiledSpliceOpenRootItems input.pattern
  have substituted :
      denoteRegion (relCtx := []) model named values PUnit.unit
        (input.pattern.elaborate.substituteBoundary
          input.patternAttachmentAssignment) :=
    (input.denote_patternAttachmentAssignment model named values).2 denotes
  rw [OpenDiagram.substituteBoundary, denoteRegion_renameWires] at substituted
  rw [pattern.elaborate_body] at substituted
  unfold ConcreteElaboration.finishRoot at substituted
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
    at substituted
  obtain ⟨hiddenEnv, hiddenDenotes⟩ := substituted
  refine ⟨hiddenEnv, ?_⟩
  have classesEq :
      values ∘ input.patternAttachmentAssignment.classes =
        (input.patternAttachmentAssignment.map values).classes := rfl
  rw [← classesEq]
  exact (denoteItemSeq_renameWires (relCtx := []) model named
    (Fin.cast (by simp [OpenConcreteDiagram.rootWires]))
    (extendWireEnv
      (values ∘ input.patternAttachmentAssignment.classes) hiddenEnv)
    (PUnit.unit : RelEnv model.Carrier []) pattern.items).mp hiddenDenotes

/-- The canonical focused valuation realizes exactly the intrinsic
empty-spine root valuation: exposed root wires read their quotient values and
hidden root wires read the supplied hidden witness. -/
theorem focusedExtendedEnvironment_patternRoot_eq
    (input : Input signature)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (outerEnv : Fin outputLeaf.inheritedWires.length → D)
    (values : input.wireQuotient.Carrier → D)
    (hiddenEnv : Fin input.pattern.val.hiddenWires.length → D)
    (outerValues : ∀ quotient index,
      outputLeaf.inheritedWires.get index =
          input.plugLayout.frameWire quotient →
        outerEnv index = values quotient) :
    ConcreteElaboration.extendedEnvironment outputLeaf.inheritedWires
        (input.plugLayout.frameRegion input.site) outerEnv
        (focusedLocalEnvironmentOfEmpty input hzero values hiddenEnv) ∘
          input.plugLayout.patternRootWireIndexMap hadmissible hzero
            outputWitness outputLeaf =
      extendWireEnv
          (input.patternAttachmentAssignment.map values).classes hiddenEnv ∘
        Fin.cast (by simp [OpenConcreteDiagram.rootWires]) := by
  funext index
  let split : Fin (input.pattern.val.exposedWires.length +
      input.pattern.val.hiddenWires.length) := Fin.cast (by simp) index
  have recover : Fin.cast (by simp) split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  · let rootIndex : Fin
        (input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).length :=
      Fin.cast (by simp)
        (Fin.castAdd input.pattern.val.hiddenWires.length exposed)
    have rootWire :
        (input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).get rootIndex =
        input.pattern.val.exposedWires.get exposed := by
      simp [rootIndex]
    have indexWire :
        (outputLeaf.inheritedWires.extend
          (input.plugLayout.frameRegion input.site)).get
            (input.plugLayout.patternRootWireIndexMap hadmissible hzero
              outputWitness outputLeaf rootIndex) =
          input.plugLayout.frameWire
            (input.plugLayout.exposedAttachment exposed) := by
      rw [input.plugLayout.patternRootWireIndexMap_spec hadmissible hzero
        outputWitness outputLeaf, rootWire]
      rw [input.plugLayout.patternPlugWire_exposed
        (input.pattern.val.exposedWires.get exposed)
        (List.get_mem _ exposed)]
      have externalIndex :
          PlugLayout.exposedWireIndex input
              (input.pattern.val.exposedWires.get exposed)
              (List.get_mem _ exposed) =
            exposed := by
        apply PlugLayout.exposedWire_get_injective input
        exact PlugLayout.exposedWireIndex_get input
          (input.pattern.val.exposedWires.get exposed)
          (List.get_mem _ exposed)
      rw [externalIndex]
      rfl
    have focusedValue :=
      focusedExtendedEnvironment_frameWire_eq input hzero
        outputLeaf.inheritedWires outerEnv values hiddenEnv outerValues
        (input.plugLayout.exposedAttachment exposed)
        (input.plugLayout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf rootIndex) indexWire
    simpa [split, rootIndex, patternAttachmentAssignment,
      BoundaryAssignment.map, extendWireEnv] using focusedValue
  · let rootIndex : Fin
        (input.pattern.val.exposedWires ++
          input.pattern.val.hiddenWires).length :=
      Fin.cast (by simp)
        (Fin.natAdd input.pattern.val.exposedWires.length hidden)
    let host := compiledSpliceHostView input hadmissible
    have seamEq :=
      input.plugLayout.patternRootSeamWireMapOfEmpty_eq hadmissible host
        outputWitness outputLeaf hzero
    have rootMapEq :
        input.plugLayout.patternRootWireIndexMap hadmissible hzero
            outputWitness outputLeaf rootIndex =
          Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              outputLeaf.inheritedWires
              (input.plugLayout.frameRegion input.site)).symm
            (Fin.natAdd outputLeaf.inheritedWires.length
              (input.plugLayout.siteLocalWireEquivOfEmpty hzero
                (Fin.natAdd
                  (ConcreteElaboration.exactScopeWires
                    input.coalesceFrameRaw input.site).length hidden))) := by
      rw [← seamEq]
      apply Fin.ext
      simp [rootIndex, PlugLayout.patternRootSeamWireMapOfEmpty,
        PlugLayout.patternRootSeamPreparedWireOfEmpty,
        PlugLayout.siteCombinedWireEquivOfEmpty, extendWireEquiv]
    have presentedIndexEq :
        Fin.cast (by simp)
            (Fin.natAdd input.pattern.val.exposedWires.length hidden) =
          rootIndex := rfl
    simp only [Function.comp_apply]
    rw [presentedIndexEq, rootMapEq]
    simp [split, rootIndex, ConcreteElaboration.extendedEnvironment,
      focusedLocalEnvironmentOfEmpty, extendWireEnv]

/-- Boundary aliasing may change only the quotient classes whose original
retained wires are all scoped exactly at the splice site.  Any pair involving
an outer-scoped wire has the same quotient equality on both sides, so replacing
the focused conjunction cannot move an existential wire binder across its
enclosing logical context. -/
def SiteLocalQuotientAgreement
    (source target : Input signature)
    (frameEq : source.frame = target.frame) : Prop :=
  ∀ left right : Fin source.frame.val.wireCount,
    (source.frame.val.wires left).scope ≠ source.site ∨
      (source.frame.val.wires right).scope ≠ source.site →
    (source.quotientWire left = source.quotientWire right ↔
      target.quotientWire
          (Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
            checked.val.wireCount) frameEq) left) =
        target.quotientWire
          (Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
            checked.val.wireCount) frameEq) right))

instance (source target : Input signature)
    (frameEq : source.frame = target.frame) :
    Decidable (SiteLocalQuotientAgreement source target frameEq) := by
  unfold SiteLocalQuotientAgreement
  exact @Nat.decidableForallFin _ _ fun _ =>
    @Nat.decidableForallFin _ _ fun _ => inferInstance

/-- Structural presentation shared by two canonical splice inputs over the
same retained frame and site. Ordered positions agree. Boundary quotient
partitions may differ only at the focused site's own wire-binding level. -/
structure TwoInputPresentation (source target : Input signature) where
  frame_eq : source.frame = target.frame
  site_eq :
    Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
      checked.val.regionCount) frame_eq) source.site = target.site
  boundary_arity_eq : source.pattern.val.boundary.length =
    target.pattern.val.boundary.length
  attachment_eq : ∀ position,
    Fin.cast (congrArg (fun checked : CheckedDiagram signature =>
      checked.val.wireCount) frame_eq) (source.attachment position) =
      target.attachment (Fin.cast boundary_arity_eq position)
  site_local_quotients :
    SiteLocalQuotientAgreement source target frame_eq

end VisualProof.Diagram.Splice.Input
