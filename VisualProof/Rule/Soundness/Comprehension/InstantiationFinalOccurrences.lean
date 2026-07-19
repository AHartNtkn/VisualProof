import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalFrame
import VisualProof.Rule.Soundness.Comprehension.InstantiationDropCompiler
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Presentation.Compiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace InstantiationTrace

/-- Composite image of a frame occurrence through every accepted copy step.
This map precedes processed-atom compaction and final vacuous promotion. -/
def frameOccurrenceMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result) :
    ConcreteElaboration.LocalOccurrence state.diagram.val.regionCount
        state.diagram.val.nodeCount →
      ConcreteElaboration.LocalOccurrence result.diagram.val.regionCount
        result.diagram.val.nodeCount
  | .node node => .node (trace.nodeMap node)
  | .child region => .child (trace.regionMap region)

@[simp] theorem frameOccurrenceMap_node
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (node : Fin state.diagram.val.nodeCount) :
    trace.frameOccurrenceMap (.node node) = .node (trace.nodeMap node) :=
  rfl

@[simp] theorem frameOccurrenceMap_child
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (region : Fin state.diagram.val.regionCount) :
    trace.frameOccurrenceMap (.child region) =
      .child (trace.regionMap region) :=
  rfl

/-- Copying is exact on the compiler traversal of every region outside the
moving quantified bubble.  The active site is enclosed by that bubble, so the
executor's off-site frame theorem applies at every recursive step. -/
theorem localOccurrences_frameMap_of_outside
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (region : Fin state.diagram.val.regionCount)
    (outside : ¬ state.diagram.val.Encloses state.bubble region) :
    ConcreteElaboration.localOccurrences result.diagram.val
        (trace.regionMap region) =
      (ConcreteElaboration.localOccurrences state.diagram.val region).map
        trace.frameOccurrenceMap := by
  induction trace with
  | done fuel state pending_empty =>
      change ConcreteElaboration.localOccurrences state.diagram.val region =
        (ConcreteElaboration.localOccurrences state.diagram.val region).map
          (fun occurrence => match occurrence with
            | .node node => .node node
            | .child child => .child child)
      have occurrenceMapId :
          (fun occurrence : ConcreteElaboration.LocalOccurrence
              state.diagram.val.regionCount state.diagram.val.nodeCount =>
            match occurrence with
            | .node node => .node node
            | .child child => .child child) = id := by
        funext occurrence
        cases occurrence <;> rfl
      rw [occurrenceMapId, List.map_id]
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      let next := advanceInstantiationState comprehension attachments binders
        payload state atom tail site arguments hadmissible
      have nodeEq : state.diagram.val.nodes atom = .atom site state.bubble := by
        simpa [candidate_eq] using node_eq
      have bubbleEnclosesSite :
          state.diagram.val.Encloses state.bubble site := by
        simpa [nodeEq] using state.diagram.property.atom_binders_enclose atom
      have regionNeSite : region ≠ site := by
        intro equal
        exact outside (equal ▸ bubbleEnclosesSite)
      have first :=
        Splice.Input.TwoInputPresentation.localOccurrences_frameRegion layout
          region regionNeSite
      have first' :
          ConcreteElaboration.localOccurrences next.diagram.val
              (layout.frameRegion region) =
            (ConcreteElaboration.localOccurrences state.diagram.val region).map
              layout.mapFrameOccurrence := by
        simpa [next, advanceInstantiationState, spliceInput,
          ConcreteElaboration.localOccurrences] using first
      have nextOutside :
          ¬ next.diagram.val.Encloses next.bubble
            (layout.frameRegion region) := by
        intro enclosed
        have mapped : layout.plugRaw.Encloses
            (layout.frameRegion state.bubble) (layout.frameRegion region) := by
          simpa [next, advanceInstantiationState, spliceInput] using enclosed
        exact outside ((layout.frame_encloses_iff state.bubble region).1 mapped)
      have tailEq := ih (layout.frameRegion region) nextOutside
      simp only [regionMap, Function.comp_apply]
      rw [tailEq, first']
      induction ConcreteElaboration.localOccurrences state.diagram.val region with
      | nil => rfl
      | cons occurrence occurrences ih =>
          cases occurrence <;>
            change _ :: _ = _ :: _ <;>
            congr 1

private theorem list_map_cancel
    (map : α → β)
    (injective : Function.Injective map) :
    Function.Injective (List.map map) := by
  intro left right equal
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => cases equal
  | cons head tail ih =>
      cases right with
      | nil => cases equal
      | cons other rest =>
          injection equal with headEq tailEq
          have headEqual := injective headEq
          have tailEqual := ih tailEq
          subst other
          subst rest
          rfl

theorem dropOccurrenceOrigin_injective
    (state : InstantiationState origin parameterCount proxyCount) :
    Function.Injective
      (InstantiationSemantic.dropOccurrenceOrigin state) := by
  intro left right equal
  cases left with
  | node leftNode =>
      cases right with
      | node rightNode =>
          congr 1
          injection equal with originEq
          exact (instantiationAtomDomain state).origin_injective originEq
      | child rightChild => cases equal
  | child leftChild =>
      cases right with
      | node rightNode => cases equal
      | child rightChild =>
          congr 1
          exact ConcreteElaboration.LocalOccurrence.child.inj equal

/-- Total occurrence map for an arbitrary source region outside the moving
quantified bubble.  Unlike `droppedFrameOccurrenceMap`, this also applies to
the quantified bubble's parent, whose child occurrence is needed by the
focused compiler proof. -/
def droppedOutsideOccurrenceMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (outside : ¬ input.val.Encloses bubble region) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount
  | .node node =>
      if nodeRegion : (input.val.nodes node).region = region then
        .node (copyTrace.droppedNodeMap node (fun enclosed =>
          outside (nodeRegion ▸ enclosed)))
      else
        .child (copyTrace.regionMap region)
  | .child child => .child (copyTrace.regionMap child)

private theorem frameOccurrence_survives_of_outside
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (outside : ¬ input.val.Encloses bubble region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region) :
    InstantiationSemantic.dropOccurrenceSurvives result
        (copyTrace.frameOccurrenceMap occurrence) = true := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          member
      exact copyTrace.nodeMap_survives_drop node (fun enclosed =>
        outside (nodeRegion ▸ enclosed))
  | child child => rfl

private theorem dropOrigin_droppedOutsideOccurrenceMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (outside : ¬ input.val.Encloses bubble region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region) :
    InstantiationSemantic.dropOccurrenceOrigin result
        (copyTrace.droppedOutsideOccurrenceMap region outside occurrence) =
      copyTrace.frameOccurrenceMap occurrence := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          member
      simp only [droppedOutsideOccurrenceMap, dif_pos nodeRegion,
        InstantiationSemantic.dropOccurrenceOrigin, frameOccurrenceMap]
      exact congrArg ConcreteElaboration.LocalOccurrence.node
        (copyTrace.droppedNodeMap_origin node (fun enclosed =>
          outside (nodeRegion ▸ enclosed)))
  | child child => rfl

/-- Atom compaction preserves the exact ordered local traversal of every
region outside the moving quantified bubble, including its parent. -/
theorem dropped_localOccurrences_of_outside
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (outside : ¬ input.val.Encloses bubble region) :
    ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap region) =
      (ConcreteElaboration.localOccurrences input.val region).map
        (copyTrace.droppedOutsideOccurrenceMap region outside) := by
  let occurrences := ConcreteElaboration.localOccurrences input.val region
  have copied :
      ConcreteElaboration.localOccurrences result.diagram.val
          (copyTrace.regionMap region) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    simpa [occurrences, initialInstantiationState] using
      copyTrace.localOccurrences_frameMap_of_outside region outside
  have allSurvive :
      (occurrences.map copyTrace.frameOccurrenceMap).filter
          (InstantiationSemantic.dropOccurrenceSurvives result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    apply List.filter_eq_self.mpr
    intro mapped mappedMember
    obtain ⟨occurrence, member, rfl⟩ := List.mem_map.mp mappedMember
    exact frameOccurrence_survives_of_outside copyTrace region outside
      occurrence member
  have originLeft :
      (ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
          (copyTrace.regionMap region)).map
          (InstantiationSemantic.dropOccurrenceOrigin result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    rw [InstantiationSemantic.dropInstantiationAtomsRaw_localOccurrences_origin,
      copied, allSurvive]
  have originRight :
      (occurrences.map
          (copyTrace.droppedOutsideOccurrenceMap region outside)).map
          (InstantiationSemantic.dropOccurrenceOrigin result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    have pointwise : ∀ occurrence ∈ occurrences,
        InstantiationSemantic.dropOccurrenceOrigin result
            (copyTrace.droppedOutsideOccurrenceMap region outside occurrence) =
          copyTrace.frameOccurrenceMap occurrence := by
      intro occurrence member
      exact dropOrigin_droppedOutsideOccurrenceMap copyTrace region outside
        occurrence member
    have mapPointwise : ∀ values : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        (∀ occurrence ∈ values,
          InstantiationSemantic.dropOccurrenceOrigin result
              (copyTrace.droppedOutsideOccurrenceMap region outside occurrence) =
            copyTrace.frameOccurrenceMap occurrence) →
        (values.map
            (copyTrace.droppedOutsideOccurrenceMap region outside)).map
            (InstantiationSemantic.dropOccurrenceOrigin result) =
          values.map copyTrace.frameOccurrenceMap := by
      intro values allPointwise
      induction values with
      | nil => rfl
      | cons occurrence rest ih =>
          have headEq := allPointwise occurrence List.mem_cons_self
          have tailPointwise : ∀ value ∈ rest,
              InstantiationSemantic.dropOccurrenceOrigin result
                  (copyTrace.droppedOutsideOccurrenceMap region outside value) =
                copyTrace.frameOccurrenceMap value := by
            intro value member
            exact allPointwise value
              (List.mem_cons_of_mem occurrence member)
          have tailEq := ih tailPointwise
          change InstantiationSemantic.dropOccurrenceOrigin result
                (copyTrace.droppedOutsideOccurrenceMap region outside
                  occurrence) :: _ =
              copyTrace.frameOccurrenceMap occurrence :: _
          rw [headEq]
          congr 1
    exact mapPointwise occurrences pointwise
  apply list_map_cancel (InstantiationSemantic.dropOccurrenceOrigin result)
    (dropOccurrenceOrigin_injective result)
  exact originLeft.trans originRight.symm

/-- Total source-frame occurrence map after processed-atom compaction.  The
fallback branch is irrelevant to a regular local traversal; it makes the map
total without pretending that nodes inside the rewritten bubble survive. -/
def droppedFrameOccurrenceMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount
  | .node node =>
      if nodeRegion : (input.val.nodes node).region = region then
        .node (copyTrace.droppedNodeMap node
          (node_outside_bubble_of_regular payload region regular node
            nodeRegion))
      else
        .child (copyTrace.regionMap region)
  | .child child => .child (copyTrace.regionMap child)

private theorem frameOccurrence_survives_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region) :
    InstantiationSemantic.dropOccurrenceSurvives result
        (copyTrace.frameOccurrenceMap occurrence) = true := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          member
      exact copyTrace.nodeMap_survives_drop node
        (node_outside_bubble_of_regular payload region regular node nodeRegion)
  | child child => rfl

private theorem dropOrigin_droppedFrameOccurrenceMap_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region) :
    InstantiationSemantic.dropOccurrenceOrigin result
        (copyTrace.droppedFrameOccurrenceMap region regular occurrence) =
      copyTrace.frameOccurrenceMap occurrence := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          member
      simp only [droppedFrameOccurrenceMap, dif_pos nodeRegion,
        InstantiationSemantic.dropOccurrenceOrigin, frameOccurrenceMap]
      exact congrArg ConcreteElaboration.LocalOccurrence.node
        (copyTrace.droppedNodeMap_origin node
          (node_outside_bubble_of_regular payload region regular node
            nodeRegion))
  | child child => rfl

/-- Atom compaction preserves the exact ordered local traversal of every
regular frame region. -/
theorem dropped_localOccurrences_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region) :
    ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap region) =
      (ConcreteElaboration.localOccurrences input.val region).map
        (copyTrace.droppedFrameOccurrenceMap region regular) := by
  let occurrences := ConcreteElaboration.localOccurrences input.val region
  have outsideBubble : ¬ input.val.Encloses bubble region := regular.1
  have copied :
      ConcreteElaboration.localOccurrences result.diagram.val
          (copyTrace.regionMap region) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    simpa [occurrences, initialInstantiationState] using
      copyTrace.localOccurrences_frameMap_of_outside region outsideBubble
  have allSurvive :
      (occurrences.map copyTrace.frameOccurrenceMap).filter
          (InstantiationSemantic.dropOccurrenceSurvives result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    apply List.filter_eq_self.mpr
    intro mapped mappedMember
    obtain ⟨occurrence, member, rfl⟩ := List.mem_map.mp mappedMember
    exact frameOccurrence_survives_of_regular copyTrace region regular
      occurrence member
  have droppedOrigin :=
    InstantiationSemantic.dropInstantiationAtomsRaw_localOccurrences_origin
      result (copyTrace.regionMap region)
  have originLeft :
      (ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
          (copyTrace.regionMap region)).map
          (InstantiationSemantic.dropOccurrenceOrigin result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    rw [droppedOrigin, copied, allSurvive]
  have originRight :
      (occurrences.map
          (copyTrace.droppedFrameOccurrenceMap region regular)).map
          (InstantiationSemantic.dropOccurrenceOrigin result) =
        occurrences.map copyTrace.frameOccurrenceMap := by
    have pointwise : ∀ occurrence ∈ occurrences,
        InstantiationSemantic.dropOccurrenceOrigin result
            (copyTrace.droppedFrameOccurrenceMap region regular occurrence) =
          copyTrace.frameOccurrenceMap occurrence := by
      intro occurrence member
      exact dropOrigin_droppedFrameOccurrenceMap_of_regular copyTrace region
        regular occurrence member
    have mapPointwise : ∀ values : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        (∀ occurrence ∈ values,
          InstantiationSemantic.dropOccurrenceOrigin result
              (copyTrace.droppedFrameOccurrenceMap region regular occurrence) =
            copyTrace.frameOccurrenceMap occurrence) →
        (values.map
            (copyTrace.droppedFrameOccurrenceMap region regular)).map
            (InstantiationSemantic.dropOccurrenceOrigin result) =
          values.map copyTrace.frameOccurrenceMap := by
      intro values allPointwise
      induction values with
      | nil => rfl
      | cons occurrence rest ih =>
          have headEq := allPointwise occurrence List.mem_cons_self
          have tailPointwise : ∀ value ∈ rest,
              InstantiationSemantic.dropOccurrenceOrigin result
                  (copyTrace.droppedFrameOccurrenceMap region regular value) =
                copyTrace.frameOccurrenceMap value := by
            intro value member
            exact allPointwise value (List.mem_cons_of_mem occurrence member)
          have tailEq := ih tailPointwise
          change InstantiationSemantic.dropOccurrenceOrigin result
                (copyTrace.droppedFrameOccurrenceMap region regular occurrence) ::
                _ = copyTrace.frameOccurrenceMap occurrence :: _
          rw [headEq]
          congr 1
    exact mapPointwise occurrences pointwise
  apply list_map_cancel (InstantiationSemantic.dropOccurrenceOrigin result)
    (dropOccurrenceOrigin_injective result)
  exact originLeft.trans originRight.symm

private theorem vacuousOccurrenceMap_injective
    (trace : VacuousElimTrace input bubble raw) :
    Function.Injective trace.occurrenceMap := by
  intro left right equal
  cases left with
  | node leftNode =>
      cases right with
      | node rightNode =>
          congr 1
          exact ConcreteElaboration.LocalOccurrence.node.inj equal
      | child rightChild => cases equal
  | child leftChild =>
      cases right with
      | node rightNode => cases equal
      | child rightChild =>
          congr 1
          injection equal with originEq
          exact trace.origin_injective originEq

/-- Total source-frame occurrence map after the complete operational
instantiation trace.  On a regular local traversal every node takes the
certified node branch; the fallback only totalizes the function. -/
def finalFrameOccurrenceMap
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence
        elimTrace.sourceDiagram.regionCount elimTrace.sourceDiagram.nodeCount
  | .node node =>
      if nodeRegion : (input.val.nodes node).region = region then
        .node (copyTrace.finalNodeMap elimTrace node
          (node_outside_bubble_of_regular payload region regular node
            nodeRegion))
      else
        .child (copyTrace.finalRegionMap elimTrace finalWellFormed region)
  | .child child =>
      .child (copyTrace.finalRegionMap elimTrace finalWellFormed child)

private theorem vacuousOrigin_finalFrameOccurrenceMap_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (member : occurrence ∈
      ConcreteElaboration.localOccurrences input.val region) :
    elimTrace.occurrenceMap
        (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed region
          regular occurrence) =
      copyTrace.droppedFrameOccurrenceMap region regular occurrence := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val region node).1
          member
      simp only [finalFrameOccurrenceMap, droppedFrameOccurrenceMap,
        dif_pos nodeRegion, VacuousElimTrace.occurrenceMap, finalNodeMap]
  | child child =>
      have childParent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val region child).1
          member
      have childNeBubble : child ≠ bubble := by
        intro equal
        subst child
        have parentEq : payload.parent = region := by
          rw [payload.bubble_eq] at childParent
          exact Option.some.inj (by
            simpa [CRegion.parent?] using childParent)
        exact regular.2 parentEq.symm
      have originEq := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
        finalWellFormed child childNeBubble
      exact congrArg ConcreteElaboration.LocalOccurrence.child originEq

/-- The complete executor trace preserves the exact ordered local traversal
of every region outside the quantified parent subtree. -/
theorem final_localOccurrences_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (region : Fin input.val.regionCount)
    (regular : FrameRegular payload region) :
    ConcreteElaboration.localOccurrences elimTrace.sourceDiagram
        (copyTrace.finalRegionMap elimTrace finalWellFormed region) =
      (ConcreteElaboration.localOccurrences input.val region).map
        (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed region
          regular) := by
  let occurrences := ConcreteElaboration.localOccurrences input.val region
  have regionNeBubble : region ≠ bubble := by
    intro equal
    subst region
    exact regular.1 (ConcreteDiagram.Encloses.refl input.val bubble)
  have mappedRegular : copyTrace.finalRegionMap elimTrace finalWellFormed
      region ≠ elimTrace.targetIndex finalWellFormed := by
    intro mapped
    rcases (copyTrace.finalRegionMap_eq_targetIndex_iff elimTrace
      finalWellFormed region).1 mapped with parentEq | bubbleEq
    · exact regular.2 parentEq
    · exact regionNeBubble bubbleEq
  have originRegion := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed region regionNeBubble
  have promoted := elimTrace.regular_localOccurrences finalWellFormed
    (copyTrace.finalRegionMap elimTrace finalWellFormed region) mappedRegular
  have promotedOrigin :
      (ConcreteElaboration.localOccurrences elimTrace.sourceDiagram
          (copyTrace.finalRegionMap elimTrace finalWellFormed region)).map
          elimTrace.occurrenceMap =
        ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
          (copyTrace.regionMap region) := by
    rw [← promoted]
    exact congrArg
      (ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result))
      originRegion
  have dropped := copyTrace.dropped_localOccurrences_of_regular region regular
  have mappedOrigin :
      (occurrences.map
          (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed region
            regular)).map elimTrace.occurrenceMap =
        occurrences.map
          (copyTrace.droppedFrameOccurrenceMap region regular) := by
    have pointwise : ∀ occurrence ∈ occurrences,
        elimTrace.occurrenceMap
            (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed region
              regular occurrence) =
          copyTrace.droppedFrameOccurrenceMap region regular occurrence := by
      intro occurrence member
      exact vacuousOrigin_finalFrameOccurrenceMap_of_regular copyTrace elimTrace
        finalWellFormed region regular occurrence member
    have mapPointwise : ∀ values : List
        (ConcreteElaboration.LocalOccurrence input.val.regionCount
          input.val.nodeCount),
        (∀ occurrence ∈ values,
          elimTrace.occurrenceMap
              (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                region regular occurrence) =
            copyTrace.droppedFrameOccurrenceMap region regular occurrence) →
        (values.map
            (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed region
              regular)).map elimTrace.occurrenceMap =
          values.map
            (copyTrace.droppedFrameOccurrenceMap region regular) := by
      intro values allPointwise
      induction values with
      | nil => rfl
      | cons occurrence rest ih =>
          have headEq := allPointwise occurrence List.mem_cons_self
          have tailPointwise : ∀ value ∈ rest,
              elimTrace.occurrenceMap
                  (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                    region regular value) =
                copyTrace.droppedFrameOccurrenceMap region regular value := by
            intro value member
            exact allPointwise value (List.mem_cons_of_mem occurrence member)
          have tailEq := ih tailPointwise
          change elimTrace.occurrenceMap
                (copyTrace.finalFrameOccurrenceMap elimTrace finalWellFormed
                  region regular occurrence) :: _ =
              copyTrace.droppedFrameOccurrenceMap region regular occurrence :: _
          rw [headEq]
          congr 1
    exact mapPointwise occurrences pointwise
  apply list_map_cancel elimTrace.occurrenceMap
    (vacuousOccurrenceMap_injective elimTrace)
  exact promotedOrigin.trans (by
    rw [dropped]
    exact mappedOrigin.symm)

end InstantiationTrace

end VisualProof.Rule
