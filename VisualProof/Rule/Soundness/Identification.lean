import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Rule.Identification
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Identification

namespace PortExpansion

theorem exists_retained
    (expansion : PortExpansion count retained exposed)
    (position : Fin retained) :
    ∃ exposedPosition : Fin exposed,
      expansion.select exposedPosition = Sum.inl position := by
  induction expansion with
  | nil => exact Fin.elim0 position
  | @retain retained exposed tail induction =>
      refine Fin.cases ?_ (fun retainedPosition => ?_) position
      · exact ⟨0, rfl⟩
      · obtain ⟨exposedPosition, selected⟩ := induction retainedPosition
        refine ⟨exposedPosition.succ, ?_⟩
        simp only [select, Fin.cases_succ]
        rw [selected]
  | @absorb retained exposed wire tail induction =>
      obtain ⟨exposedPosition, selected⟩ := induction position
      exact ⟨exposedPosition.succ, by
        simpa only [select, Fin.cases_succ] using selected⟩

end PortExpansion

namespace NodeData

/-- The one shared one-point lemma.  It serves local and root exposure: the
away syntax is related by the active typed port partition, while the selected
node is handled by its exact structural port expansion. -/
theorem denote_items_iff_of_rename
    (data : NodeData base signature count)
    (collapse : WireRenaming expanded base)
    (retain : WireRenaming base expanded)
    (fresh : Fin count → Var expanded signature)
    (collapseRetain : ∀ {wireSignature} (wire : Var base wireSignature),
      collapse (retain wire) = wire)
    (collapseFresh : ∀ wire : Fin count,
      collapse (fresh wire) = data.survivor)
    (away : ItemSeq base)
    (partition : ItemSeq.PortPartition collapse away)
    (baseEnv : Values model base)
    (expandedEnv : Values model expanded)
    (environment : Values.rename collapse baseEnv = expandedEnv) :
    denoteItemSeq model baseEnv
        (.cons data.collapsedNode away) ↔
      denoteItemSeq model expandedEnv
        (.cons (data.exposedNode retain fresh)
          (away.partitionOutput collapse partition)) := by
  have awayIff : denoteItemSeq model baseEnv away ↔
      denoteItemSeq model expandedEnv
        (away.partitionOutput collapse partition) := by
    have renamed := denoteItemSeq_renameWires model collapse baseEnv
      (away.partitionOutput collapse partition)
    rw [ItemSeq.partitionOutput_renameWires] at renamed
    rwa [environment] at renamed
  have lookupRetain : ∀ {wireSignature}
      (wire : Var base wireSignature),
      expandedEnv.lookup (retain wire) = baseEnv.lookup wire := by
    intro wireSignature wire
    rw [← environment, Values.lookup_rename, collapseRetain]
  have lookupFresh : ∀ wire : Fin count,
      expandedEnv.lookup (fresh wire) =
        baseEnv.lookup data.survivor := by
    intro wire
    rw [← environment, Values.lookup_rename, collapseFresh]
  have nodeIff : denoteItem model baseEnv data.collapsedNode ↔
      denoteItem model expandedEnv (data.exposedNode retain fresh) := by
    constructor
    · intro collapsedDenotes left right
      obtain ⟨survivorPosition, survivorEq⟩ := data.survivorPort
      cases leftSelected : data.expansion.select left with
      | inl leftRetained =>
          cases rightSelected : data.expansion.select right with
          | inl rightRetained =>
              simpa only [NodeData.exposedNode, denoteItem_identity,
                NodeData.exposedPorts, leftSelected, rightSelected,
                lookupRetain] using
                collapsedDenotes leftRetained rightRetained
          | inr rightAbsorbed =>
              have equality := collapsedDenotes leftRetained survivorPosition
              rw [survivorEq] at equality
              simpa only [NodeData.exposedNode, denoteItem_identity,
                NodeData.exposedPorts, leftSelected, rightSelected,
                lookupRetain, lookupFresh] using equality
      | inr leftAbsorbed =>
          cases rightSelected : data.expansion.select right with
          | inl rightRetained =>
              have equality := collapsedDenotes survivorPosition rightRetained
              rw [survivorEq] at equality
              simpa only [NodeData.exposedNode, denoteItem_identity,
                NodeData.exposedPorts, leftSelected, rightSelected,
                lookupRetain, lookupFresh] using equality
          | inr rightAbsorbed =>
              simp only [NodeData.exposedPorts, leftSelected,
                rightSelected, lookupFresh]
    · intro exposedDenotes left right
      obtain ⟨exposedLeft, leftSelected⟩ :=
        data.expansion.exists_retained left
      obtain ⟨exposedRight, rightSelected⟩ :=
        data.expansion.exists_retained right
      have equality := exposedDenotes exposedLeft exposedRight
      simpa only [NodeData.exposedNode, denoteItem_identity,
        NodeData.exposedPorts, leftSelected, rightSelected,
        lookupRetain] using equality
  simp only [denoteItemSeq_cons]
  exact and_congr nodeIff awayIff

end NodeData

namespace Local

theorem sound_iff
    (data : Data outer)
    (_applicability : Applicability data)
    (model : Model) (outerEnv : Values model outer) :
    denoteRegion model outerEnv data.collapsedRegion ↔
      denoteRegion model outerEnv data.exposedRegion := by
  let collapse := collapseLocal outer data.locals data.node.survivor data.count
  let retain := retainWire outer data.locals data.signature data.count
  let fresh : Fin data.count →
      Var (outer ++ (data.locals ++
        List.replicate data.count data.signature)) data.signature :=
    fun position =>
      freshLocalWire outer data.locals data.signature position
  constructor
  · rintro ⟨localEnv, collapsedDenotes⟩
    let baseEnv := outerEnv.append localEnv
    let expandedLocalEnv : Values model
        (data.locals ++ List.replicate data.count data.signature) :=
      Values.ofLookup fun wire =>
        baseEnv.lookup (collapse (Var.appendRight outer wire))
    let expandedEnv := outerEnv.append expandedLocalEnv
    have environment : Values.rename collapse baseEnv = expandedEnv := by
      apply Values.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer)
        (right := data.locals ++ List.replicate data.count data.signature)
        (motive := fun wire =>
          (Values.rename collapse baseEnv).lookup wire =
            expandedEnv.lookup wire)
      · intro inheritedSignature inherited
        simp [collapse, collapseLocal, baseEnv, expandedEnv]
      · intro localSignature localWire
        simp [expandedEnv, expandedLocalEnv]
    refine ⟨expandedLocalEnv, ?_⟩
    change denoteItemSeq model expandedEnv
      (.cons (data.node.exposedNode retain fresh) data.exposedAway)
    exact (data.node.denote_items_iff_of_rename collapse retain fresh
      (collapseLocal_retained data.node.survivor data.count)
      (collapseLocal_fresh data.node.survivor)
      data.away data.awayPartition baseEnv expandedEnv environment).mp
        collapsedDenotes
  · rintro ⟨expandedLocalEnv, exposedDenotes⟩
    let expandedEnv := outerEnv.append expandedLocalEnv
    let baseLocalEnv : Values model data.locals :=
      Values.ofLookup fun wire =>
        expandedEnv.lookup
          (retain (Var.appendRight outer wire))
    let baseEnv := outerEnv.append baseLocalEnv
    have exposedNodeDenotes : denoteItem model expandedEnv
        (data.node.exposedNode retain fresh) := by
      change denoteItemSeq model expandedEnv
          (.cons (data.node.exposedNode retain fresh)
            data.exposedAway) at exposedDenotes
      exact exposedDenotes.1
    have freshEq : ∀ wire : Fin data.count,
        expandedEnv.lookup (fresh wire) =
          expandedEnv.lookup (retain data.node.survivor) := by
      intro wire
      obtain ⟨absorbedPosition, absorbedSelected⟩ :=
        data.node.absorbedPort wire
      obtain ⟨survivorRetained, survivorEq⟩ := data.node.survivorPort
      obtain ⟨survivorPosition, survivorSelected⟩ :=
        data.node.expansion.exists_retained survivorRetained
      have equality := exposedNodeDenotes absorbedPosition survivorPosition
      simpa only [NodeData.exposedNode, denoteItem_identity,
        NodeData.exposedPorts, absorbedSelected, survivorSelected,
        survivorEq] using equality
    have environment : Values.rename collapse baseEnv = expandedEnv := by
      apply Values.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer)
        (right := data.locals ++ List.replicate data.count data.signature)
        (motive := fun wire =>
          (Values.rename collapse baseEnv).lookup wire =
            expandedEnv.lookup wire)
      · intro inheritedSignature inherited
        simp [collapse, collapseLocal, baseEnv, expandedEnv]
      · intro localSignature localWire
        apply Var.appendCases (left := data.locals)
          (right := List.replicate data.count data.signature)
          (motive := fun localWire =>
            (Values.rename collapse baseEnv).lookup
                (Var.appendRight outer localWire) =
              expandedEnv.lookup (Var.appendRight outer localWire))
        · intro retainedSignature retainedLocal
          simp only [Values.lookup_rename]
          rw [show collapse
              (Var.appendRight outer
                (retainedLocal.appendLeft
                  (List.replicate data.count data.signature))) =
                Var.appendRight outer retainedLocal by
            simpa only [collapse, retain, retainWire,
              Region.adjoinHostWire, Region.conjoinLeftWire,
              Var.appendMap_right] using
              collapseLocal_retained data.node.survivor data.count
                (Var.appendRight outer retainedLocal)]
          simp only [baseEnv, Values.lookup_append_right, baseLocalEnv,
            Values.lookup_ofLookup]
          simp [retain, retainWire, Region.adjoinHostWire,
            Region.conjoinLeftWire]
        · intro repeatedSignature repeated
          apply Repeated.elim data.signature
            (motive := fun repeated =>
              (Values.rename collapse baseEnv).lookup
                  (Var.appendRight outer
                    (Var.appendRight data.locals repeated)) =
                expandedEnv.lookup
                  (Var.appendRight outer
                    (Var.appendRight data.locals repeated)))
            (wireCase := fun position => ?_) repeated
          simp only [Values.lookup_rename]
          rw [show collapse
              (Var.appendRight outer
                (Var.appendRight data.locals
                  (Repeated.wire data.signature position))) =
                data.node.survivor by
            exact collapseLocal_fresh data.node.survivor position]
          change baseEnv.lookup data.node.survivor =
            expandedEnv.lookup (fresh position)
          have retainedEq : baseEnv.lookup data.node.survivor =
              expandedEnv.lookup (retain data.node.survivor) := by
            apply Var.appendCases (left := outer) (right := data.locals)
              (motive := fun survivor => baseEnv.lookup survivor =
                expandedEnv.lookup (retain survivor))
            · intro inheritedSignature inherited
              simp [baseEnv, expandedEnv, retain, retainWire,
                Region.adjoinHostWire, Region.conjoinLeftWire]
            · intro localSignature retainedLocal
              simp [baseEnv, baseLocalEnv, expandedEnv, retain, retainWire,
                Region.adjoinHostWire, Region.conjoinLeftWire]
          exact retainedEq.trans (freshEq position).symm
    refine ⟨baseLocalEnv, ?_⟩
    change denoteItemSeq model baseEnv
      (.cons data.node.collapsedNode data.away)
    exact (data.node.denote_items_iff_of_rename collapse retain fresh
      (collapseLocal_retained data.node.survivor data.count)
      (collapseLocal_fresh data.node.survivor)
      data.away data.awayPartition baseEnv expandedEnv environment).mpr
        exposedDenotes

end Local

namespace Open

theorem Data.denote_region_iff_of_rename
    {external : List Sig} (data : Data boundary external)
    (baseExternalEnv : Values model external)
    (expandedExternalEnv : Values model
      (external ++ List.replicate data.count data.signature))
    (environment : Values.rename
      (collapseOpen external data.survivor data.count)
        baseExternalEnv = expandedExternalEnv) :
    denoteRegion model baseExternalEnv data.collapsedRegion ↔
      denoteRegion model expandedExternalEnv data.exposedRegion := by
  let collapse :=
    (collapseOpen external data.survivor data.count).appendRight
      data.locals
  let retain : WireRenaming (external ++ data.locals)
      ((external ++ List.replicate data.count data.signature) ++
        data.locals) :=
    (retainOpenWire (external := external) data.signature
      data.count).appendRight data.locals
  let fresh : Fin data.count →
      Var ((external ++ List.replicate data.count data.signature) ++
        data.locals) data.signature := fun wire =>
    (freshOpenWire external data.signature wire).appendLeft data.locals
  have collapseRetain : ∀ {wireSignature}
      (wire : Var (external ++ data.locals) wireSignature),
      collapse (retain wire) = wire := by
    intro wireSignature wire
    apply Var.appendCases (left := external) (right := data.locals)
      (motive := fun wire => collapse (retain wire) = wire)
    · intro inheritedSignature inherited
      simp [collapse, retain, WireRenaming.appendRight,
        collapseOpen_retained]
    · intro localSignature localWire
      simp [collapse, retain, WireRenaming.appendRight]
  have collapseFresh : ∀ wire : Fin data.count,
      collapse (fresh wire) = data.node.survivor := by
    intro wire
    rw [data.nodeSurvivor]
    simp [collapse, fresh, WireRenaming.appendRight,
      collapseOpen_fresh]
  constructor
  · rintro ⟨localEnv, collapsedDenotes⟩
    refine ⟨localEnv, ?_⟩
    have combinedEnvironment : Values.rename collapse
        (baseExternalEnv.append localEnv) =
          expandedExternalEnv.append localEnv := by
      apply Values.ext
      intro wireSignature wire
      apply Var.appendCases
        (left := external ++ List.replicate data.count data.signature)
        (right := data.locals)
        (motive := fun wire =>
          (Values.rename collapse
            (baseExternalEnv.append localEnv)).lookup wire =
              (expandedExternalEnv.append localEnv).lookup wire)
      · intro inheritedSignature inherited
        have lookupEq := congrArg
          (fun values => values.lookup inherited) environment
        simpa [collapse, WireRenaming.appendRight] using lookupEq
      · intro localSignature localWire
        simp [collapse, WireRenaming.appendRight]
    change denoteItemSeq model (expandedExternalEnv.append localEnv)
      (.cons data.exposedNode data.exposedAway)
    simpa [Data.exposedAway, Data.exposedNode, collapse, retain, fresh]
      using (data.node.denote_items_iff_of_rename collapse retain fresh
      collapseRetain collapseFresh data.away data.awayPartition
      (baseExternalEnv.append localEnv)
      (expandedExternalEnv.append localEnv) combinedEnvironment).mp
        collapsedDenotes
  · rintro ⟨localEnv, exposedDenotes⟩
    refine ⟨localEnv, ?_⟩
    have combinedEnvironment : Values.rename collapse
        (baseExternalEnv.append localEnv) =
          expandedExternalEnv.append localEnv := by
      apply Values.ext
      intro wireSignature wire
      apply Var.appendCases
        (left := external ++ List.replicate data.count data.signature)
        (right := data.locals)
        (motive := fun wire =>
          (Values.rename collapse
            (baseExternalEnv.append localEnv)).lookup wire =
              (expandedExternalEnv.append localEnv).lookup wire)
      · intro inheritedSignature inherited
        have lookupEq := congrArg
          (fun values => values.lookup inherited) environment
        simpa [collapse, WireRenaming.appendRight] using lookupEq
      · intro localSignature localWire
        simp [collapse, WireRenaming.appendRight]
    change denoteItemSeq model (expandedExternalEnv.append localEnv)
      (.cons data.exposedNode data.exposedAway) at exposedDenotes
    simpa [Data.exposedAway, Data.exposedNode, collapse, retain, fresh]
      using (data.node.denote_items_iff_of_rename collapse retain fresh
      collapseRetain collapseFresh data.away data.awayPartition
      (baseExternalEnv.append localEnv)
      (expandedExternalEnv.append localEnv) combinedEnvironment).mpr
        exposedDenotes

theorem sound_iff
    {source target : OpenDiagram boundary}
    (step : Identification.Open source target)
    (model : Model) (args : Values model boundary) :
    denoteOpen model source args ↔ denoteOpen model target args := by
  let sourcePresentation : OpenDiagram boundary := {
    external := step.external
    boundaryWire := step.data.collapsedBoundary
    boundarySurjective := step.data.collapsedBoundarySurjective
    body := step.data.collapsedRegion
    canonical := step.sourceCanonical
    externalTwoEnded := step.sourceExternalTwoEnded
  }
  let targetPresentation : OpenDiagram boundary := {
    external := step.external ++
      List.replicate step.data.count step.data.signature
    boundaryWire := step.data.exposedBoundary
    boundarySurjective := step.applicability.boundarySurjective
    body := step.data.exposedRegion
    canonical := step.targetCanonical
    externalTwoEnded := step.targetExternalTwoEnded
  }
  let sourceIso : OpenDiagramIso source sourcePresentation := {
    external := step.sourceExternal
    boundary_eq := step.sourceBoundary
    body := step.sourceBody
  }
  let targetIso : OpenDiagramIso target targetPresentation := {
    external := step.targetExternal
    boundary_eq := step.targetBoundary
    body := step.targetBody
  }
  rw [sourceIso.denoteOpen_iff model args,
    targetIso.denoteOpen_iff model args]
  let collapse := collapseOpen step.external step.data.survivor step.data.count
  let retain : WireRenaming step.external
      (step.external ++
        List.replicate step.data.count step.data.signature) :=
    retainOpenWire step.data.signature step.data.count
  constructor
  · rintro ⟨baseEnv, boundaryEq, bodyDenotes⟩
    let expandedEnv := Values.rename collapse baseEnv
    refine ⟨expandedEnv, ?_, ?_⟩
    · have evaluation := evaluateVars_map_eq step.data.exposedBoundary
        collapse expandedEnv baseEnv (by
          intro wireSignature wire
          simp [expandedEnv])
      rw [exposedBoundary_collapse step.data] at evaluation
      exact evaluation.symm.trans boundaryEq
    · exact (step.data.denote_region_iff_of_rename baseEnv expandedEnv rfl).mp
        bodyDenotes
  · rintro ⟨expandedEnv, boundaryEq, bodyDenotes⟩
    let baseEnv := Values.rename retain expandedEnv
    obtain ⟨localEnv, exposedItemsDenote⟩ := bodyDenotes
    have exposedNodeDenotes : denoteItem model
        (expandedEnv.append localEnv) step.data.exposedNode := by
      exact exposedItemsDenote.1
    have freshEq : ∀ wire : Fin step.data.count,
        expandedEnv.lookup
            (freshOpenWire step.external step.data.signature wire) =
          expandedEnv.lookup (retain step.data.survivor) := by
      intro wire
      obtain ⟨absorbedPosition, absorbedSelected⟩ :=
        step.data.node.absorbedPort wire
      obtain ⟨survivorRetained, survivorEq⟩ :=
        step.data.node.survivorPort
      obtain ⟨survivorPosition, survivorSelected⟩ :=
        step.data.node.expansion.exists_retained survivorRetained
      have equality := exposedNodeDenotes absorbedPosition survivorPosition
      rw [step.data.nodeSurvivor] at survivorEq
      simpa [Data.exposedNode, NodeData.exposedNode,
        NodeData.exposedPorts, absorbedSelected, survivorSelected,
        survivorEq, retain, WireRenaming.appendRight] using equality
    have environment : Values.rename collapse baseEnv = expandedEnv := by
      apply Values.ext
      intro wireSignature wire
      apply Var.appendCases (left := step.external)
        (right := List.replicate step.data.count step.data.signature)
        (motive := fun wire =>
          (Values.rename collapse baseEnv).lookup wire =
            expandedEnv.lookup wire)
      · intro inheritedSignature inherited
        simp [collapse, baseEnv, retain, collapseOpen, retainOpenWire]
      · intro repeatedSignature repeated
        apply Repeated.elim step.data.signature
          (motive := fun repeated =>
            (Values.rename collapse baseEnv).lookup
                (Var.appendRight step.external repeated) =
              expandedEnv.lookup (Var.appendRight step.external repeated))
          (wireCase := fun position => ?_) repeated
        simp only [Values.lookup_rename]
        rw [show collapse
            (Var.appendRight step.external
              (Repeated.wire step.data.signature position)) =
              step.data.survivor by
          exact collapseOpen_fresh step.data.survivor position]
        simp only [baseEnv, Values.lookup_rename]
        change expandedEnv.lookup (retain step.data.survivor) =
          expandedEnv.lookup
            (freshOpenWire step.external step.data.signature position)
        exact (freshEq position).symm
    refine ⟨baseEnv, ?_, ?_⟩
    · have evaluation := evaluateVars_map_eq step.data.exposedBoundary
        collapse expandedEnv baseEnv (by
          intro wireSignature wire
          simpa only [Values.lookup_rename] using
            (congrArg (fun values => values.lookup wire) environment).symm)
      rw [exposedBoundary_collapse step.data] at evaluation
      exact evaluation.trans boundaryEq
    · exact (step.data.denote_region_iff_of_rename
        baseEnv expandedEnv environment).mpr ⟨localEnv, exposedItemsDenote⟩

end Open

end Identification

theorem Identification.sound
    {source target : OpenDiagram boundary}
    (step : Identification source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  rcases step with localStep | openForward | openBackward
  · apply Contextual.sound (step := localStep)
    intro wires before after evidence model env
    rcases evidence with forward | backward
    · cases forward with
      | expose data applicability =>
          exact (Identification.Local.sound_iff
            data applicability model env).mp
    · cases backward with
      | expose data applicability =>
          exact (Identification.Local.sound_iff
            data applicability model env).mpr
  · rcases openForward with ⟨openStep⟩
    intro model args
    exact (Identification.Open.sound_iff openStep model args).mp
  · rcases openBackward with ⟨openStep⟩
    intro model args
    exact (Identification.Open.sound_iff openStep model args).mpr

theorem Identification.sound_iff
    {source target : OpenDiagram boundary}
    (step : Identification source target)
    (model : Model) (args : Values model boundary) :
    denoteOpen model source args ↔ denoteOpen model target args := by
  constructor
  · exact Identification.sound step model args
  · exact Identification.sound (Identification.symm step) model args

end VisualProof.Rule
