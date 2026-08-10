import VisualProof.Refinement.Implementation.IterationQuotient
import VisualProof.Refinement.Implementation.IterationRootSourceFactor
import VisualProof.Refinement.Implementation.IterationTransport
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.RootFactor
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.IterationRootTarget

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationFragment
open VisualProof.Refinement.Implementation.IterationQuotient
open VisualProof.Refinement.Implementation.IterationRootSourceFactor
open VisualProof.Refinement.Implementation.IterationSourceFactor

/-- The compiler locals at the extracted body are exactly the selected
explicit wires, through extraction's actual origin map.  This description is
independent of the binder-spine presentation used to compile the fragment. -/
private theorem bodyInternalOrigins_perm_explicit
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val) :
    let fragmentLayout : FragmentLayout input.val selection := {}
    let spliceInput := iterationInput input selection selection.val.anchor
    let plugLayout := spliceInput.plugLayout
    (plugLayout.bodyInternalOriginalWires.map
      (input.val.fragmentWireOrigin selection fragmentLayout)).Perm
        selection.val.explicitWires := by
  dsimp only
  let fragmentLayout : FragmentLayout input.val selection := {}
  let spliceInput := iterationInput input selection selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let origins := plugLayout.bodyInternalOriginalWires.map
    (input.val.fragmentWireOrigin selection fragmentLayout)
  have originsNodup : origins.Nodup := by
    exact plugLayout.bodyInternalOriginalWires_nodup.map _
      (fun first second distinct equality =>
        distinct (input.val.fragmentWireOrigin_injective selection
          fragmentLayout equality))
  have members (wire : Fin input.val.wireCount) :
      wire ∈ origins ↔ wire ∈ selection.val.explicitWires := by
    constructor
    · intro member
      obtain ⟨fragmentWire, localMember, originEq⟩ := List.mem_map.mp member
      have localFacts :=
        (plugLayout.mem_bodyInternalOriginalWires fragmentWire).1 localMember
      have visible : spliceInput.pattern.val.diagram.Encloses
          (spliceInput.pattern.val.diagram.wires fragmentWire).scope
          spliceInput.binderSpine.bodyContainer := by
        rw [localFacts.2]
        exact Concrete.Diagram.Encloses.refl _ _
      have originVisible :=
        IterationExtraction.fragmentWireOrigin_scope_encloses_anchor input
          selection fragmentLayout fragmentWire visible
      revert localMember originEq localFacts originVisible
      refine Fin.addCases
        (fun internal _ originEq _ originVisible => ?_)
        (fun boundary _ _ localFacts _ => ?_) fragmentWire
      · have internalMember :
            selection.internalWires.get internal ∈ selection.internalWires :=
          List.get_mem _ _
        have originInternal : wire = selection.internalWires.get internal := by
          simpa [Concrete.Diagram.fragmentWireOrigin,
            FragmentLayout.internalWire] using originEq.symm
        rw [originInternal]
        rcases (selection.mem_internalWires_expanded
            (selection.internalWires.get internal)).1 internalMember with
          selectedScope | explicit
        · obtain ⟨child, childDirect, childEncloses⟩ := selectedScope
          have anchorEnclosesChild :
              input.val.Encloses selection.val.anchor child :=
            ⟨⟨1, by have := child.isLt; omega⟩, by
              simp [Concrete.Diagram.climb,
                selection.property.childRoots_direct child childDirect]⟩
          have anchorEnclosesScope :=
            Concrete.Elaboration.checked_encloses_trans input.property
              anchorEnclosesChild childEncloses
          have equal := Concrete.Elaboration.checked_encloses_antisymm
            input.property anchorEnclosesScope (by
              simpa [Concrete.Diagram.fragmentWireOrigin,
                FragmentLayout.internalWire] using originVisible)
          rw [← equal] at childEncloses
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              input.property
              (selection.property.childRoots_direct child childDirect)
              childEncloses)
        · exact explicit
      · exact False.elim (localFacts.1 (by
          change fragmentLayout.boundaryWire boundary ∈
            spliceInput.pattern.val.exposedWires
          exact (Concrete.OpenDiagram.mem_exposedWires _ _).2 (by
            change fragmentLayout.boundaryWire boundary ∈
              input.val.extractBoundaryRaw selection fragmentLayout
            exact List.mem_ofFn.mpr ⟨boundary, rfl⟩)))
    · intro explicit
      have internalMember := selection.explicitWire_mem_internalWires explicit
      obtain ⟨internal, internalGet⟩ := List.mem_iff_get.mp internalMember
      let fragmentWire := fragmentLayout.internalWire internal
      have notExposed : fragmentWire ∉ spliceInput.pattern.val.exposedWires := by
        intro exposed
        have boundaryMember :=
          (Concrete.OpenDiagram.mem_exposedWires spliceInput.pattern.val
            fragmentWire).1 exposed
        obtain ⟨position, positionGet⟩ := List.mem_iff_get.mp boundaryMember
        let boundaryIndex := Fin.cast
          (input.val.extractBoundaryRaw_length selection fragmentLayout)
          position
        have boundaryGet : spliceInput.pattern.val.boundary.get position =
            fragmentLayout.boundaryWire boundaryIndex := by
          simp [spliceInput, iterationInput, Concrete.Diagram.extractOpenRaw,
            Concrete.Diagram.extractBoundaryRaw, boundaryIndex,
            FragmentLayout.boundaryWire]
          apply Fin.ext
          rfl
        have equality : fragmentLayout.boundaryWire boundaryIndex =
            fragmentLayout.internalWire internal :=
          boundaryGet.symm.trans positionGet
        have values := congrArg Fin.val equality
        simp [FragmentLayout.internalWire, FragmentLayout.boundaryWire]
          at values
        omega
      have bodyScope :
          (spliceInput.pattern.val.diagram.wires fragmentWire).scope =
            spliceInput.binderSpine.bodyContainer := by
        change ((input.val.extractDiagramRaw selection fragmentLayout).wires
          (fragmentLayout.internalWire internal)).scope = _
        rw [input.val.extractDiagramRaw_internalWire_scope_exact,
          internalGet, selection.property.explicitWires_at_anchor wire explicit,
          input.val.fragmentParent_anchor selection fragmentLayout]
        rfl
      apply List.mem_map.mpr
      refine ⟨fragmentWire,
        (plugLayout.mem_bodyInternalOriginalWires fragmentWire).2
          ⟨notExposed, bodyScope⟩, ?_⟩
      simpa [fragmentWire, Concrete.Diagram.fragmentWireOrigin,
        FragmentLayout.internalWire] using internalGet
  rw [List.perm_iff_count]
  intro wire
  rw [originsNodup.count, selection.property.explicitWires_nodup.count]
  by_cases member : wire ∈ origins
  · have targetMember := (members wire).1 member
    simp [member, targetMember]
  · have targetNotMember : wire ∉ selection.val.explicitWires :=
      fun present => member ((members wire).2 present)
    simp [member, targetNotMember]

private noncomputable def bodyInternalExplicitEquiv
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val) :
    let spliceInput := iterationInput input selection selection.val.anchor
    FiniteEquiv (Fin spliceInput.plugLayout.bodyInternalCarriers.length)
      (Fin selection.val.explicitWires.length) := by
  dsimp only
  let fragmentLayout : FragmentLayout input.val selection := {}
  let spliceInput := iterationInput input selection selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let origins := plugLayout.bodyInternalOriginalWires.map
    (input.val.fragmentWireOrigin selection fragmentLayout)
  let permutation := bodyInternalOrigins_perm_explicit input selection
  let originsNodup : origins.Nodup :=
    permutation.nodup_iff.mpr selection.property.explicitWires_nodup
  have carrierLength : plugLayout.bodyInternalCarriers.length =
      origins.length := by
    simp only [origins, List.length_map]
    exact plugLayout.bodyInternalOriginalWires_length.symm
  exact (FiniteEquiv.finCast carrierLength).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin input.val.wireCount)) origins
      selection.val.explicitWires originsNodup
      selection.property.explicitWires_nodup
      (fun wire => by
        simpa only [FiniteEquiv.refl_apply] using permutation.mem_iff.symm))

private theorem bodyInternalExplicitEquiv_spec
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (index : Fin (iterationInput input selection
      selection.val.anchor).plugLayout.bodyInternalCarriers.length) :
    selection.val.explicitWires.get
        (bodyInternalExplicitEquiv input selection index) =
      input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((iterationInput input selection selection.val.anchor).plugLayout
          |>.internalWires.origin
            ((iterationInput input selection selection.val.anchor).plugLayout
              |>.bodyInternalCarriers.get index)) := by
  let fragmentLayout : FragmentLayout input.val selection := {}
  let spliceInput := iterationInput input selection selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let origins := plugLayout.bodyInternalOriginalWires.map
    (input.val.fragmentWireOrigin selection fragmentLayout)
  let permutation := bodyInternalOrigins_perm_explicit input selection
  let originsNodup : origins.Nodup :=
    permutation.nodup_iff.mpr selection.property.explicitWires_nodup
  let carrierLength : plugLayout.bodyInternalCarriers.length =
      origins.length := by
    simp only [origins, List.length_map]
    exact plugLayout.bodyInternalOriginalWires_length.symm
  have restricted := FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.val.wireCount)) origins
    selection.val.explicitWires originsNodup
    selection.property.explicitWires_nodup
    (fun wire => by
      simpa only [FiniteEquiv.refl_apply] using permutation.mem_iff.symm)
    (Fin.cast carrierLength index)
  have originGet : origins.get (Fin.cast carrierLength index) =
      input.val.fragmentWireOrigin selection fragmentLayout
        (plugLayout.internalWires.origin
          (plugLayout.bodyInternalCarriers.get index)) := by
    let originalLength : plugLayout.bodyInternalCarriers.length =
        plugLayout.bodyInternalOriginalWires.length :=
      plugLayout.bodyInternalOriginalWires_length.symm
    calc
      origins.get (Fin.cast carrierLength index) =
          input.val.fragmentWireOrigin selection fragmentLayout
            (plugLayout.bodyInternalOriginalWires.get
              (Fin.cast originalLength index)) := by
        simp only [origins, List.get_eq_getElem, List.getElem_map]
        rfl
      _ = input.val.fragmentWireOrigin selection fragmentLayout
          (plugLayout.internalWires.origin
            (plugLayout.bodyInternalCarriers.get index)) := by
        apply congrArg (input.val.fragmentWireOrigin selection fragmentLayout)
        unfold Concrete.Splice.Input.PlugLayout.bodyInternalOriginalWires
        rw [List.get_eq_getElem, List.getElem_map]
        apply congrArg plugLayout.internalWires.origin
        apply congrArg (List.get plugLayout.bodyInternalCarriers)
        apply Fin.ext
        rfl
  have result := restricted.trans originGet
  simpa [bodyInternalExplicitEquiv, spliceInput, plugLayout, origins,
    fragmentLayout, carrierLength, FiniteEquiv.finCast] using result

private theorem ItemSeq.append_congr
    {firstLeft firstRight secondLeft secondRight : ItemSeq wires rels}
    (firstEq : firstLeft = firstRight)
    (secondEq : secondLeft = secondRight) :
    firstLeft.append secondLeft = firstRight.append secondRight := by
  subst firstRight
  subst secondRight
  rfl

private noncomputable def RegionIso.conjoin_left
    (fixed : Region wires rels)
    {source target : Region wires rels}
    (iso : RegionIso (FiniteEquiv.refl (Fin wires)) rels source target) :
    RegionIso (FiniteEquiv.refl (Fin wires)) rels
      (fixed.conjoin source) (fixed.conjoin target) := by
  cases fixed with
  | mk prefixLocal prefixItems =>
    cases source with
    | mk sourceLocal sourceItems =>
      cases target with
      | mk targetLocal targetItems =>
        cases iso with
        | mk localEquiv itemsIso =>
          let combinedLocal := extendWireEquiv
            (FiniteEquiv.refl (Fin prefixLocal)) localEquiv
          let combinedWire := extendWireEquiv
            (FiniteEquiv.refl (Fin wires)) combinedLocal
          let prefixSource := Region.conjoinLeftWire wires prefixLocal
            sourceLocal
          let prefixTarget := Region.conjoinLeftWire wires prefixLocal
            targetLocal
          let suffixSource := Region.conjoinRightWire wires prefixLocal
            sourceLocal
          let suffixTarget := Region.conjoinRightWire wires prefixLocal
            targetLocal
          have prefixCommutes : combinedWire.toFun ∘ prefixSource =
              prefixTarget := by
            funext index
            refine Fin.addCases (fun inherited => ?_)
              (fun localIndex => ?_) index
            · simp [combinedWire, combinedLocal, prefixSource, prefixTarget,
                Region.conjoinLeftWire]
            · simp [combinedWire, combinedLocal, prefixSource, prefixTarget,
                Region.conjoinLeftWire]
          have suffixCommutes : combinedWire.toFun ∘ suffixSource =
              suffixTarget ∘
                (extendWireEquiv (FiniteEquiv.refl (Fin wires))
                  localEquiv).toFun := by
            funext index
            refine Fin.addCases (fun inherited => ?_)
              (fun localIndex => ?_) index
            · simp [combinedWire, combinedLocal, suffixSource, suffixTarget,
                Region.conjoinRightWire]
            · simp [combinedWire, combinedLocal, suffixSource, suffixTarget,
                Region.conjoinRightWire]
          let prefixIso := (ItemSeqIso.refl prefixItems).renameWires_commuting
            prefixSource prefixTarget combinedWire prefixCommutes
          let suffixIso := itemsIso.renameWires_commuting suffixSource
            suffixTarget combinedWire suffixCommutes
          exact RegionIso.mk combinedLocal (prefixIso.append suffixIso)

private noncomputable def RegionIso.adjoinAt_nil
    (hostLocal : Nat)
    {source target : Region (outer + hostLocal) rels}
    (iso : RegionIso (FiniteEquiv.refl (Fin (outer + hostLocal))) rels
      source target) :
    RegionIso (FiniteEquiv.refl (Fin outer)) rels
      (Region.adjoinAt hostLocal .nil source)
      (Region.adjoinAt hostLocal .nil target) := by
  cases iso with
  | @mk _ _ sourceLocal targetLocal _ _ sourceItems targetItems localEquiv
      itemsIso =>
    let hostRefl := FiniteEquiv.refl (Fin hostLocal)
    let liftedLocal := extendWireEquiv hostRefl localEquiv
    let liftedWire := extendWireEquiv (FiniteEquiv.refl (Fin outer))
      liftedLocal
    let sourceMap := Region.adjoinMaterialWire outer hostLocal sourceLocal
    let targetMap := Region.adjoinMaterialWire outer hostLocal targetLocal
    have commutes : liftedWire.toFun ∘ sourceMap = targetMap ∘
        (extendWireEquiv (FiniteEquiv.refl (Fin (outer + hostLocal)))
          localEquiv).toFun := by
      funext index
      refine Fin.addCases (fun prior => ?_) (fun added => ?_) index
      · refine Fin.addCases (fun inherited => ?_)
          (fun hostIndex => ?_) prior
        · simp [liftedWire, liftedLocal, hostRefl, sourceMap, targetMap]
        · simp [liftedWire, liftedLocal, hostRefl, sourceMap, targetMap]
      · simp [liftedWire, liftedLocal, hostRefl, sourceMap, targetMap]
    let liftedItems := itemsIso.renameWires_commuting sourceMap targetMap
      liftedWire commutes
    refine RegionIso.mk liftedLocal ?_
    simpa [Region.adjoinAt, ItemSeq.nil_append] using liftedItems

private noncomputable def OpenDiagramIso.ofEq
    {arity : Nat} {left right : OpenDiagram arity}
    (equality : left = right) : OpenDiagramIso left right := by
  subst right
  exact OpenDiagramIso.refl left

private theorem OpenDiagram.castArity_body
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (externalEq : (diagram.castArity equality).externalClasses =
      diagram.externalClasses) :
    (diagram.castArity equality).body =
      diagram.body.renameWires (Fin.cast externalEq.symm) := by
  subst targetArity
  have proofEq : externalEq = rfl := Subsingleton.elim _ _
  rw [proofEq]
  simpa using (Region.renameWires_id diagram.body).symm

private theorem OpenDiagram.castArity_boundary_cast
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (position : Fin targetArity) :
    Fin.cast (OpenDiagram.castArity_externalClasses diagram equality)
        ((diagram.castArity equality).boundary position) =
      diagram.boundary (Fin.cast equality.symm position) := by
  subst targetArity
  apply Fin.ext
  rfl

private theorem Region.castWiresEq_renameWires_cancel
    (region : Region sourceWires rels)
    (equality : sourceWires = targetWires) :
    (region.castWiresEq equality).renameWires (Fin.cast equality.symm) =
      region := by
  subst targetWires
  simpa [Region.castWiresEq_eq_renameWires,
    Region.renameWires_comp] using Region.renameWires_id region

private theorem Region.castWiresEq_renameWires_cancel_two
    (region : Region sourceWires rels)
    (forward : sourceWires = targetWires)
    (backward : targetWires = sourceWires) :
    (region.castWiresEq forward).renameWires (Fin.cast backward) = region := by
  have backwardEq : backward = forward.symm := Subsingleton.elim _ _
  rw [backwardEq]
  exact Region.castWiresEq_renameWires_cancel region forward

private theorem RegionIso.localEquivCast_target
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso ambient rels source target)
    (targetLocalEq : target.localCount = targetLocal) :
    iso.localEquivCast rfl targetLocalEq =
      iso.localEquiv.trans (FiniteEquiv.finCast targetLocalEq) := by
  subst targetLocal
  rfl

private theorem Region.adjoinHostWire_extendWireEquiv
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (host : FiniteEquiv (Fin sourceHost) (Fin targetHost))
    (copy : FiniteEquiv (Fin sourceCopy) (Fin targetCopy)) :
    (extendWireEquiv outer (extendWireEquiv host copy)).toFun ∘
        Region.adjoinHostWire sourceOuter sourceHost sourceCopy =
      Region.adjoinHostWire targetOuter targetHost targetCopy ∘
        (extendWireEquiv outer host).toFun := by
  funext index
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
  · simp [Function.comp_apply]
  · simp [Function.comp_apply]

private noncomputable def OpenDiagramIso.castArity
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem OpenDiagram.castArity_trans
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private theorem checkedOpenElaborateCast_eq
    {arity : Nat} {left right : Concrete.CheckedOpen}
    (equality : left = right)
    (leftArity : left.val.boundary.length = arity)
    (rightArity : right.val.boundary.length = arity) :
    left.elaborate.castArity leftArity =
      right.elaborate.castArity rightArity := by
  subst right
  rfl

/-- The Base target at a root anchor.  The original selected material remains
in the routed source and one freshly wired copy is inserted at the retained
focus. -/
noncomputable def rootAtStartTargetBody
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    {layout : FragmentLayout source.diagram.val selection}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput source.diagram selection layout spliceInput}
    (assembly : @FactorAssembly source.diagram selection layout 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      spliceInput fragment selection.val.anchor []
      (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot)) :
    Region source.checked.elaborate.externalClasses [] :=
  Region.adjoinAt source.checked.val.hiddenWires.length .nil
    (assembly.selected.conjoin
      (assembly.descendant.fill
        ((Region.adjoinAt selection.val.explicitWires.length .nil
          ((assembly.selected.renameWires assembly.copyWires.wire)
            |>.renameRelations assembly.descendant.outerRelation)).conjoin
          assembly.remainder)))

private noncomputable def rootAtStart_sourceBodyFactor
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor))
    (assembly : @FactorAssembly source.diagram selection {} 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      (iterationInput source.diagram selection selection.val.anchor)
      fragment selection.val.anchor [] (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot))
    (admissible : (iterationInput source.diagram selection
      selection.val.anchor).Admissible) :
    let spliceInput := iterationInput source.diagram selection
      selection.val.anchor
    let coalesced :=
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
        admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped
    let quotient := coalescedOpenIso source.diagram selection
      selection.val.anchor source.checked.val.boundary
    let quotientSourceLocalEq :=
      coalesced.val.elaborate_body_localCount coalesced.property
    { iso : RegionIso quotient.exposedWiresEquiv []
        coalesced.elaborate.body assembly.sourceBody //
      iso.localEquivCast quotientSourceLocalEq rfl =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv } := by
  dsimp only
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let coalesced :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
      admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let quotient := coalescedOpenIso source.diagram selection
    selection.val.anchor source.checked.val.boundary
  let sourceOpen := Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
    spliceInput source.checked.val.boundary
  let targetOpen : Concrete.OpenDiagram := {
    diagram := source.diagram.val
    boundary := source.checked.val.boundary
  }
  let quotientIso := quotient.elaborate_isomorphic
    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot_wellFormed
      spliceInput admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped)
    source.checked.property
  let rawSource : Concrete.State coalesced.val.boundary.length := {
    checked := source.checked
    boundary_length := quotient.boundary_length_eq.symm
  }
  let sourceTargetIso := rootSourceIso rawSource selection anchorRoot assembly
  let composed := quotientIso.body.trans sourceTargetIso.body
  let sourceId : Fin coalesced.elaborate.externalClasses →
      Fin coalesced.elaborate.externalClasses := id
  let targetCast := Fin.cast
    (OpenDiagram.castArity_externalClasses source.checked.elaborate
      quotient.boundary_length_eq.symm)
  have commutes : quotient.exposedWiresEquiv.toFun ∘ sourceId =
      targetCast ∘
        (quotientIso.external.trans sourceTargetIso.external).toFun := by
    funext index
    change quotient.exposedWiresEquiv (sourceId index) =
      targetCast ((quotientIso.external.trans sourceTargetIso.external) index)
    obtain ⟨position, rfl⟩ := coalesced.elaborate.boundary_surjective index
    rw [show (quotientIso.external.trans sourceTargetIso.external)
          (coalesced.elaborate.boundary position) =
        ((source.checked.elaborate.castArity
          quotient.boundary_length_eq.symm).withBody
            (assembly.sourceBody.castWiresEq
              (OpenDiagram.castArity_externalClasses
                source.checked.elaborate
                quotient.boundary_length_eq.symm).symm)).boundary position by
      exact congrArg sourceTargetIso.external
        (quotientIso.boundary position) |>.trans
          (sourceTargetIso.boundary position)]
    have boundaryCommute := quotient.boundaryClass_commute position
    have sourceBoundaryEq : coalesced.elaborate.boundary position =
        sourceOpen.boundaryClass position := by
      rfl
    rw [sourceBoundaryEq]
    have targetBoundaryEq : targetCast
          (((source.checked.elaborate.castArity
            quotient.boundary_length_eq.symm).withBody
              (assembly.sourceBody.castWiresEq
                (OpenDiagram.castArity_externalClasses
                  source.checked.elaborate
                  quotient.boundary_length_eq.symm).symm)).boundary position) =
        targetOpen.boundaryClass
          (Fin.cast quotient.boundary_length_eq position) := by
      simpa [targetCast, targetOpen, OpenDiagram.withBody,
        OpenDiagram.elaborate_boundary] using
          OpenDiagram.castArity_boundary_cast source.checked.elaborate
            quotient.boundary_length_eq.symm position
    rw [targetBoundaryEq]
    exact boundaryCommute
  let uncast := composed.renameWires_commuting sourceId targetCast
    quotient.exposedWiresEquiv commutes
  let rawBody := sourceOpen.elaborate
    (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot_wellFormed
      spliceInput admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped) |>.body
  let rawTarget :=
    (rawSource.checked.elaborate.castArity rawSource.boundary_length
      ).withBody
        (assembly.sourceBody.castWiresEq
          (OpenDiagram.castArity_externalClasses rawSource.checked.elaborate
            rawSource.boundary_length).symm) |>.body
  change RegionIso quotient.exposedWiresEquiv []
    (rawBody.renameWires id) (rawTarget.renameWires targetCast) at uncast
  have sourceCancel : rawBody.renameWires id = rawBody :=
    Region.renameWires_id rawBody
  have targetCancel : rawTarget.renameWires targetCast =
      assembly.sourceBody := by
    dsimp only [rawTarget, OpenDiagram.withBody]
    apply Region.castWiresEq_renameWires_cancel_two
  let sourceTransportedFirst : RegionIso quotient.exposedWiresEquiv []
      rawBody (rawTarget.renameWires targetCast) :=
    Eq.mp (congrArg (fun sourceBody => RegionIso
      quotient.exposedWiresEquiv [] sourceBody
        (rawTarget.renameWires targetCast)) sourceCancel) uncast
  let sourceTransported : RegionIso quotient.exposedWiresEquiv []
      rawBody assembly.sourceBody :=
    Eq.mp (congrArg (fun target => RegionIso quotient.exposedWiresEquiv []
      rawBody target) targetCancel) sourceTransportedFirst
  let hostBodyIso : RegionIso quotient.exposedWiresEquiv []
      coalesced.elaborate.body assembly.sourceBody := by
    simpa [rawBody, sourceOpen, coalesced] using sourceTransported
  let quotientSourceLocalEq :=
    coalesced.val.elaborate_body_localCount coalesced.property
  let quotientTargetLocalEq :=
    source.checked.val.elaborate_castArity_body_localCount
      source.checked.property quotient.boundary_length_eq.symm
  let rootSourceLocalEq :
      (rawSource.checked.elaborate.castArity rawSource.boundary_length
        ).body.localCount =
          (rootSourcePartition source selection anchorRoot
            ).sourceRegion.localCount := by
    have sourceBodyLocalEq :=
      source.checked.val.elaborate_body_localCount source.checked.property
    have sourceRegionLocalEq := congrArg Region.localCount
      (rootSourceRegion_eq rawSource selection anchorRoot).symm
    exact quotientTargetLocalEq.trans
      (sourceBodyLocalEq.symm.trans (by
        simpa [rawSource] using sourceRegionLocalEq))
  let rootTargetLocalEq : rawTarget.localCount =
      assembly.sourceBody.localCount := by
    dsimp only [rawTarget, OpenDiagram.withBody]
    apply Region.castWiresEq_localCount
  let rawSourceLocalEq : rawBody.localCount =
      coalesced.val.hiddenWires.length := by
    simpa [rawBody, sourceOpen, coalesced] using quotientSourceLocalEq
  let renamedSourceLocalEq : (rawBody.renameWires id).localCount =
      coalesced.val.hiddenWires.length :=
    (Region.renameWires_localCount rawBody id).trans rawSourceLocalEq
  let renamedTargetLocalEq :
      (rawTarget.renameWires targetCast).localCount =
        assembly.sourceBody.localCount :=
    (Region.renameWires_localCount rawTarget targetCast).trans
      rootTargetLocalEq
  have quotientLocal : quotientIso.body.localEquivCast
      quotientSourceLocalEq quotientTargetLocalEq =
        quotient.hiddenWiresEquiv := by
    simpa only [quotientIso] using
      quotient.elaborate_isomorphic_localEquivCast
        coalesced.property source.checked.property
  have sourceLocal : sourceTargetIso.body.localEquivCast
      rootSourceLocalEq rootTargetLocalEq =
        assembly.source_iso.localEquiv := by
    simpa only [sourceTargetIso] using
      rootSourceIso_localEquivCast rawSource selection anchorRoot assembly
        rootSourceLocalEq rootTargetLocalEq
  have composedLocal : composed.localEquivCast quotientSourceLocalEq
      rootTargetLocalEq =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv := by
    calc
      composed.localEquivCast quotientSourceLocalEq rootTargetLocalEq =
          (quotientIso.body.localEquivCast quotientSourceLocalEq
            quotientTargetLocalEq).trans
            (sourceTargetIso.body.localEquivCast rootSourceLocalEq
              rootTargetLocalEq) := by
        simpa only [composed] using RegionIso.localEquivCast_trans
          quotientIso.body sourceTargetIso.body quotientSourceLocalEq
          quotientTargetLocalEq rootTargetLocalEq
      _ = quotient.hiddenWiresEquiv.trans
          (sourceTargetIso.body.localEquivCast rootSourceLocalEq
            rootTargetLocalEq) :=
        congrArg (fun left => left.trans
          (sourceTargetIso.body.localEquivCast rootSourceLocalEq
            rootTargetLocalEq)) quotientLocal
      _ = quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv :=
        congrArg (fun right => quotient.hiddenWiresEquiv.trans right)
          sourceLocal
  have renamedLocal : uncast.localEquivCast renamedSourceLocalEq
      renamedTargetLocalEq =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv := by
    have preserved := RegionIso.renameWires_commuting_localEquivCast
      composed sourceId targetCast quotient.exposedWiresEquiv commutes
        quotientSourceLocalEq rootTargetLocalEq
    have preserved' : uncast.localEquivCast renamedSourceLocalEq
        renamedTargetLocalEq = composed.localEquivCast
          quotientSourceLocalEq rootTargetLocalEq := by
      simpa only [uncast, renamedSourceLocalEq, renamedTargetLocalEq,
        rawBody, rawTarget, sourceId] using preserved
    exact preserved'.trans composedLocal
  have transportedLocal : sourceTransported.localEquivCast
      rawSourceLocalEq rfl =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv := by
    have preserved := RegionIso.localEquivCast_castEndpoints uncast
      sourceCancel targetCancel renamedSourceLocalEq renamedTargetLocalEq
        rawSourceLocalEq rfl
    have preserved' : sourceTransported.localEquivCast
        rawSourceLocalEq rfl = uncast.localEquivCast
          renamedSourceLocalEq renamedTargetLocalEq := by
      simpa only [sourceTransportedFirst, sourceTransported]
        using preserved
    exact preserved'.trans renamedLocal
  have hostBodyLocalEq : hostBodyIso.localEquivCast
      quotientSourceLocalEq rfl =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv := by
    simpa only [hostBodyIso, rawBody, sourceOpen, coalesced]
      using transportedLocal
  exact ⟨hostBodyIso, hostBodyLocalEq⟩

set_option maxHeartbeats 600000 in
private noncomputable opaque rootAtStart_bodyIso
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor))
    (assembly : @FactorAssembly source.diagram selection {} 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      (iterationInput source.diagram selection selection.val.anchor)
      fragment selection.val.anchor [] (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot))
    (admissible : (iterationInput source.diagram selection
      selection.val.anchor).Admissible)
    (siteRoot :
      (iterationInput source.diagram selection selection.val.anchor).site =
        (iterationInput source.diagram selection
          selection.val.anchor).frame.val.root)
    (coalescedArity :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput source.diagram selection selection.val.anchor)
        admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped).val.boundary.length =
          source.checked.val.boundary.length) :
    let spliceInput := iterationInput source.diagram selection
      selection.val.anchor
    let plugLayout := spliceInput.plugLayout
    let sourceCompiler :=
      Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern spliceInput
        plugLayout admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped siteRoot
        fragment.context fragment.contextExact fragment.binders
        fragment.enumeration fragment.items
    let quotient := coalescedOpenIso source.diagram selection
      selection.val.anchor source.checked.val.boundary
    let sourceOpen := Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
      spliceInput source.checked.val.boundary
    let targetOpen : Concrete.OpenDiagram := {
      diagram := source.diagram.val
      boundary := source.checked.val.boundary
    }
    let sourceExternalEq :
        (sourceCompiler.castArity coalescedArity).externalClasses =
          sourceOpen.exposedWires.length := by
      simp [sourceCompiler, sourceOpen,
        Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern,
        Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
        Concrete.Splice.replaceOpenBody,
        Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot]
    let targetExternalEq :
        (source.checked.elaborate.withBody
          (rootAtStartTargetBody source selection anchorRoot assembly)
        ).externalClasses = targetOpen.exposedWires.length := by
      rfl
    let external :=
      ((FiniteEquiv.finCast sourceExternalEq).trans
        quotient.exposedWiresEquiv).trans
          (FiniteEquiv.finCast targetExternalEq.symm)
    RegionIso external [] (sourceCompiler.castArity coalescedArity).body
      (rootAtStartTargetBody source selection anchorRoot assembly) := by
  dsimp only
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let coalesced :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
      admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let sourceCompiler :=
    Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern spliceInput
      plugLayout admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped siteRoot
      fragment.context fragment.contextExact fragment.binders
      fragment.enumeration fragment.items
  let quotient := coalescedOpenIso source.diagram selection
    selection.val.anchor source.checked.val.boundary
  let sourceOpen := Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
    spliceInput source.checked.val.boundary
  let targetOpen : Concrete.OpenDiagram := {
    diagram := source.diagram.val
    boundary := source.checked.val.boundary
  }
  let sourceExternalEq :
      (sourceCompiler.castArity coalescedArity).externalClasses =
        sourceOpen.exposedWires.length := by
    simp [sourceCompiler, sourceOpen,
      Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern,
      Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
      Concrete.Splice.replaceOpenBody,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot]
  let targetExternalEq :
      (source.checked.elaborate.withBody
        (rootAtStartTargetBody source selection anchorRoot assembly)
      ).externalClasses = targetOpen.exposedWires.length := by
    rfl
  let external :=
    ((FiniteEquiv.finCast sourceExternalEq).trans
      quotient.exposedWiresEquiv).trans
        (FiniteEquiv.finCast targetExternalEq.symm)
  let sourceFactor := rootAtStart_sourceBodyFactor source selection
    anchorRoot fragment assembly admissible
  let hostBodyIso := sourceFactor.val
  let quotientSourceLocalEq :=
    coalesced.val.elaborate_body_localCount coalesced.property
  have hostBodyLocalEq : hostBodyIso.localEquivCast
      quotientSourceLocalEq rfl =
        quotient.hiddenWiresEquiv.trans assembly.source_iso.localEquiv :=
    sourceFactor.property
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput
    admissible
  let outputWitness :=
    Concrete.Splice.Input.compiledSpliceOutputRootWitness spliceInput
      plugLayout admissible siteRoot
  let outputLeaf :=
    Concrete.Splice.Input.compiledSpliceOutputRootLeaf spliceInput plugLayout
      admissible siteRoot
  let binderWitness := plugLayout.patternBinderWitnessOfEnumeration admissible
    fragment.binders fragment.enumeration outputWitness outputLeaf
  let hostPrepared :=
    Concrete.Splice.Input.compiledSpliceRootHostPreparedOfExactPattern
      spliceInput plugLayout admissible siteRoot
  let patternPrepared :=
    Concrete.Splice.Input.compiledSpliceRootPatternPreparedOfExactPattern
      spliceInput plugLayout admissible siteRoot fragment.context
      fragment.contextExact fragment.binders fragment.enumeration fragment.items
  let reindex := plugLayout.rootReindexOfExactPattern spliceInput admissible
    source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped siteRoot
  let checkedCoalesced :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
      admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let rootEq : checkedCoalesced.val.rootWires.length =
      checkedCoalesced.val.exposedWires.length +
        checkedCoalesced.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let hostContext := host.compilerLeaf.inheritedWires.extend spliceInput.site
  let hostExact : hostContext.Exact spliceInput.coalesceFrameRaw.root := by
    change hostContext.Exact spliceInput.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let hostTransport :=
    (Concrete.exactContextToOpenRootWireEquiv checkedCoalesced hostContext
      hostExact).trans (FiniteEquiv.finCast rootEq)
  let openItems :=
    Concrete.Splice.Input.compiledSpliceOpenRootItems checkedCoalesced
  let coalescedBody : Region checkedCoalesced.val.exposedWires.length [] :=
    .mk checkedCoalesced.val.hiddenWires.length
      (openItems.items.castWiresEq rootEq)
  have checkedCoalescedBodyEq : checkedCoalesced.elaborate.body =
      coalescedBody := by
    rw [openItems.elaborate_body]
    rfl
  let hostFactorIso : RegionIso quotient.exposedWiresEquiv []
      coalescedBody assembly.sourceBody :=
    Eq.mp (congrArg (fun body => RegionIso quotient.exposedWiresEquiv []
      body assembly.sourceBody) checkedCoalescedBodyEq) hostBodyIso
  have hostFactorLocalEq : hostFactorIso.localEquivCast rfl rfl =
      quotient.hiddenWiresEquiv.trans
        assembly.source_iso.localEquiv := by
    have preserved := RegionIso.localEquivCast_castEndpoints hostBodyIso
      checkedCoalescedBodyEq rfl quotientSourceLocalEq rfl rfl rfl
    have preserved' : hostFactorIso.localEquivCast rfl rfl =
        hostBodyIso.localEquivCast quotientSourceLocalEq rfl := by
      simpa only [hostFactorIso] using preserved
    exact preserved'.trans hostBodyLocalEq
  let hostEmbedding := Region.adjoinHostWire
    checkedCoalesced.val.exposedWires.length
    checkedCoalesced.val.hiddenWires.length
    plugLayout.bodyInternalCarriers.length
  let hostNormalization : ItemSeqIso
      (FiniteEquiv.refl (Fin (checkedCoalesced.val.exposedWires.length +
        (checkedCoalesced.val.hiddenWires.length +
          plugLayout.bodyInternalCarriers.length)))) []
      (hostPrepared.renameWires reindex)
      ((openItems.items.castWiresEq rootEq).renameWires hostEmbedding) := by
    simpa [hostPrepared, reindex, checkedCoalesced, rootEq, openItems,
      hostEmbedding] using
      (Concrete.Splice.Input.PlugLayout.compiledSpliceRootHostNormalizationIso
        spliceInput plugLayout admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped siteRoot)
  suffices coreBodyIso : RegionIso quotient.exposedWiresEquiv []
      (.mk (sourceOpen.hiddenWires.length +
          plugLayout.bodyInternalCarriers.length)
        ((hostPrepared.append patternPrepared).renameWires reindex))
      (rootAtStartTargetBody source selection anchorRoot assembly) by
    let sourceCast := Fin.cast sourceExternalEq.symm
    let targetId : Fin source.checked.elaborate.externalClasses →
        Fin source.checked.elaborate.externalClasses := id
    have commutes : external.toFun ∘ sourceCast = targetId ∘
        quotient.exposedWiresEquiv.toFun := by
      funext index
      apply Fin.ext
      rfl
    have lifted := coreBodyIso.renameWires_commuting sourceCast targetId
      external commutes
    have castBodyEq := OpenDiagram.castArity_body sourceCompiler
      coalescedArity sourceExternalEq
    have sourceCompilerBodyEq : sourceCompiler.body =
        .mk (sourceOpen.hiddenWires.length +
            plugLayout.bodyInternalCarriers.length)
          ((hostPrepared.append patternPrepared).renameWires reindex) := by
      rfl
    rw [castBodyEq, sourceCompilerBodyEq]
    let renamedSource :=
      (Region.mk (sourceOpen.hiddenWires.length +
          plugLayout.bodyInternalCarriers.length)
        ((hostPrepared.append patternPrepared).renameWires reindex)
      ).renameWires sourceCast
    have targetCancel :
        (rootAtStartTargetBody source selection anchorRoot assembly
          ).renameWires targetId =
        rootAtStartTargetBody source selection anchorRoot assembly := by
      simpa [targetId] using Region.renameWires_id
        (rootAtStartTargetBody source selection anchorRoot assembly)
    let transported : RegionIso external [] renamedSource
        (rootAtStartTargetBody source selection anchorRoot assembly) :=
      Eq.mp (congrArg (fun target => RegionIso external [] renamedSource target)
        targetCancel) lifted
    exact transported
  cases sourceBodyEq : assembly.sourceBody with
  | mk targetLocal targetItems =>
    let sourceBodyLocalEq : assembly.sourceBody.localCount = targetLocal :=
      congrArg Region.localCount sourceBodyEq
    have targetLocalRoot : targetLocal =
        source.checked.val.hiddenWires.length := by
      calc
        targetLocal = assembly.sourceBody.localCount :=
          sourceBodyLocalEq.symm
        _ = (rootSourcePartition source selection anchorRoot
              ).anchorLocal := assembly.sourceBody_localCount
        _ = source.checked.val.hiddenWires.length := by rfl
    cases targetLocalRoot
    let targetLocal := source.checked.val.hiddenWires.length
    let assemblyLocal := assembly.source_iso.localEquivCast rfl
      sourceBodyLocalEq
    let hostFactorIso' : RegionIso quotient.exposedWiresEquiv []
        coalescedBody (.mk targetLocal targetItems) :=
      Eq.mp (congrArg (fun target => RegionIso
        quotient.exposedWiresEquiv [] coalescedBody target) sourceBodyEq)
        hostFactorIso
    have hostFactorLocalEqAtTarget :
        hostFactorIso.localEquivCast rfl sourceBodyLocalEq =
          quotient.hiddenWiresEquiv.trans assemblyLocal := by
      have native : hostFactorIso.localEquiv =
          quotient.hiddenWiresEquiv.trans
            assembly.source_iso.localEquiv := by
        simpa only [RegionIso.localEquivCast] using hostFactorLocalEq
      have hostCast := RegionIso.localEquivCast_target hostFactorIso
        sourceBodyLocalEq
      have assemblyCast := RegionIso.localEquivCast_target
        assembly.source_iso sourceBodyLocalEq
      calc
        hostFactorIso.localEquivCast rfl sourceBodyLocalEq =
            hostFactorIso.localEquiv.trans
              (FiniteEquiv.finCast sourceBodyLocalEq) := hostCast
        _ = (quotient.hiddenWiresEquiv.trans
              assembly.source_iso.localEquiv).trans
              (FiniteEquiv.finCast sourceBodyLocalEq) :=
          congrArg (fun value => value.trans
            (FiniteEquiv.finCast sourceBodyLocalEq)) native
        _ = quotient.hiddenWiresEquiv.trans
            (assembly.source_iso.localEquiv.trans
              (FiniteEquiv.finCast sourceBodyLocalEq)) := by
          apply FiniteEquiv.ext
          intro index
          rfl
        _ = quotient.hiddenWiresEquiv.trans assemblyLocal := by
          apply congrArg (fun value => quotient.hiddenWiresEquiv.trans value)
          exact assemblyCast.symm
    have hostFactorLocalEq' : hostFactorIso'.localEquivCast rfl rfl =
        quotient.hiddenWiresEquiv.trans assemblyLocal := by
      have preserved := RegionIso.localEquivCast_castEndpoints hostFactorIso
        rfl sourceBodyEq rfl sourceBodyLocalEq rfl rfl
      have preserved' : hostFactorIso'.localEquivCast rfl rfl =
          hostFactorIso.localEquivCast rfl sourceBodyLocalEq := by
        simpa only [hostFactorIso'] using preserved
      exact preserved'.trans hostFactorLocalEqAtTarget
    dsimp only [coalescedBody] at hostFactorIso'
    cases hostFactorWitness : hostFactorIso' with
    | @mk _ _ _ _ _ _ _ _ hostLocal hostItemsIso =>
      let copyLocal := bodyInternalExplicitEquiv source.diagram selection
      let combinedLocal := extendWireEquiv hostLocal copyLocal
      let combinedWire := extendWireEquiv quotient.exposedWiresEquiv
        combinedLocal
      let targetHostEmbedding := Region.adjoinHostWire
        source.checked.elaborate.externalClasses targetLocal
        selection.val.explicitWires.length
      let hostWire := extendWireEquiv quotient.exposedWiresEquiv hostLocal
      have hostEmbeddingCommute :
          combinedWire.toFun ∘ hostEmbedding =
            targetHostEmbedding ∘ hostWire.toFun := by
        simpa only [combinedWire, combinedLocal, hostEmbedding,
          targetHostEmbedding, hostWire] using
            Region.adjoinHostWire_extendWireEquiv
              quotient.exposedWiresEquiv hostLocal copyLocal
      let hostItemsLifted := hostItemsIso.renameWires_commuting hostEmbedding
        targetHostEmbedding combinedWire hostEmbeddingCommute
      let hostBlock : ItemSeqIso combinedWire []
          (hostPrepared.renameWires reindex)
          (targetItems.renameWires targetHostEmbedding) :=
        hostNormalization.trans hostItemsLifted
      let quotientRootWire := extendWireEquiv quotient.exposedWiresEquiv
        quotient.hiddenWiresEquiv
      have hostLocalEq : hostLocal =
          quotient.hiddenWiresEquiv.trans
            assemblyLocal := by
        simpa only [hostFactorWitness, RegionIso.localEquivCast]
          using hostFactorLocalEq'
      let sourceWireAtTarget := extendWireEquiv
        (FiniteEquiv.refl
          (Fin source.checked.elaborate.externalClasses)) assemblyLocal
      have hostWireEq : hostWire =
          quotientRootWire.trans sourceWireAtTarget := by
        apply FiniteEquiv.ext
        intro index
        refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
          index
        · have quotientOuterWire : quotientRootWire
                (Fin.castAdd checkedCoalesced.val.hiddenWires.length
                  inherited) =
              Fin.castAdd source.checked.val.hiddenWires.length
                (quotient.exposedWiresEquiv inherited) := by
            simpa only [quotientRootWire] using
              (extendWireEquiv_outer quotient.exposedWiresEquiv
                quotient.hiddenWiresEquiv inherited)
          have sourceOuterWire : sourceWireAtTarget
                (Fin.castAdd source.checked.val.hiddenWires.length
                  (quotient.exposedWiresEquiv inherited)) =
              Fin.castAdd targetLocal
                (quotient.exposedWiresEquiv inherited) := by
            simpa only [sourceWireAtTarget] using
              (extendWireEquiv_outer
                (FiniteEquiv.refl
                  (Fin source.checked.elaborate.externalClasses))
                assemblyLocal (quotient.exposedWiresEquiv inherited))
          have hostOuterWire : hostWire
                (Fin.castAdd checkedCoalesced.val.hiddenWires.length
                  inherited) =
              Fin.castAdd targetLocal
                (quotient.exposedWiresEquiv inherited) := by
            simpa only [hostWire] using
              (extendWireEquiv_outer quotient.exposedWiresEquiv
                hostLocal inherited)
          change hostWire
              (Fin.castAdd checkedCoalesced.val.hiddenWires.length
                inherited) =
            sourceWireAtTarget
              (quotientRootWire
                (Fin.castAdd checkedCoalesced.val.hiddenWires.length
                  inherited))
          rw [quotientOuterWire]
          exact hostOuterWire.trans sourceOuterWire.symm
        · have quotientLocalWire : quotientRootWire
              (Fin.natAdd
                (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
                  spliceInput source.checked.val.boundary
                  ).exposedWires.length localIndex) =
            Fin.natAdd source.checked.elaborate.externalClasses
              (quotient.hiddenWiresEquiv localIndex) := by
            simpa only [quotientRootWire] using
              (extendWireEquiv_local quotient.exposedWiresEquiv
                quotient.hiddenWiresEquiv localIndex)
          change hostWire
              (Fin.natAdd
                (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
                  spliceInput source.checked.val.boundary
                  ).exposedWires.length localIndex) =
            sourceWireAtTarget (quotientRootWire
              (Fin.natAdd
                (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
                  spliceInput source.checked.val.boundary
                  ).exposedWires.length localIndex))
          rw [quotientLocalWire]
          have sourceLocalWire : sourceWireAtTarget
                (Fin.natAdd source.checked.elaborate.externalClasses
                  (quotient.hiddenWiresEquiv localIndex)) =
              Fin.natAdd source.checked.elaborate.externalClasses
                (assemblyLocal (quotient.hiddenWiresEquiv localIndex)) := by
            simpa only [sourceWireAtTarget] using
              (extendWireEquiv_local
                (FiniteEquiv.refl
                  (Fin source.checked.elaborate.externalClasses))
                assemblyLocal (quotient.hiddenWiresEquiv localIndex))
          have hostLocalWire : hostWire
                (Fin.natAdd
                  (Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
                    spliceInput source.checked.val.boundary
                    ).exposedWires.length localIndex) =
              Fin.natAdd source.checked.elaborate.externalClasses
                (hostLocal localIndex) := by
            simpa only [hostWire] using
              (extendWireEquiv_local quotient.exposedWiresEquiv
                hostLocal localIndex)
          have localApply : hostLocal localIndex =
              assemblyLocal (quotient.hiddenWiresEquiv localIndex) := by
            rw [hostLocalEq]
            rfl
          exact hostLocalWire.trans
            ((congrArg (Fin.natAdd source.checked.elaborate.externalClasses)
              localApply).trans sourceLocalWire.symm)
      let materialBinder :=
        IterationExtraction.ExtractionBinderWitness.terminal source.diagram
          selection ({} : FragmentLayout source.diagram.val selection)
          fragment.binders fragment.enumeration
          (rootLeaf source selection anchorRoot).binders
          (rootLeaf source selection anchorRoot).bindersCover
      let compilerBinderMap : RelationRenaming fragment.rels [] :=
        fun relation => binderWitness.relationMap relation
      let materialBinderMap : RelationRenaming fragment.rels [] :=
        fun relation => materialBinder.relationMap relation
      have binderMapEq :
          (fun (relationArity : Nat)
              (relation : RelVar fragment.rels relationArity) =>
            @compilerBinderMap relationArity relation) =
          (fun (relationArity : Nat)
              (relation : RelVar fragment.rels relationArity) =>
            @materialBinderMap relationArity relation) := by
        funext relationArity relation
        exact Fin.elim0 (@compilerBinderMap relationArity relation).index
      let patternWire :=
        plugLayout.patternPreparedWireOfExactPattern admissible host
          fragment.context fragment.contextExact outputWitness outputLeaf
      let compilerFragmentMap := reindex.toFun ∘ patternWire
      let materialPrepared :=
        fragment.items.renameRelations materialBinderMap
      have patternPreparedEq : patternPrepared.renameWires reindex =
          materialPrepared.renameWires compilerFragmentMap := by
        rw [show patternPrepared =
          materialPrepared.renameWires patternWire by
          unfold patternPrepared
          unfold Concrete.Splice.Input.compiledSpliceRootPatternPreparedOfExactPattern
          dsimp only
          rw [ItemSeq.renameWires_renameRelations]
          change (fragment.items.renameRelations compilerBinderMap
            ).renameWires patternWire =
              (fragment.items.renameRelations materialBinderMap
                ).renameWires patternWire
          rw [binderMapEq]]
        exact ItemSeq.renameWires_comp materialPrepared patternWire reindex
      cases materialIsoEq : assembly.material_iso with
      | @mk _ _ _ _ _ _ _ _ materialLocal materialItemsIso =>
        let materialWire := extendWireEquiv
          (FiniteEquiv.refl
            (Fin (rootSourcePartition source selection
              anchorRoot).ancestorWires)) materialLocal
        have targetWitnessHere :
            assembly.route_alignment.targetWitness =
              Region.ContextPath.here
                ((Region.mk 0 assembly.keptItems).renameWires
                  (rootSourcePartition source selection
                    anchorRoot).wire) := by
          rfl
        have rootAncestorEq :
            (rootSourcePartition source selection anchorRoot
              ).ancestorWires =
              source.checked.elaborate.externalClasses := by
          rfl
        have targetHoleWiresEq :
            assembly.route_alignment.targetWitness.toFocus.holeWires =
              source.checked.elaborate.externalClasses + targetLocal := by
          calc
            assembly.route_alignment.targetWitness.toFocus.holeWires =
                (rootSourcePartition source selection anchorRoot
                  ).ancestorWires +
                  (rootSourcePartition source selection anchorRoot
                    ).anchorLocal := by
              rw [targetWitnessHere]
              rfl
            _ = (rootSourcePartition source selection anchorRoot
                  ).ancestorWires + targetLocal :=
              congrArg (fun localCount =>
                (rootSourcePartition source selection anchorRoot
                  ).ancestorWires + localCount)
                (assembly.sourceBody_localCount.symm.trans
                  sourceBodyLocalEq)
            _ = source.checked.elaborate.externalClasses + targetLocal :=
              congrArg (fun outer => outer + targetLocal) rootAncestorEq
        let rootCopyWire :
            Fin ((rootSourcePartition source selection anchorRoot
                ).ancestorWires + assembly.sourceBody.localCount) →
              Fin (source.checked.elaborate.externalClasses +
                (targetLocal + selection.val.explicitWires.length)) := by
          exact fun index => Fin.cast
            ((congrArg (fun holeWires =>
                holeWires + selection.val.explicitWires.length)
                targetHoleWiresEq).trans
              (Nat.add_assoc source.checked.elaborate.externalClasses
                targetLocal selection.val.explicitWires.length))
            (assembly.copyWires.wire index)
        let targetMaterialMap :
            Fin ((rootSourcePartition source selection anchorRoot
                ).ancestorWires + assembly.materialTarget.localCount) →
              Fin (source.checked.elaborate.externalClasses +
                (targetLocal + selection.val.explicitWires.length)) :=
          rootCopyWire ∘ assembly.sourceSelectedEmbedding
        let sourceMaterialMap := combinedWire.symm.toFun ∘
          targetMaterialMap ∘ materialWire.toFun
        have materialCommutes : combinedWire.toFun ∘ sourceMaterialMap =
            targetMaterialMap ∘ materialWire.toFun := by
          funext index
          exact combinedWire.right_inv
            (targetMaterialMap (materialWire index))
        let materialBlockRaw : ItemSeqIso combinedWire []
            ((materialPrepared.renameWires
              assembly.fragmentSourceEmbedding).renameWires
                sourceMaterialMap)
            ((Region.items assembly.materialTarget).renameWires
              targetMaterialMap) := by
          have materialSourceItemsEq :
              Region.items assembly.materialSource =
                materialPrepared.renameWires
                  assembly.fragmentSourceEmbedding := by
            change
              (materialPrepared.renameWires
                  (IterationExtraction.extractionContextIndexMap
                    source.diagram selection
                    ({} : FragmentLayout source.diagram.val selection)
                    fragment.context
                    ((rootLeaf source selection anchorRoot).inheritedWires.extend
                      selection.val.anchor)
                    fragment.contextExact
                    (rootLeaf source selection anchorRoot).wiresExact)
                ).renameWires
                  (rootSourcePartition source selection anchorRoot).wire =
                materialPrepared.renameWires
                  ((rootSourcePartition source selection anchorRoot).wire ∘
                    IterationExtraction.extractionContextIndexMap
                      source.diagram selection
                      ({} : FragmentLayout source.diagram.val selection)
                      fragment.context
                      ((rootLeaf source selection anchorRoot
                        ).inheritedWires.extend selection.val.anchor)
                      fragment.contextExact
                      (rootLeaf source selection anchorRoot).wiresExact)
            exact ItemSeq.renameWires_comp _ _ _
          have renamedSourceEq := congrArg
            (ItemSeq.renameWires sourceMaterialMap) materialSourceItemsEq
          have raw := materialItemsIso.renameWires_commuting
            sourceMaterialMap targetMaterialMap combinedWire
            materialCommutes
          exact Eq.mp (congrArg (fun sourceItems => ItemSeqIso
            combinedWire [] sourceItems
              ((Region.items assembly.materialTarget).renameWires
                targetMaterialMap)) renamedSourceEq) raw
        have materialSourceMapEq :
            sourceMaterialMap ∘ assembly.fragmentSourceEmbedding =
              compilerFragmentMap := by
          funext index
          apply combinedWire.injective
          change combinedWire
              (sourceMaterialMap
                (assembly.fragmentSourceEmbedding index)) =
            combinedWire (compilerFragmentMap index)
          have sourceCancel : combinedWire
              (sourceMaterialMap
                (assembly.fragmentSourceEmbedding index)) =
              targetMaterialMap
                (materialWire (assembly.fragmentSourceEmbedding index)) :=
            combinedWire.right_inv _
          rw [sourceCancel]
          have selectedCommute := congrFun
            assembly.selectedEmbedding_commuting index
          have selectedCommute' : assembly.sourceSelectedEmbedding
                (materialWire (assembly.fragmentSourceEmbedding index)) =
              assembly.sourceWire
                (assembly.fragmentSourceEmbedding index) := by
            simpa [materialWire, materialIsoEq,
              FactorAssembly.sourceWire, Function.comp_apply] using
                selectedCommute
          rw [show targetMaterialMap
              (materialWire (assembly.fragmentSourceEmbedding index)) =
                rootCopyWire
                  (assembly.sourceWire
                    (assembly.fragmentSourceEmbedding index)) by
            exact congrArg rootCopyWire selectedCommute']
          let fragmentWire := fragment.context.get index
          by_cases exposedMember :
              fragmentWire ∈ spliceInput.pattern.val.exposedWires
          · obtain ⟨exposed, exposedGet⟩ :=
              List.mem_iff_get.mp exposedMember
            have represents : fragment.context.get index =
                spliceInput.pattern.val.exposedWires.get exposed := by
              exact exposedGet.symm
            let hostIndex := plugLayout.exposedWireRenaming admissible host
              exposed
            have compilerExposed :=
              Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_pattern_exposed_factor_exact
                spliceInput plugLayout admissible
                source.checked.val.boundary
                source.checked.property.boundary_is_root_scoped siteRoot
                fragment.context fragment.contextExact index exposed
                represents
            have compilerExposedEq : compilerFragmentMap index =
                hostEmbedding (hostTransport hostIndex) := by
              calc
                compilerFragmentMap index =
                    Region.conjoinLeftWire
                      checkedCoalesced.val.exposedWires.length
                      checkedCoalesced.val.hiddenWires.length
                      plugLayout.bodyInternalCarriers.length
                      (hostTransport hostIndex) := by
                  simpa [compilerFragmentMap, patternWire, hostTransport,
                    hostContext, hostExact, rootEq, checkedCoalesced,
                    hostIndex,
                    Concrete.Splice.Input.PlugLayout.rootHostOpenEmbedding]
                    using compilerExposed
                _ = hostEmbedding (hostTransport hostIndex) := by
                  simpa only [hostEmbedding] using congrFun
                    (Region.conjoinLeftWire_eq_adjoinHostWire
                      checkedCoalesced.val.exposedWires.length
                      checkedCoalesced.val.hiddenWires.length
                      plugLayout.bodyInternalCarriers.length)
                    (hostTransport hostIndex)
            have rootCoordinateEq : quotientRootWire
                  (hostTransport hostIndex) =
                assembly.fragmentSourceEmbedding index := by
              let sourceRootEq : source.checked.val.rootWires.length =
                  source.checked.elaborate.externalClasses +
                    source.checked.val.hiddenWires.length := by
                simp [Concrete.OpenDiagram.rootWires]
              have quotientRootWire_get
                  (position : Fin
                    (checkedCoalesced.val.exposedWires.length +
                      checkedCoalesced.val.hiddenWires.length)) :
                  source.checked.val.rootWires.get
                      (Fin.cast sourceRootEq.symm
                        (quotientRootWire position)) =
                    quotient.diagram.wires
                      (checkedCoalesced.val.rootWires.get
                        (Fin.cast rootEq.symm position)) := by
                simpa only [quotientRootWire, sourceOpen] using
                  quotient.rootWiresEquiv_spec position
              have hostTransportGet : checkedCoalesced.val.rootWires.get
                    (Fin.cast rootEq.symm
                      (hostTransport hostIndex)) =
                  hostContext.get hostIndex := by
                have spec :=
                  Concrete.exactContextToOpenRootWireEquiv_spec
                    checkedCoalesced hostContext hostExact hostIndex
                simpa [hostTransport, FiniteEquiv.trans_apply,
                  FiniteEquiv.finCast] using spec
              have hostIndexGet : hostContext.get hostIndex =
                  plugLayout.exposedAttachment exposed := by
                simpa [hostContext, hostIndex] using
                  plugLayout.exposedWireRenaming_spec admissible host exposed
              have attachmentOrigin :=
                IterationTransport.iterationExposedAttachment_eq_fragmentOrigin
                  source.diagram selection selection.val.anchor exposed
              dsimp only at attachmentOrigin
              have leftGet : source.checked.val.rootWires.get
                    (Fin.cast sourceRootEq.symm
                      (quotientRootWire (hostTransport hostIndex))) =
                  source.diagram.val.fragmentWireOrigin selection
                    ({} : FragmentLayout source.diagram.val selection)
                    (fragment.context.get index) := by
                rw [quotientRootWire_get, hostTransportGet, hostIndexGet,
                  attachmentOrigin]
                change IterationQuotient.quotientWireEquiv source.diagram
                    selection selection.val.anchor
                    ((iterationInput source.diagram selection
                      selection.val.anchor).quotientWire
                      (source.diagram.val.fragmentWireOrigin selection
                        ({} : FragmentLayout source.diagram.val selection)
                        (spliceInput.pattern.val.exposedWires.get exposed))) = _
                rw [IterationQuotient.quotientWireEquiv_quotientWire,
                  represents]
              let leafContext :=
                (rootLeaf source selection anchorRoot).inheritedWires.extend
                  selection.val.anchor
              let extractionIndex :=
                IterationExtraction.extractionContextIndexMap source.diagram
                  selection
                  ({} : FragmentLayout source.diagram.val selection)
                  fragment.context leafContext fragment.contextExact
                  (rootLeaf source selection anchorRoot).wiresExact index
              have extractionGet :=
                IterationExtraction.extractionContextIndexMap_spec
                  source.diagram selection
                  ({} : FragmentLayout source.diagram.val selection)
                  fragment.context leafContext fragment.contextExact
                  (rootLeaf source selection anchorRoot).wiresExact index
              have leafExact : leafContext.Exact
                  source.checked.val.diagram.root := by
                change leafContext.Exact source.diagram.val.root
                rw [← anchorRoot]
                exact (rootLeaf source selection anchorRoot).wiresExact
              let exactWire := Concrete.exactContextToOpenRootWireEquiv
                source.checked leafContext leafExact
              have exactGet :=
                Concrete.exactContextToOpenRootWireEquiv_spec source.checked
                  leafContext leafExact extractionIndex
              have rightGet : source.checked.val.rootWires.get
                    (Fin.cast sourceRootEq.symm
                      (assembly.fragmentSourceEmbedding index)) =
                  source.diagram.val.fragmentWireOrigin selection
                    ({} : FragmentLayout source.diagram.val selection)
                    (fragment.context.get index) := by
                calc
                  _ = leafContext.get extractionIndex := by
                    simpa [FactorAssembly.fragmentSourceEmbedding,
                      rootSourcePartition, extractionIndex, exactWire,
                      sourceRootEq, FiniteEquiv.trans_apply,
                      FiniteEquiv.finCast] using exactGet
                  _ = _ := extractionGet.symm
              apply Fin.ext
              apply (List.getElem_inj
                source.checked.val.rootWires_nodup).mp
              simpa only [List.get_eq_getElem] using
                leftGet.trans rightGet.symm
            have notFresh : ∀ fresh,
                assembly.copyWires.sourceOfFresh fresh ≠
                  assembly.sourceWire
                    (assembly.fragmentSourceEmbedding index) := by
              intro fresh equality
              have freshGet := assembly.copyWires_sourceOfFresh_get fresh
              rw [equality] at freshGet
              simp only [FiniteEquiv.symm_apply_apply] at freshGet
              let leafContext :=
                (rootLeaf source selection anchorRoot).inheritedWires.extend
                  selection.val.anchor
              let extractionIndex :=
                IterationExtraction.extractionContextIndexMap source.diagram
                  selection
                  ({} : FragmentLayout source.diagram.val selection)
                  fragment.context leafContext fragment.contextExact
                  (rootLeaf source selection anchorRoot).wiresExact index
              have partitionCancel :
                  (rootSourcePartition source selection anchorRoot).wire.symm
                      (assembly.fragmentSourceEmbedding index) =
                    extractionIndex := by
                change (rootSourcePartition source selection anchorRoot
                  ).wire.symm
                    ((rootSourcePartition source selection anchorRoot).wire
                      extractionIndex) = extractionIndex
                exact (rootSourcePartition source selection anchorRoot
                  ).wire.left_inv extractionIndex
              rw [partitionCancel] at freshGet
              have extractionGet :=
                IterationExtraction.extractionContextIndexMap_spec
                  source.diagram selection
                  ({} : FragmentLayout source.diagram.val selection)
                  fragment.context leafContext fragment.contextExact
                  (rootLeaf source selection anchorRoot).wiresExact index
              have originExplicit :
                  source.diagram.val.fragmentWireOrigin selection
                      ({} : FragmentLayout source.diagram.val selection)
                      (fragment.context.get index) =
                    selection.val.explicitWires.get fresh :=
                extractionGet.trans freshGet
              have exposedBoundary :=
                (Concrete.OpenDiagram.mem_exposedWires
                  spliceInput.pattern.val
                  (spliceInput.pattern.val.exposedWires.get exposed)).1
                    (List.get_mem _ exposed)
              change spliceInput.pattern.val.exposedWires.get exposed ∈
                  source.diagram.val.extractBoundaryRaw selection
                    (let iterationLayout :
                      FragmentLayout source.diagram.val selection :=
                        { externalBinders := selection.externalBinders
                          externalBinders_exact := rfl }
                    iterationLayout) at exposedBoundary
              obtain ⟨boundaryIndex, boundaryGet⟩ :=
                List.mem_ofFn.mp exposedBoundary
              have originTouching :
                  source.diagram.val.fragmentWireOrigin selection
                      ({} : FragmentLayout source.diagram.val selection)
                      (fragment.context.get index) ∈
                    selection.touchingWires := by
                rw [represents, ← boundaryGet]
                simp [Concrete.Diagram.fragmentWireOrigin,
                  FragmentLayout.boundaryWire]
              have originInternal :
                  source.diagram.val.fragmentWireOrigin selection
                      ({} : FragmentLayout source.diagram.val selection)
                      (fragment.context.get index) ∈
                    selection.internalWires := by
                rw [originExplicit]
                exact selection.explicitWire_mem_internalWires
                  (List.get_mem _ fresh)
              exact (selection.mem_touchingWires_consequences
                originTouching).1 originInternal
            rw [compilerExposedEq,
              show combinedWire (hostEmbedding (hostTransport hostIndex)) =
                  targetHostEmbedding
                    (hostWire (hostTransport hostIndex)) from
                congrFun hostEmbeddingCommute (hostTransport hostIndex),
              hostWireEq, FiniteEquiv.trans_apply, rootCoordinateEq]
            dsimp only [rootCopyWire]
            rw [assembly.copyWires.wire_inherited _ notFresh]
            apply Fin.ext
            simp [targetHostEmbedding, sourceWireAtTarget, assemblyLocal,
              FactorAssembly.sourceWire, FactorAssembly.descendant,
              Region.adjoinHostWire]
            rfl
          · have fragmentEncloses :
                spliceInput.pattern.val.diagram.Encloses
                  (spliceInput.pattern.val.diagram.wires fragmentWire).scope
                  spliceInput.binderSpine.bodyContainer :=
              (Concrete.Elaboration.WireContext.Exact.mem_iff
                fragment.contextExact fragmentWire).1
                  (List.get_mem fragment.context index)
            have fragmentScope :
                (spliceInput.pattern.val.diagram.wires fragmentWire).scope =
                  spliceInput.binderSpine.bodyContainer :=
              match Concrete.Splice.Input.PlugLayout.patternWire_scope_material_or_bodyContainer
                  spliceInput fragmentWire exposedMember with
              | .inl material => False.elim
                  (plugLayout.material_not_encloses_bodyContainer _ material
                    fragmentEncloses)
              | .inr scope => scope
            have internalMember : fragmentWire ∈
                plugLayout.bodyInternalOriginalWires :=
              (plugLayout.mem_bodyInternalOriginalWires fragmentWire).2
                ⟨exposedMember, fragmentScope⟩
            obtain ⟨internal, internalMember, originEq⟩ :=
              List.mem_map.mp internalMember
            obtain ⟨carrier, carrierGet⟩ :=
              List.mem_iff_get.mp internalMember
            have represents : fragment.context.get index =
                plugLayout.internalWires.origin
                  (plugLayout.bodyInternalCarriers.get carrier) := by
              exact (show fragmentWire = _ from
                originEq.symm.trans (congrArg plugLayout.internalWires.origin
                  carrierGet.symm))
            let fresh := copyLocal carrier
            have freshSpec := bodyInternalExplicitEquiv_spec source.diagram
              selection carrier
            have representsFresh : source.diagram.val.fragmentWireOrigin
                  selection
                  ({} : FragmentLayout source.diagram.val selection)
                  (fragment.context.get index) =
                selection.val.explicitWires.get fresh := by
              exact (congrArg
                (source.diagram.val.fragmentWireOrigin selection
                  ({} : FragmentLayout source.diagram.val selection))
                represents).trans (by
                  simpa [fresh, copyLocal, spliceInput, plugLayout]
                    using freshSpec.symm)
            have sourceFresh :=
              assembly.sourceWire_fragmentSourceEmbedding_eq_sourceOfFresh
                index fresh representsFresh
            rw [sourceFresh]
            dsimp only [rootCopyWire]
            rw [assembly.copyWires.wire_fresh]
            have compilerInternal :=
              Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_pattern_internal_factor_exact
                spliceInput plugLayout admissible
                source.checked.val.boundary
                source.checked.property.boundary_is_root_scoped siteRoot
                fragment.context fragment.contextExact index carrier
                represents
            rw [show compilerFragmentMap index =
                Fin.natAdd checkedCoalesced.val.exposedWires.length
                  (Fin.natAdd checkedCoalesced.val.hiddenWires.length
                    carrier) by
              simpa [compilerFragmentMap, patternWire,
                checkedCoalesced] using compilerInternal]
            apply Fin.ext
            change assembly.route_alignment.targetWitness.toFocus.holeWires +
                fresh.val =
              (combinedWire
                (Fin.natAdd checkedCoalesced.val.exposedWires.length
                  (Fin.natAdd checkedCoalesced.val.hiddenWires.length
                    carrier))).val
            rw [targetHoleWiresEq]
            have combinedInternal : combinedWire
                  (Fin.natAdd checkedCoalesced.val.exposedWires.length
                    (Fin.natAdd checkedCoalesced.val.hiddenWires.length
                      carrier)) =
                  Fin.natAdd source.checked.val.exposedWires.length
                    (Fin.natAdd targetLocal (copyLocal carrier)) := by
              change (extendWireEquiv quotient.exposedWiresEquiv
                  (extendWireEquiv hostLocal copyLocal))
                    (Fin.natAdd sourceOpen.exposedWires.length
                      (Fin.natAdd checkedCoalesced.val.hiddenWires.length
                        carrier)) = _
              rw [extendWireEquiv_local, extendWireEquiv_local]
              rfl
            rw [combinedInternal]
            simp [Concrete.CheckedOpen.elaborate_externalClasses,
              fresh, Nat.add_assoc]
        have materialSourceItemsEq :
            (materialPrepared.renameWires assembly.fragmentSourceEmbedding
              ).renameWires sourceMaterialMap =
            patternPrepared.renameWires reindex := by
          rw [ItemSeq.renameWires_comp, materialSourceMapEq,
            patternPreparedEq]
          rfl
        let materialBlock : ItemSeqIso combinedWire []
            (patternPrepared.renameWires reindex)
            ((Region.items assembly.materialTarget).renameWires
              targetMaterialMap) :=
          Eq.mp (congrArg (fun sourceItems => ItemSeqIso combinedWire []
            sourceItems
              ((Region.items assembly.materialTarget).renameWires
                targetMaterialMap))
            materialSourceItemsEq) materialBlockRaw
        let combinedItems := hostBlock.append materialBlock
        let normalizedBody : Region
            source.checked.elaborate.externalClasses [] :=
          .mk (targetLocal + selection.val.explicitWires.length)
            ((targetItems.renameWires targetHostEmbedding).append
              ((Region.items assembly.materialTarget).renameWires
                targetMaterialMap))
        let compilerNormalizedRaw : RegionIso quotient.exposedWiresEquiv []
            (.mk (checkedCoalesced.val.hiddenWires.length +
              plugLayout.bodyInternalCarriers.length)
              ((hostPrepared.renameWires reindex).append
                (patternPrepared.renameWires reindex)))
            normalizedBody := by
          refine RegionIso.mk combinedLocal ?_
          exact combinedItems
        let compilerNormalized : RegionIso quotient.exposedWiresEquiv []
            (.mk (checkedCoalesced.val.hiddenWires.length +
              plugLayout.bodyInternalCarriers.length)
              ((hostPrepared.append patternPrepared).renameWires reindex))
            normalizedBody := by
          let sourceEq :
              Region.mk (checkedCoalesced.val.hiddenWires.length +
                  plugLayout.bodyInternalCarriers.length)
                  ((hostPrepared.append patternPrepared).renameWires
                    reindex) =
                Region.mk (checkedCoalesced.val.hiddenWires.length +
                  plugLayout.bodyInternalCarriers.length)
                  ((hostPrepared.renameWires reindex).append
                    (patternPrepared.renameWires reindex)) :=
            congrArg
              (Region.mk (checkedCoalesced.val.hiddenWires.length +
                plugLayout.bodyInternalCarriers.length))
              (ItemSeq.renameWires_append hostPrepared patternPrepared
                reindex)
          exact sourceEq ▸ compilerNormalizedRaw
        let copyRegion : Region
            assembly.route_alignment.targetWitness.toFocus.holeWires
            assembly.route_alignment.targetWitness.toFocus.holeRels :=
          Region.adjoinAt selection.val.explicitWires.length .nil
            ((assembly.selected.renameWires assembly.copyWires.wire
              ).renameRelations assembly.descendant.outerRelation)
        let selectedItems := assembly.selected.items
        let retained := assembly.descendant.fill assembly.remainder
        let normalizedSite := assembly.selected.conjoin retained
        have sourceBodyPresentation : assembly.sourceBody =
            Region.adjoinAt source.checked.val.hiddenWires.length .nil
              normalizedSite := by
          rfl
        let sourceBodyEndpoint :=
          sourceBodyEq.symm.trans sourceBodyPresentation
        let targetItemsPresentation :=
          Region.itemsCast_eq_of_mk_eq targetItems _ sourceBodyEndpoint
        have normalizedSiteLocalEq : normalizedSite.localCount = 0 := by
          have endpointLocal :=
            congrArg Region.localCount sourceBodyEndpoint
          rw [Region.adjoinAt_localCount] at endpointLocal
          change source.checked.val.hiddenWires.length =
            source.checked.val.hiddenWires.length +
              normalizedSite.localCount at endpointLocal
          omega
        have copyRegionLocalEq : copyRegion.localCount =
            selection.val.explicitWires.length := by
          calc
            copyRegion.localCount =
                selection.val.explicitWires.length +
                  (((assembly.selected.renameWires assembly.copyWires.wire
                    ).renameRelations assembly.descendant.outerRelation
                    ).localCount) :=
              Region.adjoinAt_localCount _ _ _
            _ = selection.val.explicitWires.length +
                  (assembly.selected.renameWires
                    assembly.copyWires.wire).localCount :=
              congrArg (selection.val.explicitWires.length + ·)
                (Region.renameRelations_localCount _ _)
            _ = selection.val.explicitWires.length +
                  assembly.selected.localCount :=
              congrArg (selection.val.explicitWires.length + ·)
                (Region.renameWires_localCount _ _)
            _ = selection.val.explicitWires.length := by rfl
        let normalizedTarget :=
          Region.adjoinAt source.checked.val.hiddenWires.length .nil
            (normalizedSite.conjoin copyRegion)
        let normalizedTargetLocalEq : normalizedTarget.localCount =
            targetLocal + selection.val.explicitWires.length := by
          calc
            normalizedTarget.localCount =
                source.checked.val.hiddenWires.length +
                  (normalizedSite.conjoin copyRegion).localCount :=
              Region.adjoinAt_localCount _ _ _
            _ = source.checked.val.hiddenWires.length +
                  (normalizedSite.localCount + copyRegion.localCount) :=
              congrArg (source.checked.val.hiddenWires.length + ·)
                (Region.conjoin_localCount _ _)
            _ = targetLocal + selection.val.explicitWires.length := by
              rw [normalizedSiteLocalEq, copyRegionLocalEq]
              simp only [Nat.zero_add, targetLocal]
        let normalizedTargetShape :=
          Region.mk_itemsCast normalizedTarget normalizedTargetLocalEq
        have normalizedBodyEq : normalizedBody =
            normalizedTarget := by
          dsimp only [normalizedBody]
          rw [← normalizedTargetShape]
          apply congrArg
            (Region.mk (targetLocal + selection.val.explicitWires.length))
          rw [← targetItemsPresentation]
          change _ =
            (Region.adjoinAt source.checked.val.hiddenWires.length .nil
              (normalizedSite.conjoin copyRegion)).itemsCast
                normalizedTargetLocalEq
          let normalizedTargetItems :=
            Region.itemsCast_adjoinAt_nil_conjoin_zero
            (outer := source.checked.elaborate.externalClasses)
            (hostLocal := source.checked.val.hiddenWires.length)
            (addedLocal := selection.val.explicitWires.length)
            normalizedSite copyRegion normalizedSiteLocalEq
            copyRegionLocalEq normalizedTargetLocalEq
          have targetHostEmbeddingDef :
              Region.adjoinHostWire
                  source.checked.elaborate.externalClasses
                  source.checked.val.hiddenWires.length
                  selection.val.explicitWires.length =
                targetHostEmbedding := by
            rfl
          rw [targetHostEmbeddingDef] at normalizedTargetItems
          refine Eq.trans ?_ normalizedTargetItems.symm
          apply ItemSeq.append_congr
          · apply congrArg (ItemSeq.renameWires targetHostEmbedding)
            apply congrArg (fun localEq =>
              (Region.adjoinAt
                source.checked.val.hiddenWires.length .nil
                normalizedSite).itemsCast localEq)
            exact Subsingleton.elim _ _
          · rw [Region.itemsCast_eq_renameWires]
            dsimp only [copyRegion, FactorAssembly.materialTarget,
              FactorAssembly.selected]
            simp only [Region.adjoinAt, Region.renameWires,
              Region.renameRelations, Region.items, Region.localCount,
              ItemSeq.renameWires, ItemSeq.nil_append,
              ItemSeq.renameWires_comp]
            change ItemSeq.renameWires _ selectedItems =
              ItemSeq.renameWires _
                (ItemSeq.renameWires _
                  (ItemSeq.renameRelations _
                    (ItemSeq.renameWires _ selectedItems)))
            have relationDrop :
                ItemSeq.renameRelations
                    (fun {arity} => assembly.descendant.outerRelation)
                    (ItemSeq.renameWires (extendWireRenaming
                      assembly.copyWires.wire 0) selectedItems) =
                  ItemSeq.renameWires (extendWireRenaming
                    assembly.copyWires.wire 0) selectedItems := by
              simpa only using
                (ItemSeq.renameRelations_to_nil
                  (ItemSeq.renameWires (extendWireRenaming
                    assembly.copyWires.wire 0) selectedItems) rfl
                  (fun {arity} => assembly.descendant.outerRelation))
            refine Eq.trans ?_ (congrArg (fun items =>
              ItemSeq.renameWires
                (Region.adjoinMaterialWire
                  source.checked.elaborate.externalClasses
                  source.checked.val.hiddenWires.length
                  selection.val.explicitWires.length ∘ Fin.cast _)
                (ItemSeq.renameWires
                  (Region.adjoinMaterialWire
                    assembly.route_alignment.targetWitness.toFocus.holeWires
                    selection.val.explicitWires.length 0) items))
              relationDrop.symm)
            dsimp only
            rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
            apply congrArg (fun wireMap =>
              ItemSeq.renameWires wireMap selectedItems)
            funext index
            apply Fin.ext
            dsimp only [Function.comp_apply, targetMaterialMap,
              rootCopyWire]
            simp only [Region.adjoinMaterialWire_zero,
              extendWireRenaming_zero, id_eq]
            have sourceSelectedIndex :
                assembly.sourceSelectedEmbedding index = index := by
              apply Fin.ext
              rfl
            rw [sourceSelectedIndex]
            rfl
        let siteAssoc := RegionIso.conjoin_assoc
          assembly.selected
          retained copyRegion
        let siteSwap := RegionIso.conjoin_left assembly.selected
          (RegionIso.conjoin_comm
            retained copyRegion)
        let siteNormalizer := siteAssoc.trans siteSwap
        let targetNormalizer := RegionIso.adjoinAt_nil
          source.checked.val.hiddenWires.length siteNormalizer
        have descendantHole : assembly.descendant = .hole := by
          rfl
        have descendantFill
            (body : Region
              assembly.route_alignment.targetWitness.toFocus.holeWires
              assembly.route_alignment.targetWitness.toFocus.holeRels) :
            assembly.descendant.fill body = body := by
          exact (congrArg (fun context => context.fill body)
            descendantHole).trans rfl
        have targetBodyEq : rootAtStartTargetBody source selection
              anchorRoot assembly =
            Region.adjoinAt source.checked.val.hiddenWires.length .nil
              (assembly.selected.conjoin
                (copyRegion.conjoin
                  (assembly.descendant.fill assembly.remainder))) := by
          unfold rootAtStartTargetBody
          change Region.adjoinAt source.checked.val.hiddenWires.length .nil
              (assembly.selected.conjoin
                (assembly.descendant.fill
                  (copyRegion.conjoin assembly.remainder))) = _
          rw [descendantFill, descendantFill]
        let completed := compilerNormalized.trans
          (Eq.mp (congrArg (fun normalized => RegionIso
            (FiniteEquiv.refl
              (Fin source.checked.elaborate.externalClasses)) []
            normalized
            (Region.adjoinAt source.checked.val.hiddenWires.length .nil
              (assembly.selected.conjoin
                (copyRegion.conjoin
                  (assembly.descendant.fill assembly.remainder)))))
            normalizedBodyEq.symm) targetNormalizer)
        let completedRoot : RegionIso quotient.exposedWiresEquiv []
            (.mk (checkedCoalesced.val.hiddenWires.length +
              plugLayout.bodyInternalCarriers.length)
              ((hostPrepared.append patternPrepared).renameWires reindex))
            (rootAtStartTargetBody source selection anchorRoot assembly) :=
          Eq.mp (congrArg (fun target => RegionIso
            quotient.exposedWiresEquiv []
            (.mk (checkedCoalesced.val.hiddenWires.length +
              plugLayout.bodyInternalCarriers.length)
              ((hostPrepared.append patternPrepared).renameWires reindex))
            target) targetBodyEq.symm) completed
        simpa [checkedCoalesced, sourceOpen,
          sourceCompiler, Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern,
          Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
          Concrete.Splice.replaceOpenBody] using completedRoot

set_option maxHeartbeats 1200000 in
private noncomputable opaque rootAtStart_sourceNormalizer
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor))
    (assembly : @FactorAssembly source.diagram selection {} 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      (iterationInput source.diagram selection selection.val.anchor)
      fragment selection.val.anchor [] (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot))
    (admissible : (iterationInput source.diagram selection
      selection.val.anchor).Admissible)
    (siteRoot :
      (iterationInput source.diagram selection selection.val.anchor).site =
        (iterationInput source.diagram selection
          selection.val.anchor).frame.val.root)
    (coalescedArity :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput source.diagram selection selection.val.anchor)
        admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped).val.boundary.length =
          source.checked.val.boundary.length) :
    let spliceInput := iterationInput source.diagram selection
      selection.val.anchor
    let plugLayout := spliceInput.plugLayout
    let sourceCompiler :=
      Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern spliceInput
        plugLayout admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped siteRoot
        fragment.context fragment.contextExact fragment.binders
        fragment.enumeration fragment.items
    OpenDiagramIso (sourceCompiler.castArity coalescedArity)
      (source.checked.elaborate.withBody
        (rootAtStartTargetBody source selection anchorRoot assembly)) := by
  dsimp only
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let sourceCompiler :=
    Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern spliceInput
      plugLayout admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped siteRoot
      fragment.context fragment.contextExact fragment.binders
      fragment.enumeration fragment.items
  let quotient := coalescedOpenIso source.diagram selection
    selection.val.anchor source.checked.val.boundary
  let sourceOpen := Concrete.Splice.Input.PlugLayout.coalescedOpenRoot
    spliceInput source.checked.val.boundary
  let targetOpen : Concrete.OpenDiagram := {
    diagram := source.diagram.val
    boundary := source.checked.val.boundary
  }
  let sourceExternalEq :
      (sourceCompiler.castArity coalescedArity).externalClasses =
        sourceOpen.exposedWires.length := by
    simp [sourceCompiler, sourceOpen,
      Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern,
      Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
      Concrete.Splice.replaceOpenBody,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot]
  let targetExternalEq :
      (source.checked.elaborate.withBody
        (rootAtStartTargetBody source selection anchorRoot assembly)
      ).externalClasses = targetOpen.exposedWires.length := by
    rfl
  let external :=
    ((FiniteEquiv.finCast sourceExternalEq).trans
      quotient.exposedWiresEquiv).trans
        (FiniteEquiv.finCast targetExternalEq.symm)
  let bodyIso : RegionIso external []
      (sourceCompiler.castArity coalescedArity).body
      (rootAtStartTargetBody source selection anchorRoot assembly) :=
    rootAtStart_bodyIso source selection anchorRoot fragment assembly
      admissible siteRoot coalescedArity
  let normalizer : OpenDiagramIso
      (sourceCompiler.castArity coalescedArity)
      (source.checked.elaborate.withBody
        (rootAtStartTargetBody source selection anchorRoot assembly)) := {
    external := external
    boundary := by
      intro position
      let coalescedPosition := Fin.cast coalescedArity.symm position
      have commute := quotient.boundaryClass_commute coalescedPosition
      have sourceBoundary :
          (FiniteEquiv.finCast sourceExternalEq)
              ((sourceCompiler.castArity coalescedArity).boundary position) =
            sourceOpen.boundaryClass coalescedPosition := by
        change Fin.cast sourceExternalEq
            ((sourceCompiler.castArity coalescedArity).boundary position) =
          sourceOpen.boundaryClass coalescedPosition
        calc
          _ = Fin.cast
              (OpenDiagram.castArity_externalClasses sourceCompiler
                coalescedArity)
              ((sourceCompiler.castArity coalescedArity).boundary
                position) := by
            apply Fin.ext
            rfl
          _ = sourceCompiler.boundary coalescedPosition :=
            OpenDiagram.castArity_boundary_cast sourceCompiler
              coalescedArity position
          _ = sourceOpen.boundaryClass coalescedPosition := by
            simp [sourceCompiler, sourceOpen,
              Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern,
              Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
              Concrete.Splice.replaceOpenBody,
              Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot]
      have targetBoundary :
          (FiniteEquiv.finCast targetExternalEq.symm)
              (targetOpen.boundaryClass
                (Fin.cast quotient.boundary_length_eq coalescedPosition)) =
            (source.checked.elaborate.withBody
              (rootAtStartTargetBody source selection anchorRoot assembly)
            ).boundary position := by
        apply Fin.ext
        rfl
      change (FiniteEquiv.finCast targetExternalEq.symm)
          (quotient.exposedWiresEquiv
            ((FiniteEquiv.finCast sourceExternalEq)
              ((sourceCompiler.castArity coalescedArity).boundary
                position))) = _
      rw [sourceBoundary, commute, targetBoundary]
    body := bodyIso
  }
  exact normalizer

private noncomputable opaque rootAtStart_outputCompilerIso
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    {result : Concrete.Checked}
    (success :
      (iterationInput source.diagram selection selection.val.anchor
        ).spliceChecked = .ok result)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor)) :
    let spliceInput := iterationInput source.diagram selection
      selection.val.anchor
    let plugLayout := spliceInput.plugLayout
    let admissible := (Concrete.Splice.Input.spliceChecked_sound success).2.1
    let siteRoot : spliceInput.site = spliceInput.frame.val.root := by
      simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using
        anchorRoot
    let output := Concrete.Splice.Input.spliceCheckedResultOpen
      spliceInput success source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
    let outputArityEq : output.val.boundary.length =
        source.checked.val.boundary.length := by
      dsimp only [output,
        Concrete.Splice.Input.spliceCheckedResultOpen,
        Concrete.Splice.Input.spliceCheckedResultOpenRaw,
        Concrete.Splice.Input.PlugLayout.outputOpenRoot]
      simp only [List.length_map]
      rfl
    let coalesced :=
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
        admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped
    let coalescedArity : coalesced.val.boundary.length =
        source.checked.val.boundary.length := by
      simp [coalesced,
        Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
        Concrete.Splice.Input.PlugLayout.coalescedOpenRoot]
      rfl
    let sourceCompiler :=
      Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern spliceInput
        plugLayout admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped siteRoot
        fragment.context fragment.contextExact fragment.binders
        fragment.enumeration fragment.items
    OpenDiagramIso (output.elaborate.castArity outputArityEq)
      (sourceCompiler.castArity coalescedArity) := by
  dsimp only
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let plugLayout := spliceInput.plugLayout
  let admissible := (Concrete.Splice.Input.spliceChecked_sound success).2.1
  let siteRoot : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using
      anchorRoot
  have outputEq :=
    Concrete.Splice.Input.spliceCheckedResultOpen_eq_checkedOutputOpenRoot
      spliceInput success source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let compilerIso :=
    Concrete.Splice.Input.compiledSpliceRootIsoOfExactPattern spliceInput
      plugLayout admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped siteRoot fragment.fuel
      fragment.context fragment.contextExact fragment.binders
      fragment.enumeration fragment.items fragment.computation
  let actualOutput := Concrete.Splice.Input.spliceCheckedResultOpen
    spliceInput success source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped
  let checkedOutput := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    spliceInput plugLayout admissible source.checked.val.boundary
    source.checked.property.boundary_is_root_scoped
  let actualArity : actualOutput.val.boundary.length =
      source.checked.val.boundary.length := by
    simp [actualOutput, Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw, spliceInput,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
    rfl
  let checkedArity : checkedOutput.val.boundary.length =
      source.checked.val.boundary.length := by
    simp [checkedOutput, Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
    rfl
  have castEq := checkedOpenElaborateCast_eq outputEq actualArity checkedArity
  let outputCastIso : OpenDiagramIso
      (actualOutput.elaborate.castArity actualArity)
      (checkedOutput.elaborate.castArity checkedArity) :=
    OpenDiagramIso.ofEq castEq
  let coalesced :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
      admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let coalescedArity : coalesced.val.boundary.length =
      source.checked.val.boundary.length := by
    simp [coalesced,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot]
    rfl
  let compilerOutputArity : checkedOutput.val.boundary.length =
      coalesced.val.boundary.length := by
    simp [checkedOutput, coalesced,
      Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot]
  let compilerReverseCast :=
    OpenDiagramIso.castArity coalescedArity compilerIso.symm
  have compilerReverse : OpenDiagramIso
      (checkedOutput.elaborate.castArity checkedArity)
      ((Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern
        spliceInput plugLayout admissible source.checked.val.boundary
        source.checked.property.boundary_is_root_scoped siteRoot
        fragment.context fragment.contextExact fragment.binders
        fragment.enumeration fragment.items).castArity coalescedArity) := by
    rw [show checkedOutput.elaborate.castArity checkedArity =
        (checkedOutput.elaborate.castArity compilerOutputArity).castArity
          coalescedArity by
      rw [OpenDiagram.castArity_trans]
      ]
    simpa only [checkedOutput] using compilerReverseCast
  exact outputCastIso.trans compilerReverse

/-- Successful root iteration output is isomorphic to the exact Base target,
using one selected fragment compiler package and its matching factor assembly. -/
noncomputable def rootAtStart_targetIso
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    {result : Concrete.Checked}
    (success :
      (iterationInput source.diagram selection selection.val.anchor
        ).spliceChecked = .ok result)
    (fragment : FragmentInput source.diagram selection
      ({} : FragmentLayout source.diagram.val selection)
      (iterationInput source.diagram selection selection.val.anchor))
    (assembly : @FactorAssembly source.diagram selection {} 0 []
      (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)
      (rootLeaf source selection anchorRoot)
      (iterationInput source.diagram selection selection.val.anchor)
      fragment selection.val.anchor [] (.here selection.val.anchor)
      (rootSourcePartition source selection anchorRoot)) :
    let output := Concrete.Splice.Input.spliceCheckedResultOpen
      (iterationInput source.diagram selection selection.val.anchor)
      success source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
    let outputArityEq : output.val.boundary.length =
        source.checked.val.boundary.length := by
      dsimp only [output,
        Concrete.Splice.Input.spliceCheckedResultOpen,
        Concrete.Splice.Input.spliceCheckedResultOpenRaw,
        Concrete.Splice.Input.PlugLayout.outputOpenRoot]
      simp only [List.length_map]
      rfl
    OpenDiagramIso
      (output.elaborate.castArity outputArityEq)
      (source.checked.elaborate.withBody
        (rootAtStartTargetBody source selection anchorRoot assembly)) := by
  dsimp only
  let admissible :=
    (Concrete.Splice.Input.spliceChecked_sound success).2.1
  let spliceInput := iterationInput source.diagram selection
    selection.val.anchor
  let siteRoot : spliceInput.site = spliceInput.frame.val.root := by
    simpa [spliceInput, Concrete.Splice.Input.coalesceFrameRaw] using
      anchorRoot
  let coalesced :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot spliceInput
      admissible source.checked.val.boundary
      source.checked.property.boundary_is_root_scoped
  let coalescedArity : coalesced.val.boundary.length =
      source.checked.val.boundary.length := by
    simp [coalesced,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot]
    rfl
  let compilerPrefix := rootAtStart_outputCompilerIso source selection
    anchorRoot success fragment
  let normalizer := rootAtStart_sourceNormalizer source selection anchorRoot
    fragment assembly admissible siteRoot coalescedArity
  exact compilerPrefix.trans normalizer

end VisualProof.Refinement.Implementation.IterationRootTarget
