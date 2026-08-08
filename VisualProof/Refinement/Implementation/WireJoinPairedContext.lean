import VisualProof.Refinement.Implementation.WireJoinAway
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Refinement.Implementation.WireJoinPairedContext

open VisualProof
open VisualProof.Rule
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireJoin

theorem localRename
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (step : Rule.WireSever.Local before after) :
    Rule.WireSever.Local (before.renameWires wire)
      (after.renameWires wire) := by
  cases step with
  | @sever _ localWires rels joined separate =>
      let localIso := FiniteEquiv.refl (Fin localWires)
      let extended := extendWireEquiv wire localIso
      let joined' := extended joined
      let separate' := separate.renameWires
        (extendWireEquiv wire (FiniteEquiv.refl (Fin (localWires + 1))))
      have collapseCommutes :
          extendWireRenaming wire.toFun localWires ∘
              Rule.WireSever.collapseLocal sourceWires localWires joined =
            Rule.WireSever.collapseLocal targetWires localWires joined' ∘
              extendWireRenaming wire.toFun (localWires + 1) := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
        · have sourceCollapse : Rule.WireSever.collapseLocal sourceWires
              localWires joined (Fin.castAdd (localWires + 1) inherited) =
            Fin.castAdd localWires inherited := by
            have old : inherited.val < sourceWires + localWires := by omega
            have old' : (Fin.castAdd (localWires + 1) inherited).val <
                sourceWires + localWires := by simpa using old
            unfold Rule.WireSever.collapseLocal
            rw [dif_pos old']
            rfl
          have targetCollapse : Rule.WireSever.collapseLocal targetWires
              localWires joined'
                (Fin.castAdd (localWires + 1) (wire inherited)) =
            Fin.castAdd localWires (wire inherited) := by
            have old : (wire inherited).val <
                targetWires + localWires := by omega
            have old' :
                (Fin.castAdd (localWires + 1) (wire inherited)).val <
                  targetWires + localWires := by simpa using old
            unfold Rule.WireSever.collapseLocal
            rw [dif_pos old']
            rfl
          simp only [Function.comp_apply]
          have mappedInput : extendWireRenaming wire.toFun (localWires + 1)
                (Fin.castAdd (localWires + 1) inherited) =
              Fin.castAdd (localWires + 1) (wire inherited) := by
            simp [extendWireRenaming]
          rw [mappedInput]
          change extendWireRenaming wire.toFun localWires
              (Rule.WireSever.collapseLocal sourceWires localWires joined
                (Fin.castAdd (localWires + 1) inherited)) =
            Rule.WireSever.collapseLocal targetWires localWires joined'
              (Fin.castAdd (localWires + 1) (wire inherited))
          rw [sourceCollapse, targetCollapse]
          simp [extendWireRenaming]
        · refine Fin.lastCases ?_ (fun oldLocal => ?_) localIndex
          · have sourceCollapse : Rule.WireSever.collapseLocal sourceWires
                localWires joined
                  (Fin.natAdd sourceWires (Fin.last localWires)) = joined := by
              apply Fin.ext
              simp [Rule.WireSever.collapseLocal]
            have targetCollapse : Rule.WireSever.collapseLocal targetWires
                localWires joined'
                  (Fin.natAdd targetWires (Fin.last localWires)) = joined' := by
              apply Fin.ext
              simp [Rule.WireSever.collapseLocal]
            simp only [Function.comp_apply]
            have mappedInput : extendWireRenaming wire.toFun (localWires + 1)
                  (Fin.natAdd sourceWires (Fin.last localWires)) =
                Fin.natAdd targetWires (Fin.last localWires) := by
              unfold extendWireRenaming
              exact Fin.addCases_right _
            rw [mappedInput]
            change extendWireRenaming wire.toFun localWires
                (Rule.WireSever.collapseLocal sourceWires localWires joined
                  (Fin.natAdd sourceWires (Fin.last localWires))) =
              Rule.WireSever.collapseLocal targetWires localWires joined'
                (Fin.natAdd targetWires (Fin.last localWires))
            rw [sourceCollapse, targetCollapse]
            change extendWireRenaming wire.toFun localWires joined =
              extendWireRenaming wire.toFun localWires joined
            rfl
          · have sourceCollapse : Rule.WireSever.collapseLocal sourceWires
                localWires joined
                  (Fin.natAdd sourceWires (Fin.castSucc oldLocal)) =
              Fin.natAdd sourceWires oldLocal := by
              apply Fin.ext
              simp [Rule.WireSever.collapseLocal]
            have targetCollapse : Rule.WireSever.collapseLocal targetWires
                localWires joined'
                  (Fin.natAdd targetWires (Fin.castSucc oldLocal)) =
              Fin.natAdd targetWires oldLocal := by
              apply Fin.ext
              simp [Rule.WireSever.collapseLocal]
            simp only [Function.comp_apply]
            have mappedInput : extendWireRenaming wire.toFun (localWires + 1)
                  (Fin.natAdd sourceWires (Fin.castSucc oldLocal)) =
                Fin.natAdd targetWires (Fin.castSucc oldLocal) := by
              apply Fin.ext
              simp [extendWireRenaming]
            rw [mappedInput]
            change extendWireRenaming wire.toFun localWires
                (Rule.WireSever.collapseLocal sourceWires localWires joined
                  (Fin.natAdd sourceWires (Fin.castSucc oldLocal))) =
              Rule.WireSever.collapseLocal targetWires localWires joined'
                (Fin.natAdd targetWires (Fin.castSucc oldLocal))
            rw [sourceCollapse, targetCollapse]
            simp [extendWireRenaming]
      have extendEq : extendWireRenaming wire.toFun (localWires + 1) =
          (extendWireEquiv wire
            (FiniteEquiv.refl (Fin (localWires + 1)))).toFun := by
        funext index
        refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
        · rfl
        · rfl
      rw [extendEq] at collapseCommutes
      have beforeEq :
          (Region.mk localWires
              (separate.renameWires
                (Rule.WireSever.collapseLocal sourceWires localWires joined))).renameWires
              wire =
            Region.mk localWires
              (separate'.renameWires
                (Rule.WireSever.collapseLocal targetWires localWires
                  joined')) := by
        simp only [Region.renameWires, separate', ItemSeq.renameWires_comp]
        rw [collapseCommutes]
      have afterEq :
          (Region.mk (localWires + 1) separate).renameWires wire =
            Region.mk (localWires + 1) separate' := by
        rfl
      rw [beforeEq, afterEq]
      exact .sever joined' separate'

def contextWitnessCast
    {input : Concrete.Diagram}
    {outer inner : Fin input.wireCount}
    {distinct : outer ≠ inner}
    {sourceContext sourceContext' : Concrete.Elaboration.WireContext input}
    {targetContext targetContext' : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)}
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceEq : sourceContext' = sourceContext)
    (targetEq : targetContext' = targetContext) :
    VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext' targetContext' := by
  subst sourceContext
  subst targetContext
  exact witness

theorem contextWitnessCast_indexMap
    {input : Concrete.Diagram}
    {outer inner : Fin input.wireCount}
    {distinct : outer ≠ inner}
    {sourceContext sourceContext' : Concrete.Elaboration.WireContext input}
    {targetContext targetContext' : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)}
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceEq : sourceContext' = sourceContext)
    (targetEq : targetContext' = targetContext)
    (index : Fin sourceContext'.length) :
    (contextWitnessCast witness sourceEq targetEq).indexMap index =
      Fin.cast (congrArg List.length targetEq).symm
        (witness.indexMap
          (Fin.cast (congrArg List.length sourceEq) index)) := by
  subst sourceContext
  subst targetContext
  rfl

noncomputable def compilerRawFrame
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    {region child : Fin input.regionCount}
    {rest : List Nat}
    (regionNe : region ≠ (input.wires inner).scope)
    (childParent : (input.regions child).parent? = some region)
    (position : Fin (Concrete.Elaboration.localOccurrences input region).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input region) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute input child
      (input.wires inner).scope rest)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {rels : Theory.RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) rels}
    {targetItems : ItemSeq (targetOuter + targetLocal) rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region
      (.here (.mk targetLocal targetItems)))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceState.inheritedWires targetState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel)
    (extendedEquiv : FiniteEquiv
      (Fin (sourceState.inheritedWires.extend region).length)
      (Fin (targetState.inheritedWires.extend region).length))
    (extendedApply : ∀ index, extendedEquiv index =
      (witness.extend inputWellFormed ordered region sourceState.wiresExact
        targetState.wiresExact).indexMap index)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndex : Fin targetState.items.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    ItemSeqIso.Frame extendedEquiv sourceIndex targetIndex := by
  let sourceExtended := sourceState.inheritedWires.extend region
  let targetExtended := targetState.inheritedWires.extend region
  let extendedWitness := witness.extend inputWellFormed ordered region
    sourceState.wiresExact targetState.wiresExact
  let occurrences := Concrete.Elaboration.localOccurrences input region
  have targetComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (Concrete.Elaboration.compileRegion?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetState.fuel)
        targetExtended targetState.binders occurrences =
          some targetState.items := by
    simpa [targetExtended, occurrences] using targetState.itemsComputation
  have sourceComputation :
      Concrete.Elaboration.compileOccurrencesWith? input
        (Concrete.Elaboration.compileRegion? input sourceState.fuel)
        sourceExtended sourceState.binders occurrences =
          some sourceState.items := by
    simpa [sourceExtended, occurrences] using sourceState.itemsComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input sourceState.fuel)
    sourceExtended sourceState.binders sourceComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetState.fuel)
    targetExtended targetState.binders targetComputation
  let positions : FiniteEquiv (Fin sourceState.items.length)
      (Fin targetState.items.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      (FiniteEquiv.finCast targetLength.symm)
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    simp [positions, sourceIndexVal, targetIndexVal, FiniteEquiv.finCast]
  refine {
    positions := positions
    mapped := mapped
    siblings := ?_
  }
  intro index indexNe
  let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
  have occurrenceNe : occurrenceIndex ≠ position := by
    intro equality
    apply indexNe
    apply Fin.ext
    have values := congrArg Fin.val equality
    simpa [occurrenceIndex, sourceIndexVal] using values
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input sourceState.fuel)
    sourceExtended sourceState.binders sourceComputation occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetState.fuel)
    targetExtended targetState.binders targetComputation occurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm occurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [sourcePosition] at sourceGet
  rw [targetPosition] at targetGet
  let occurrence := occurrences.get occurrenceIndex
  have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
  change Concrete.Elaboration.compileOccurrenceWith? input
      (Concrete.Elaboration.compileRegion? input sourceState.fuel)
      sourceExtended sourceState.binders occurrence =
        some (sourceState.items.get index) at sourceGet
  change Concrete.Elaboration.compileOccurrenceWith?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (Concrete.Elaboration.compileRegion?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetState.fuel)
      targetExtended targetState.binders occurrence =
        some (targetState.items.get (positions index)) at targetGet
  have regionEnclosesSite : input.Encloses region
      (input.wires inner).scope :=
    Concrete.Elaboration.checked_encloses_trans inputWellFormed
      (by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        simp [Concrete.Diagram.climb, childParent])
      (Concrete.Splice.Input.RegionRoute.encloses tail inputWellFormed)
  have siteNotEnclosesRegion :
      ¬ input.Encloses (input.wires inner).scope region := by
    intro reverse
    exact regionNe (Concrete.Elaboration.checked_encloses_antisymm
      inputWellFormed regionEnclosesSite reverse)
  have siblingGeometry : ∀ sibling, occurrence = .child sibling →
      sibling ≠ child ∧
      ¬ input.Encloses (input.wires inner).scope sibling ∧
      ¬ input.Encloses sibling (input.wires inner).scope := by
    intro sibling siblingEq
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child input region
        sibling).1 (by
          rw [← siblingEq]
          exact occurrenceMem)
    have siblingNe : sibling ≠ child := by
      intro equality
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup input region)
        occurrenceIndex
      have same : some occurrenceIndex = some position := by
        rw [← found, ← positionEq]
        congr 1
      exact occurrenceNe (Option.some.inj same)
    have notAbove : ¬ input.Encloses sibling
        (input.wires inner).scope :=
      Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
        inputWellFormed tail childParent siblingParent siblingNe
    have notBelow : ¬ input.Encloses
        (input.wires inner).scope sibling := by
      intro siteSibling
      have childSite := Concrete.Splice.Input.RegionRoute.encloses tail
        inputWellFormed
      have childSibling := Concrete.Elaboration.checked_encloses_trans
        inputWellFormed childSite siteSibling
      rcases Concrete.Elaboration.encloses_direct_child siblingParent
          childSibling with equality | cycle
      · exact siblingNe equality.symm
      · exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          inputWellFormed childParent cycle
    exact ⟨siblingNe, notBelow, notAbove⟩
  cases occurrenceEq : occurrence with
  | node node =>
      rw [occurrenceEq] at sourceGet targetGet
      simp only [Concrete.Elaboration.compileOccurrenceWith?]
        at sourceGet targetGet
      have nodeRegion : (input.nodes node).region = region :=
        (Concrete.Elaboration.mem_localOccurrences_node input region node).1
          (by rw [← occurrenceEq]; exact occurrenceMem)
      have nodeMap := compileNode_map_away input inputWellFormed outer inner
        distinct ordered targetWellFormed region siteNotEnclosesRegion
        sourceExtended targetExtended extendedWitness sourceState.wiresExact
        targetState.wiresExact sourceState.binders node nodeRegion
      rw [sourceGet] at nodeMap
      have nodeMapTarget : Concrete.Elaboration.compileNode?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetExtended
          targetState.binders node =
            some ((sourceState.items.get index).renameWires
              extendedWitness.indexMap) := by
        rw [bindersEq]
        simpa only [Option.map_some] using nodeMap
      have nodeMap' : some (targetState.items.get (positions index)) =
          some ((sourceState.items.get index).renameWires
            extendedWitness.indexMap) := by
        exact targetGet.symm.trans nodeMapTarget
      have itemEqWitness : targetState.items.get (positions index) =
          (sourceState.items.get index).renameWires
            extendedWitness.indexMap := Option.some.inj nodeMap'
      have renameEq :
          (sourceState.items.get index).renameWires
              extendedWitness.indexMap =
            (sourceState.items.get index).renameWires extendedEquiv := by
        apply congrArg (fun map =>
          (sourceState.items.get index).renameWires map)
        funext wireIndex
        exact (extendedApply wireIndex).symm
      have itemEq : targetState.items.get (positions index) =
          (sourceState.items.get index).renameWires extendedEquiv := by
        exact itemEqWitness.trans renameEq
      exact itemEq.symm ▸ ItemIso.renameWiresEquiv _ extendedEquiv
  | child sibling =>
      rw [occurrenceEq] at sourceGet targetGet
      obtain ⟨siblingNe, notBelow, notAbove⟩ :=
        siblingGeometry sibling occurrenceEq
      have siblingParent :=
        (Concrete.Elaboration.mem_localOccurrences_child input region
          sibling).1 (by rw [← occurrenceEq]; exact occurrenceMem)
      have targetSiblingParent :
          ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).regions sibling).parent? =
            some region := by
        simpa using siblingParent
      have sourceChildExact := sourceState.wiresExact.extend_child
        inputWellFormed siblingParent
      have targetChildExact := targetState.wiresExact.extend_child
        targetWellFormed targetSiblingParent
      have siblingNotSite : sibling ≠ (input.wires inner).scope := by
        intro equality
        subst sibling
        exact notBelow (Concrete.Diagram.Encloses.refl input _)
      cases siblingKind : input.regions sibling with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, siblingKind]
            at sourceGet
      | cut parent =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
            VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
          cases sourceResultEq : Concrete.Elaboration.compileRegion? input
              sourceState.fuel sibling sourceExtended sourceState.binders with
          | none => simp [sourceResultEq] at sourceGet
          | some sourceBody =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  targetState.fuel sibling targetExtended
                  targetState.binders with
              | none => simp [targetResultEq] at targetGet
              | some targetBody =>
                  rw [sourceResultEq] at sourceGet
                  rw [targetResultEq] at targetGet
                  have sourceItemEq : sourceState.items.get index =
                      .cut sourceBody := Option.some.inj sourceGet |>.symm
                  have targetItemEq : targetState.items.get (positions index) =
                      .cut targetBody := Option.some.inj targetGet |>.symm
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      sourceState.fuel sibling targetExtended
                      sourceState.binders = some targetBody := by
                    simpa [fuelEq, bindersEq] using targetResultEq
                  have recursive := compileRegion_away input inputWellFormed
                    outer inner distinct ordered targetWellFormed sourceState.fuel
                    sibling siblingNotSite notBelow notAbove sourceExtended
                    targetExtended extendedWitness sourceChildExact
                    targetChildExact sourceState.binders sourceResultEq
                    targetResultEq'
                  have recursive' : RegionIso extendedEquiv rels sourceBody
                      targetBody := by
                    have renamed := RegionIso.renameWiresEquiv sourceBody
                      extendedEquiv
                    have aligned : sourceBody.renameWires extendedEquiv =
                        sourceBody.renameWires extendedWitness.indexMap := by
                      apply congrArg (fun map => Region.renameWires map sourceBody)
                      funext wireIndex
                      exact extendedApply wireIndex
                    exact renamed.trans (aligned ▸ recursive)
                  exact sourceItemEq.symm ▸ targetItemEq.symm ▸
                    ItemIso.cut recursive'
      | bubble parent arity =>
          simp only [Concrete.Elaboration.compileOccurrenceWith?, siblingKind,
            VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
          let pushed := sourceState.binders.push sibling arity
          cases sourceResultEq : Concrete.Elaboration.compileRegion? input
              sourceState.fuel sibling sourceExtended pushed with
          | none => simp [pushed, sourceResultEq] at sourceGet
          | some sourceBody =>
              cases targetResultEq : Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  targetState.fuel sibling targetExtended
                  (targetState.binders.push sibling arity) with
              | none => simp [targetResultEq] at targetGet
              | some targetBody =>
                  change (Concrete.Elaboration.compileRegion? input
                    sourceState.fuel sibling sourceExtended pushed).bind _ =
                      some (sourceState.items.get index) at sourceGet
                  rw [sourceResultEq] at sourceGet
                  rw [targetResultEq] at targetGet
                  have sourceItemEq : sourceState.items.get index =
                      .bubble arity sourceBody :=
                    Option.some.inj sourceGet |>.symm
                  have targetItemEq : targetState.items.get (positions index) =
                      .bubble arity targetBody :=
                    Option.some.inj targetGet |>.symm
                  have pushedEq : targetState.binders.push sibling arity =
                      pushed := by
                    simpa [pushed] using congrArg
                      (fun binders => binders.push sibling arity) bindersEq
                  have targetResultEq' : Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      sourceState.fuel sibling targetExtended pushed =
                        some targetBody := by
                    simpa [fuelEq, pushedEq] using targetResultEq
                  have recursive := compileRegion_away input inputWellFormed
                    outer inner distinct ordered targetWellFormed sourceState.fuel
                    sibling siblingNotSite notBelow notAbove sourceExtended
                    targetExtended extendedWitness sourceChildExact
                    targetChildExact pushed sourceResultEq targetResultEq'
                  have recursive' : RegionIso extendedEquiv (arity :: rels)
                      sourceBody targetBody := by
                    have renamed := RegionIso.renameWiresEquiv sourceBody
                      extendedEquiv
                    have aligned : sourceBody.renameWires extendedEquiv =
                        sourceBody.renameWires extendedWitness.indexMap := by
                      apply congrArg (fun map => Region.renameWires map sourceBody)
                      funext wireIndex
                      exact extendedApply wireIndex
                    exact renamed.trans (aligned ▸ recursive)
                  exact sourceItemEq.symm ▸ targetItemEq.symm ▸
                    ItemIso.bubble recursive'

theorem inner_absent_of_enclosing_route
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (inner : Fin input.wireCount)
    {region child : Fin input.regionCount}
    {rest : List Nat}
    (regionNe : region ≠ (input.wires inner).scope)
    (childParent : (input.regions child).parent? = some region)
    (tail : Concrete.Splice.RegionRoute input child
      (input.wires inner).scope rest)
    {outer : Nat} {rels : RelCtx} {body : Region outer rels}
    (state : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here body)) :
    inner ∉ state.inheritedWires.extend region := by
  intro member
  have reverse := (state.wiresExact.mem_iff inner).1 member
  have forward : input.Encloses region (input.wires inner).scope :=
    Concrete.Elaboration.checked_encloses_trans inputWellFormed
      (by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        simp [Concrete.Diagram.climb, childParent])
      (Concrete.Splice.Input.RegionRoute.encloses tail inputWellFormed)
  exact regionNe (Concrete.Elaboration.checked_encloses_antisymm
    inputWellFormed forward reverse)

noncomputable def compilerLeafFrame
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    {region child : Fin input.regionCount}
    {rest : List Nat}
    (regionNe : region ≠ (input.wires inner).scope)
    (childParent : (input.regions child).parent? = some region)
    (position : Fin (Concrete.Elaboration.localOccurrences input region).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input region) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute input child
      (input.wires inner).scope rest)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {rels : Theory.RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) rels}
    {targetItems : ItemSeq (targetOuter + targetLocal) rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region
      (.here (.mk targetLocal targetItems)))
    (sourceLocalCanonical : sourceLocal =
      (Concrete.Elaboration.exactScopeWires input region).length)
    (targetLocalCanonical : targetLocal =
      (Concrete.Elaboration.exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length)
    (sourceItemsCanonical : HEq sourceItems sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetItems targetState.canonicalBodyItems)
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceState.inheritedWires targetState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel)
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    let inherited := contextEquiv witness
      (by
        have nodup := sourceState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend,
          List.nodup_append] at nodup
        exact nodup.1)
      (by
        intro member
        exact inner_absent_of_enclosing_route input inputWellFormed inner
          regionNe childParent tail sourceState
          (List.mem_append_left _ member))
    let outerWire := Concrete.Splice.Input.compilerBodyOuterWire
      sourceState targetState inherited
    let localWire :=
      (FiniteEquiv.finCast sourceLocalCanonical).trans
        ((localEquiv input outer inner distinct region regionNe).trans
          (FiniteEquiv.finCast targetLocalCanonical.symm))
    ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex := by
  dsimp only
  subst sourceLocal
  subst targetLocal
  have sourceInheritedNodup : sourceState.inheritedWires.Nodup := by
    have nodup := sourceState.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have sourceInheritedAbsent : inner ∉ sourceState.inheritedWires := by
    intro member
    exact inner_absent_of_enclosing_route input inputWellFormed inner regionNe
      childParent tail sourceState (List.mem_append_left _ member)
  let inherited := contextEquiv witness sourceInheritedNodup
    sourceInheritedAbsent
  let outerWire := Concrete.Splice.Input.compilerBodyOuterWire sourceState
    targetState inherited
  let sourceExtended := sourceState.inheritedWires.extend region
  let targetExtended := targetState.inheritedWires.extend region
  let extendedWitness := witness.extend inputWellFormed ordered region
    sourceState.wiresExact targetState.wiresExact
  have sourceExtendedAbsent : inner ∉ sourceExtended :=
    inner_absent_of_enclosing_route input inputWellFormed inner regionNe
      childParent tail sourceState
  let extendedEquiv := contextEquiv extendedWitness
    sourceState.wiresExact.nodup sourceExtendedAbsent
  have extendedEquivEq : extendedEquiv =
      (FiniteEquiv.finCast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region)).trans
        ((extendWireEquiv inherited
          (localEquiv input outer inner distinct region regionNe)).trans
          (FiniteEquiv.finCast
            (Concrete.Elaboration.WireContext.length_extend
              targetState.inheritedWires region)).symm) := by
    apply FiniteEquiv.ext
    intro index
    let split := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend
        sourceState.inheritedWires region) index
    have recover : Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm split = index := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun inheritedIndex => ?_) (fun localIndex => ?_) split
    · apply Fin.ext
      have mapped := witness.extend_index_inherited inputWellFormed ordered
        region sourceState.wiresExact targetState.wiresExact inheritedIndex
      simpa [extendedEquiv, inherited, contextEquiv, extendWireEquiv,
        FiniteEquiv.finCast, split] using congrArg Fin.val mapped
    · apply Fin.ext
      have mapped := witness.extend_index_local_of_ne inputWellFormed ordered
        region regionNe sourceState.wiresExact targetState.wiresExact localIndex
      simpa [extendedEquiv, inherited, contextEquiv, localEquiv,
        extendWireEquiv, FiniteEquiv.finCast, split] using
          congrArg Fin.val mapped
  let localWire := localEquiv input outer inner distinct region regionNe
  let sourceCast : FiniteEquiv (Fin sourceExtended.length)
      (Fin (sourceOuter +
        (Concrete.Elaboration.exactScopeWires input region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires input region).length)
        sourceState.inheritedLength))
  let targetCast : FiniteEquiv (Fin targetExtended.length)
      (Fin (targetOuter + (Concrete.Elaboration.exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires
            (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length)
        targetState.inheritedLength))
  have sourceCanonicalEq : sourceItems =
      sourceState.items.renameWires sourceCast := by
    have core := eq_of_heq sourceItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp sourceState.items _ _).trans (by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      rfl))
  have targetCanonicalEq : targetItems =
      targetState.items.renameWires targetCast := by
    have core := eq_of_heq targetItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp targetState.items _ _).trans (by
      apply congrArg (targetState.items.renameWires ·)
      funext index
      rfl))
  let sourceRenamedIndex : Fin
      (sourceState.items.renameWires sourceCast).length :=
    Fin.cast (congrArg ItemSeq.length sourceCanonicalEq) sourceIndex
  let targetRenamedIndex : Fin
      (targetState.items.renameWires targetCast).length :=
    Fin.cast (congrArg ItemSeq.length targetCanonicalEq) targetIndex
  let rawSourceIndex :=
    (sourceState.items.renameWiresPositionEquiv sourceCast).symm
      sourceRenamedIndex
  let rawTargetIndex :=
    (targetState.items.renameWiresPositionEquiv targetCast).symm
      targetRenamedIndex
  have rawSourceVal : rawSourceIndex.val = position.val := by
    simpa [rawSourceIndex, sourceRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using sourceIndexVal
  have rawTargetVal : rawTargetIndex.val = position.val := by
    simpa [rawTargetIndex, targetRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using targetIndexVal
  let rawFrame := compilerRawFrame input inputWellFormed outer inner
    distinct ordered targetWellFormed regionNe childParent position positionEq
    tail sourceState targetState witness bindersEq fuelEq extendedEquiv
    (fun index => rfl) rawSourceIndex rawTargetIndex rawSourceVal rawTargetVal
  have sourceUndo : sourceItems.renameWires sourceCast.symm =
      sourceState.items := by
    calc
      sourceItems.renameWires sourceCast.symm =
          (sourceState.items.renameWires sourceCast).renameWires
            sourceCast.symm := congrArg
              (fun items => items.renameWires sourceCast.symm) sourceCanonicalEq
      _ = sourceState.items.renameWires
          (sourceCast.symm.toFun ∘ sourceCast.toFun) :=
        ItemSeq.renameWires_comp sourceState.items sourceCast sourceCast.symm
      _ = sourceState.items := by
        have identity : sourceCast.symm.toFun ∘ sourceCast.toFun = id := by
          funext index
          exact sourceCast.left_inv index
        rw [identity]
        exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires targetCast = targetItems :=
    targetCanonicalEq.symm
  let finalWire := extendWireEquiv outerWire localWire
  have wireFactor :
      (sourceCast.symm.trans extendedEquiv).trans targetCast = finalWire := by
    have extendedEq : extendedEquiv =
        (FiniteEquiv.finCast
          (Concrete.Elaboration.WireContext.length_extend
            sourceState.inheritedWires region)).trans
          ((extendWireEquiv inherited localWire).trans
            (FiniteEquiv.finCast
              (Concrete.Elaboration.WireContext.length_extend
                targetState.inheritedWires region)).symm) := by
      apply FiniteEquiv.ext
      intro index
      let split := Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region) index
      have recover : Fin.cast
          (Concrete.Elaboration.WireContext.length_extend
            sourceState.inheritedWires region).symm split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun inheritedIndex => ?_)
        (fun localIndex => ?_) split
      · apply Fin.ext
        have mapped := witness.extend_index_inherited inputWellFormed ordered
          region sourceState.wiresExact targetState.wiresExact inheritedIndex
        simpa [extendedEquiv, inherited, contextEquiv, localWire,
          extendWireEquiv, FiniteEquiv.finCast, split, sourceExtended,
          targetExtended] using congrArg Fin.val mapped
      · apply Fin.ext
        have mapped := witness.extend_index_local_of_ne inputWellFormed ordered
          region regionNe sourceState.wiresExact targetState.wiresExact
          localIndex
        simpa [extendedEquiv, inherited, contextEquiv, localWire, localEquiv,
          extendWireEquiv, FiniteEquiv.finCast, split, sourceExtended,
          targetExtended] using congrArg Fin.val mapped
    have sourceChildExtended : sourceOuter +
          (Concrete.Elaboration.exactScopeWires input region).length =
        sourceExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires input region).length)
          sourceState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm
    have targetChildExtended : targetOuter +
          (Concrete.Elaboration.exactScopeWires
            (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length =
        targetExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires
              (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length)
          targetState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires region).symm
    have algebra :=
      Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
        sourceChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region)
        sourceState.inheritedLength
        (rfl : sourceOuter +
          (Concrete.Elaboration.exactScopeWires input region).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires input region).length = _)
        targetChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires region)
        targetState.inheritedLength
        (rfl : targetOuter +
          (Concrete.Elaboration.exactScopeWires
            (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length = _)
        inherited localWire
    simpa [sourceCast, targetCast, extendedEq, finalWire, outerWire,
      sourceExtended, targetExtended] using algebra
  obtain ⟨sourceIndex', targetIndex', sourceVal, targetVal, frame⟩ :=
    ItemSeqIso.Frame.pullPush sourceCast.symm extendedEquiv targetCast
      finalWire sourceUndo targetPush wireFactor rawFrame
  have sourceIndexEq : sourceIndex' = sourceIndex := by
    apply Fin.ext
    exact sourceVal.trans (by
      change rawSourceIndex.val = sourceIndex.val
      simp [rawSourceIndex, sourceRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  have targetIndexEq : targetIndex' = targetIndex := by
    apply Fin.ext
    exact targetVal.trans (by
      change rawTargetIndex.val = targetIndex.val
      simp [rawTargetIndex, targetRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  subst sourceIndex'
  subst targetIndex'
  simpa only [finalWire] using frame

theorem compilerLeafOuterFactor
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    {region : Fin input.regionCount}
    (regionNe : region ≠ (input.wires inner).scope)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat}
    {parentRels childRels : RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) parentRels}
    {targetItems : ItemSeq (targetOuter + targetLocal) parentRels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region
      (.here (.mk targetLocal targetItems)))
    (sourceLocalCanonical : sourceLocal =
      (Concrete.Elaboration.exactScopeWires input region).length)
    (targetLocalCanonical : targetLocal =
      (Concrete.Elaboration.exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region).length)
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceState.inheritedWires targetState.inheritedWires)
    (sourceInheritedNodup : sourceState.inheritedWires.Nodup)
    (sourceInheritedAbsent : inner ∉ sourceState.inheritedWires)
    {child : Fin input.regionCount}
    {sourceChildBody : Region (sourceOuter + sourceLocal) childRels}
    {targetChildBody : Region (targetOuter + targetLocal) childRels}
    (sourceChildState : Concrete.Splice.Region.ContextPath.CompilerLeaf input
      child (.here sourceChildBody))
    (targetChildState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) child
      (.here targetChildBody))
    (sourceInherited : sourceChildState.inheritedWires =
      sourceState.inheritedWires.extend region)
    (targetInherited : targetChildState.inheritedWires =
      targetState.inheritedWires.extend region) :
    let inherited := contextEquiv witness sourceInheritedNodup
      sourceInheritedAbsent
    let extendedWitness := witness.extend inputWellFormed ordered region
      sourceState.wiresExact targetState.wiresExact
    let childWitness := contextWitnessCast extendedWitness sourceInherited
      targetInherited
    let childNodup : sourceChildState.inheritedWires.Nodup := by
      rw [sourceInherited]
      exact sourceState.wiresExact.nodup
    let childAbsent : inner ∉ sourceChildState.inheritedWires := by
      rw [sourceInherited]
      intro member
      rw [Concrete.Elaboration.WireContext.extend, List.mem_append] at member
      exact member.elim sourceInheritedAbsent (fun localMember =>
        regionNe ((Concrete.Elaboration.mem_exactScopeWires input region
          inner).1 localMember).symm)
    let childEquiv := contextEquiv childWitness childNodup childAbsent
    let localWire :=
      (FiniteEquiv.finCast sourceLocalCanonical).trans
        ((localEquiv input outer inner distinct region regionNe).trans
          (FiniteEquiv.finCast targetLocalCanonical.symm))
    Concrete.Splice.Input.compilerBodyOuterWire sourceChildState
        targetChildState childEquiv =
      extendWireEquiv
        (Concrete.Splice.Input.compilerBodyOuterWire sourceState targetState
          inherited)
        localWire := by
  dsimp only
  let inherited := contextEquiv witness sourceInheritedNodup
    sourceInheritedAbsent
  let extendedWitness := witness.extend inputWellFormed ordered region
    sourceState.wiresExact targetState.wiresExact
  have sourceExtendedAbsent : inner ∉
      sourceState.inheritedWires.extend region := by
    intro member
    rw [Concrete.Elaboration.WireContext.extend, List.mem_append] at member
    exact member.elim sourceInheritedAbsent (fun localMember =>
      regionNe ((Concrete.Elaboration.mem_exactScopeWires input region
        inner).1 localMember).symm)
  let extendedEquiv := contextEquiv extendedWitness
    sourceState.wiresExact.nodup sourceExtendedAbsent
  have extendedEquivEq : extendedEquiv =
      (FiniteEquiv.finCast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region)).trans
        ((extendWireEquiv inherited
          (localEquiv input outer inner distinct region regionNe)).trans
          (FiniteEquiv.finCast
            (Concrete.Elaboration.WireContext.length_extend
              targetState.inheritedWires region)).symm) := by
    apply FiniteEquiv.ext
    intro index
    let split := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend
        sourceState.inheritedWires region) index
    have recover : Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm split = index := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun inheritedIndex => ?_)
      (fun localIndex => ?_) split
    · apply Fin.ext
      have mapped := witness.extend_index_inherited inputWellFormed ordered
        region sourceState.wiresExact targetState.wiresExact inheritedIndex
      simpa [extendedEquiv, inherited, contextEquiv, extendWireEquiv,
        FiniteEquiv.finCast, split] using congrArg Fin.val mapped
    · apply Fin.ext
      have mapped := witness.extend_index_local_of_ne inputWellFormed ordered
        region regionNe sourceState.wiresExact targetState.wiresExact localIndex
      simpa [extendedEquiv, inherited, contextEquiv, localEquiv,
        extendWireEquiv, FiniteEquiv.finCast, split] using
          congrArg Fin.val mapped
  let childWitness := contextWitnessCast extendedWitness sourceInherited
    targetInherited
  have childNodup : sourceChildState.inheritedWires.Nodup := by
    rw [sourceInherited]
    exact sourceState.wiresExact.nodup
  have childAbsent : inner ∉ sourceChildState.inheritedWires := by
    rw [sourceInherited]
    exact sourceExtendedAbsent
  let childEquiv := contextEquiv childWitness childNodup childAbsent
  have childEquivEq : childEquiv =
      (FiniteEquiv.finCast (congrArg List.length sourceInherited)).trans
        (extendedEquiv.trans
          (FiniteEquiv.finCast
            (congrArg List.length targetInherited).symm)) := by
    apply FiniteEquiv.ext
    intro index
    simpa [childEquiv, childWitness, extendedEquiv, contextEquiv,
      FiniteEquiv.finCast] using contextWitnessCast_indexMap extendedWitness
        sourceInherited targetInherited index
  let localWire :=
    (FiniteEquiv.finCast sourceLocalCanonical).trans
      ((localEquiv input outer inner distinct region regionNe).trans
        (FiniteEquiv.finCast targetLocalCanonical.symm))
  have sourceChildExtended : sourceOuter + sourceLocal =
      (sourceState.inheritedWires.extend region).length :=
    sourceChildState.inheritedLength.symm.trans
      (congrArg List.length sourceInherited)
  have targetChildExtended : targetOuter + targetLocal =
      (targetState.inheritedWires.extend region).length :=
    targetChildState.inheritedLength.symm.trans
      (congrArg List.length targetInherited)
  have algebra := Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
    sourceChildExtended
    (Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires region)
    sourceState.inheritedLength
    (rfl : sourceOuter + sourceLocal = _)
    sourceLocalCanonical
    targetChildExtended
    (Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires region)
    targetState.inheritedLength
    (rfl : targetOuter + targetLocal = _)
    targetLocalCanonical inherited
    (localEquiv input outer inner distinct region regionNe)
  change Concrete.Splice.Input.compilerBodyOuterWire sourceChildState
      targetChildState childEquiv = _
  rw [childEquivEq]
  rw [extendedEquivEq]
  simpa [Concrete.Splice.Input.compilerBodyOuterWire, inherited,
    localWire] using algebra

noncomputable def terminalLocal
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    {sourceOuter targetOuter : Nat}
    {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input
      (input.wires inner).scope (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (input.wires inner).scope (.here targetBody))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceState.inheritedWires targetState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel) :
    let inherited := contextEquiv witness
      (by
        have nodup := sourceState.wiresExact.nodup
        rw [Concrete.Elaboration.WireContext.extend,
          List.nodup_append] at nodup
        exact nodup.1)
      (by
        intro member
        exact (sourceState.inherited_mem_iff (.here _) inner).1 member |>.2 rfl)
    Σ before after : Region targetOuter rels,
      PSigma fun _rewrite : Rule.WireSever.Local before after =>
        PSigma fun _targetIso : RegionIso
            (FiniteEquiv.refl (Fin targetOuter)) rels targetBody before =>
          RegionIso (Concrete.Splice.Input.compilerBodyOuterWire sourceState
            targetState inherited) rels sourceBody after := by
  dsimp only
  have sourceNodup : sourceState.inheritedWires.Nodup := by
    have nodup := sourceState.wiresExact.nodup
    rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at nodup
    exact nodup.1
  have innerAbsent : inner ∉ sourceState.inheritedWires := by
    intro member
    exact (sourceState.inherited_mem_iff (.here _) inner).1 member |>.2 rfl
  let inherited := contextEquiv witness sourceNodup innerAbsent
  let sourceCanonical := Concrete.Elaboration.finishRegion input
    sourceState.inheritedWires (input.wires inner).scope sourceState.items
  let targetCanonical := Concrete.Elaboration.finishRegion
    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetState.inheritedWires
    (input.wires inner).scope targetState.items
  have sourceCompiled : Concrete.Elaboration.compileRegion? input
      (sourceState.fuel + 1) (input.wires inner).scope
      sourceState.inheritedWires sourceState.binders =
        some sourceCanonical := by
    simp only [Concrete.Elaboration.compileRegion?]
    rw [sourceState.itemsComputation]
    rfl
  have targetCompiled : Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (sourceState.fuel + 1) (input.wires inner).scope
      targetState.inheritedWires sourceState.binders =
        some targetCanonical := by
    simp only [Concrete.Elaboration.compileRegion?]
    have items : Concrete.Elaboration.compileOccurrencesWith?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (Concrete.Elaboration.compileRegion?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) sourceState.fuel)
        (targetState.inheritedWires.extend (input.wires inner).scope)
        sourceState.binders
        (Concrete.Elaboration.localOccurrences
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
          (input.wires inner).scope) = some targetState.items := by
      simpa [fuelEq, bindersEq] using targetState.itemsComputation
    rw [items]
    rfl
  obtain ⟨beforeRaw, afterRaw, rewriteRaw, targetIsoRaw, sourceIsoRaw⟩ :=
    siteLocal input inputWellFormed outer inner distinct ordered
      targetWellFormed sourceState.inheritedWires targetState.inheritedWires
      witness sourceState.wiresExact targetState.wiresExact innerAbsent
      (sourceState.fuel + 1) sourceState.binders sourceCompiled targetCompiled
  let sourceCast : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin sourceOuter) := FiniteEquiv.finCast sourceState.inheritedLength
  let targetCast : FiniteEquiv (Fin targetState.inheritedWires.length)
      (Fin targetOuter) := FiniteEquiv.finCast targetState.inheritedLength
  let before := beforeRaw.renameWires targetCast
  let after := afterRaw.renameWires targetCast
  have rewrite : Rule.WireSever.Local before after :=
    localRename targetCast rewriteRaw
  have sourceBodyEq : sourceBody =
      sourceCanonical.renameWires sourceCast := by
    simpa [sourceCanonical, sourceCast,
      Region.castWiresEq_eq_renameWires] using sourceState.bodyComputation
  have targetBodyEq : targetBody =
      targetCanonical.renameWires targetCast := by
    simpa [targetCanonical, targetCast,
      Region.castWiresEq_eq_renameWires] using targetState.bodyComputation
  have targetTransport : RegionIso (FiniteEquiv.refl (Fin targetOuter)) rels
      (targetCanonical.renameWires targetCast) before := by
    apply targetIsoRaw.renameWires_commuting targetCast targetCast
      (FiniteEquiv.refl (Fin targetOuter))
    funext index
    simp [FiniteEquiv.refl]
  have targetIso : RegionIso (FiniteEquiv.refl (Fin targetOuter)) rels
      targetBody before := by
    rw [targetBodyEq]
    exact targetTransport
  let outerWire := Concrete.Splice.Input.compilerBodyOuterWire sourceState
    targetState inherited
  have commutes : outerWire.toFun ∘ sourceCast.toFun =
      targetCast.toFun ∘ inherited.toFun := by
    funext index
    have recover : Fin.cast sourceState.inheritedLength.symm
        (Fin.cast sourceState.inheritedLength index) = index := by
      apply Fin.ext
      rfl
    change Fin.cast targetState.inheritedLength
        (inherited (Fin.cast sourceState.inheritedLength.symm
          (Fin.cast sourceState.inheritedLength index))) =
      Fin.cast targetState.inheritedLength (inherited index)
    rw [recover]
  have sourceTransport : RegionIso outerWire rels
      (sourceCanonical.renameWires sourceCast) after :=
    sourceIsoRaw.renameWires_commuting sourceCast targetCast outerWire commutes
  have sourceIso : RegionIso outerWire rels sourceBody after := by
    rw [sourceBodyEq]
    exact sourceTransport
  exact ⟨before, after, rewrite, targetIso, sourceIso⟩

structure CompilerTraceAlignment
    {sourceOuter targetOuter : Nat}
    {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath) where
  holeRelsEq : sourceWitness.toFocus.holeRels =
    targetWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  contexts : DiagramContextIso outerWire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq.symm ▸ targetWitness.toFocus.context)
  before : Region targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  after : Region targetWitness.toFocus.holeWires
    targetWitness.toFocus.holeRels
  rewrite : Rule.WireSever.Local before after
  target_iso : RegionIso
    (FiniteEquiv.refl (Fin targetWitness.toFocus.holeWires))
    targetWitness.toFocus.holeRels targetWitness.toFocus.body before
  source_iso : RegionIso holeWire sourceWitness.toFocus.holeRels
    sourceWitness.toFocus.body (holeRelsEq.symm ▸ after)

noncomputable def compilerTraceContextIso
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    {start site : Fin input.regionCount}
    (siteEq : (input.wires inner).scope = site)
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute input start
      site sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) start
      site targetPath}
    {sourceOuter targetOuter : Nat}
    {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input start
      (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) start (.here targetBody))
    (sourceTrace : Concrete.Splice.CompilerTrace input sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetRoute targetWitness
      targetState)
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceState.inheritedWires targetState.inheritedWires)
    (bindersEq : targetState.binders = sourceState.binders)
    (fuelEq : targetState.fuel = sourceState.fuel) :
    let sourceNodup : sourceState.inheritedWires.Nodup := by
      have nodup := sourceState.wiresExact.nodup
      rw [Concrete.Elaboration.WireContext.extend,
        List.nodup_append] at nodup
      exact nodup.1
    let innerAbsent : inner ∉ sourceState.inheritedWires := by
      intro member
      have inherited := (sourceState.inherited_mem_iff (.here _) inner).1 member
      have reverse : input.Encloses site start := by simpa [siteEq] using inherited.1
      have forward := Concrete.Splice.Input.RegionRoute.encloses sourceRoute
        inputWellFormed
      have equality := Concrete.Elaboration.checked_encloses_antisymm
        inputWellFormed forward reverse
      exact inherited.2 (siteEq.trans equality.symm)
    let inherited := contextEquiv witness sourceNodup innerAbsent
    CompilerTraceAlignment
      (Concrete.Splice.Input.compilerBodyOuterWire sourceState targetState
        inherited) sourceWitness targetWitness := by
  dsimp only
  revert targetTrace witness
  induction sourceTrace using @Concrete.Splice.CompilerTrace.rec input
      generalizing targetPath targetOuter with
  | here sourceState =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) with
      | here targetState =>
          intro witness
          cases siteEq
          obtain ⟨before, after, rewrite, targetIso, sourceIso⟩ :=
            terminalLocal input inputWellFormed outer inner distinct ordered
              targetWellFormed sourceState targetState witness bindersEq fuelEq
          let sourceNodup : sourceState.inheritedWires.Nodup := by
            have nodup := sourceState.wiresExact.nodup
            rw [Concrete.Elaboration.WireContext.extend,
              List.nodup_append] at nodup
            exact nodup.1
          let innerAbsent : inner ∉ sourceState.inheritedWires := by
            intro member
            exact (sourceState.inherited_mem_iff (.here _) inner).1 member |>.2 rfl
          let inherited := contextEquiv witness sourceNodup innerAbsent
          exact {
            holeRelsEq := rfl
            holeWire := Concrete.Splice.Input.compilerBodyOuterWire sourceState
              targetState inherited
            contexts := .hole _
            before := before
            after := after
            rewrite := rewrite
            target_iso := targetIso
            source_iso := sourceIso
          }
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ targetTailTrace =>
          intro witness
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              targetWellFormed targetParent
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed))
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ targetTailTrace =>
          intro witness
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              targetWellFormed targetParent
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed))
  | @cut sourceStart sourceChild sourceEnd sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceSeq
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) with
      | here targetState =>
          intro witness
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
                (Concrete.Splice.Input.RegionRoute.encloses sourceTail
                  inputWellFormed))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels
          targetSeq targetFocus targetChildBody targetAt targetIsCut targetNested
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro witness
          have sourceTailEncloses : input.Encloses sourceChild sourceEnd :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              inputWellFormed
          have targetTailEncloses : input.Encloses targetChild sourceEnd :=
            (VisualProof.Refinement.Implementation.WireJoin.target_encloses_iff input outer inner _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailSite : Concrete.Splice.RegionRoute input sourceChild
              (input.wires inner).scope sourceRest := by
            simpa only [siteEq] using sourceTail
          have targetParentInput : (input.regions targetChild).parent? =
              some sourceStart := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions] using targetParent
          have childrenEq : sourceChild = targetChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                sourceTailEncloses targetTailEncloses with
              sourceTarget | targetSource
            · rcases Concrete.Elaboration.encloses_direct_child targetParentInput
                  sourceTarget with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParentInput cycle)
          subst targetChild
          let targetPosition' : Fin
              (Concrete.Elaboration.localOccurrences input sourceStart).length :=
            Fin.cast (by simp) targetPosition
          have targetPositionEq' : indexOf?
              (Concrete.Elaboration.localOccurrences input sourceStart)
                (.child sourceChild) = some targetPosition' := by
            simpa [targetPosition'] using targetPositionEq
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences input sourceStart).get
                  targetPosition' = .child sourceChild := by
            simpa only [List.get_eq_getElem] using
              indexOf?_sound targetPositionEq'
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup input sourceStart)
              sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa [targetPosition'] using congrArg Fin.val positionsEq
          have regionNe : sourceStart ≠ (input.wires inner).scope := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
                (Concrete.Splice.Input.RegionRoute.encloses sourceTailSite
                  inputWellFormed)
          let childWitness0 := witness.extend inputWellFormed ordered sourceStart
            sourceState.wiresExact targetState.wiresExact
          let childWitness := contextWitnessCast childWitness0 sourceInherited
            targetInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans (bindersEq.trans sourceBinders.symm)
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by omega
          let childResult := ih siteEq targetChildState childBindersEq
            childFuelEq targetTailTrace childWitness
          have sourceNodup : sourceState.inheritedWires.Nodup := by
            have nodup := sourceState.wiresExact.nodup
            rw [Concrete.Elaboration.WireContext.extend,
              List.nodup_append] at nodup
            exact nodup.1
          have sourceAbsent : inner ∉ sourceState.inheritedWires := by
            intro member
            exact inner_absent_of_enclosing_route input inputWellFormed inner
              regionNe sourceParent sourceTailSite sourceState
                (List.mem_append_left _ member)
          let inherited := contextEquiv witness sourceNodup sourceAbsent
          let localWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              ((localEquiv input outer inner distinct sourceStart regionNe).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))
          have childOuter := compilerLeafOuterFactor input inputWellFormed outer
            inner distinct ordered regionNe sourceState targetState
            sourceLocalCanonical targetLocalCanonical witness sourceNodup
            sourceAbsent sourceChildState targetChildState sourceInherited
            targetInherited
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val,
              ItemSeq.focusAt?_index_lt targetSeq targetPosition.val
                targetFocus targetAt⟩
          let frame := compilerLeafFrame input inputWellFormed outer
            inner distinct ordered targetWellFormed regionNe sourceParent
            sourcePosition sourcePositionEq sourceTailSite sourceState targetState
            sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
            targetItemsCanonical witness bindersEq fuelEq sourceIndex targetIndex
            rfl positionVals
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (Concrete.Splice.Input.compilerBodyOuterWire sourceState
                  targetState inherited) localWire)
              childResult.holeWire sourceRels
              sourceNested.toFocus.holeRels sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.cut targetLocal targetFocus.before
                    targetFocus.after targetNested.toFocus.context =
                DiagramContext.cut targetLocal targetFocus.before
                  targetFocus.after
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.cut_transport_holeRels
              childResult.holeRelsEq targetFocus.before targetFocus.after
                targetNested.toFocus.context
          have cutContexts := DiagramContextIso.cutFrame
            (holeWire := childResult.holeWire) localWire sourceFocus targetFocus
            sourceAt targetAt frame sourceNested.toFocus.context
            (childResult.holeRelsEq.symm ▸ targetNested.toFocus.context)
            childContexts
          exact {
            holeRelsEq := childResult.holeRelsEq
            holeWire := childResult.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using cutContexts
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            target_iso := childResult.target_iso
            source_iso := childResult.source_iso
          }
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro witness
          have targetKind : input.regions targetChild =
              .bubble sourceStart targetArity := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions] using targetChildKind
          have sourceTailEncloses : input.Encloses sourceChild sourceEnd :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              inputWellFormed
          have targetTailEncloses : input.Encloses targetChild sourceEnd :=
            (VisualProof.Refinement.Implementation.WireJoin.target_encloses_iff input outer inner _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have targetParentInput : (input.regions targetChild).parent? =
              some sourceStart := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions] using targetParent
          have childrenEq : sourceChild = targetChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                sourceTailEncloses targetTailEncloses with
              sourceTarget | targetSource
            · rcases Concrete.Elaboration.encloses_direct_child targetParentInput
                  sourceTarget with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParentInput cycle)
          subst targetChild
          have impossible := sourceChildKind.symm.trans targetKind
          contradiction
  | @bubble sourceStart sourceChild sourceEnd sourceRest sourceParent
      sourcePosition sourcePositionEq sourceTail sourceOuter sourceLocal
      sourceArity sourceRels sourceSeq sourceFocus sourceChildBody sourceAt
      sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace ih =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) with
      | here targetState =>
          intro witness
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
                (Concrete.Splice.Input.RegionRoute.encloses sourceTail
                  inputWellFormed))
      | @cut _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetRels
          targetSeq targetFocus targetChildBody targetAt targetIsCut targetNested
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          intro witness
          have targetKind : input.regions targetChild =
              .cut sourceStart := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions]
              using targetChildKind
          have sourceTailEncloses : input.Encloses sourceChild sourceEnd :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              inputWellFormed
          have targetTailEncloses : input.Encloses targetChild sourceEnd :=
            (VisualProof.Refinement.Implementation.WireJoin.target_encloses_iff
              input outer inner _ _).1
                (Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed)
          have targetParentInput : (input.regions targetChild).parent? =
              some sourceStart := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions]
              using targetParent
          have childrenEq : sourceChild = targetChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                sourceTailEncloses targetTailEncloses with
              sourceTarget | targetSource
            · rcases Concrete.Elaboration.encloses_direct_child
                  targetParentInput sourceTarget with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParentInput cycle)
          subst targetChild
          have impossible := sourceChildKind.symm.trans targetKind
          contradiction
      | @bubble _ targetChild _ targetRest targetParent targetPosition
          targetPositionEq targetTail targetOuter targetLocal targetArity
          targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro witness
          have targetKind : input.regions targetChild =
              .bubble sourceStart targetArity := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions]
              using targetChildKind
          have sourceTailEncloses : input.Encloses sourceChild sourceEnd :=
            Concrete.Splice.Input.RegionRoute.encloses sourceTail
              inputWellFormed
          have targetTailEncloses : input.Encloses targetChild sourceEnd :=
            (VisualProof.Refinement.Implementation.WireJoin.target_encloses_iff input outer inner _ _).1
              (Concrete.Splice.Input.RegionRoute.encloses targetTail
                targetWellFormed)
          have sourceTailSite : Concrete.Splice.RegionRoute input sourceChild
              (input.wires inner).scope sourceRest := by
            simpa only [siteEq] using sourceTail
          have targetParentInput : (input.regions targetChild).parent? =
              some sourceStart := by
            simpa [VisualProof.Refinement.Implementation.WireJoin.target_regions] using targetParent
          have childrenEq : sourceChild = targetChild := by
            rcases Concrete.Diagram.enclosingRegions_comparable
                sourceTailEncloses targetTailEncloses with
              sourceTarget | targetSource
            · rcases Concrete.Elaboration.encloses_direct_child targetParentInput
                  sourceTarget with equality | cycle
              · exact equality
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed sourceParent cycle)
            · rcases Concrete.Elaboration.encloses_direct_child sourceParent
                  targetSource with equality | cycle
              · exact equality.symm
              · exact False.elim
                  (Concrete.Elaboration.checked_direct_child_not_encloses_parent
                    inputWellFormed targetParentInput cycle)
          subst targetChild
          have aritiesEq : targetArity = sourceArity := by
            have kinds := targetKind.symm.trans sourceChildKind
            injection kinds
          subst targetArity
          let targetPosition' : Fin
              (Concrete.Elaboration.localOccurrences input sourceStart).length :=
            Fin.cast (by simp) targetPosition
          have targetPositionEq' : indexOf?
              (Concrete.Elaboration.localOccurrences input sourceStart)
                (.child sourceChild) = some targetPosition' := by
            simpa [targetPosition'] using targetPositionEq
          have targetPositionGet :
              (Concrete.Elaboration.localOccurrences input sourceStart).get
                  targetPosition' = .child sourceChild := by
            simpa only [List.get_eq_getElem] using
              indexOf?_sound targetPositionEq'
          have positionsEq : targetPosition' = sourcePosition :=
            indexOf?_unique_of_nodup
              (Concrete.Elaboration.localOccurrences_nodup input sourceStart)
              sourcePositionEq targetPositionGet
          have positionVals : targetPosition.val = sourcePosition.val := by
            simpa [targetPosition'] using congrArg Fin.val positionsEq
          have regionNe : sourceStart ≠ (input.wires inner).scope := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              inputWellFormed sourceParent
                (Concrete.Splice.Input.RegionRoute.encloses sourceTailSite
                  inputWellFormed)
          let childWitness0 := witness.extend inputWellFormed ordered sourceStart
            sourceState.wiresExact targetState.wiresExact
          let childWitness := contextWitnessCast childWitness0 sourceInherited
            targetInherited
          have childBindersEq : targetChildState.binders =
              sourceChildState.binders :=
            targetBinders.trans
              ((congrArg (fun binders => binders.push sourceChild sourceArity)
                bindersEq).trans sourceBinders.symm)
          have childFuelEq : targetChildState.fuel =
              sourceChildState.fuel := by omega
          let childResult := ih siteEq targetChildState childBindersEq
            childFuelEq targetTailTrace childWitness
          have sourceNodup : sourceState.inheritedWires.Nodup := by
            have nodup := sourceState.wiresExact.nodup
            rw [Concrete.Elaboration.WireContext.extend,
              List.nodup_append] at nodup
            exact nodup.1
          have sourceAbsent : inner ∉ sourceState.inheritedWires := by
            intro member
            exact inner_absent_of_enclosing_route input inputWellFormed inner
              regionNe sourceParent sourceTailSite sourceState
                (List.mem_append_left _ member)
          let inherited := contextEquiv witness sourceNodup sourceAbsent
          let localWire :=
            (FiniteEquiv.finCast sourceLocalCanonical).trans
              ((localEquiv input outer inner distinct sourceStart regionNe).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))
          have childOuter := compilerLeafOuterFactor input inputWellFormed outer
            inner distinct ordered regionNe sourceState targetState
            sourceLocalCanonical targetLocalCanonical witness sourceNodup
            sourceAbsent sourceChildState targetChildState sourceInherited
            targetInherited
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val,
              ItemSeq.focusAt?_index_lt sourceSeq sourcePosition.val
                sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val,
              ItemSeq.focusAt?_index_lt targetSeq targetPosition.val
                targetFocus targetAt⟩
          let frame := compilerLeafFrame input inputWellFormed outer
            inner distinct ordered targetWellFormed regionNe sourceParent
            sourcePosition sourcePositionEq sourceTailSite sourceState targetState
            sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
            targetItemsCanonical witness bindersEq fuelEq sourceIndex targetIndex
            rfl positionVals
          have childContexts : DiagramContextIso
              (extendWireEquiv
                (Concrete.Splice.Input.compilerBodyOuterWire sourceState
                  targetState inherited) localWire)
              childResult.holeWire (sourceArity :: sourceRels)
              sourceNested.toFocus.holeRels sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuter]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.bubble targetLocal targetFocus.before
                    targetFocus.after sourceArity targetNested.toFocus.context =
                DiagramContext.bubble targetLocal targetFocus.before
                  targetFocus.after sourceArity
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
            exact DiagramContext.bubble_transport_holeRels
              childResult.holeRelsEq targetFocus.before targetFocus.after
                targetNested.toFocus.context
          have bubbleContexts := DiagramContextIso.bubbleFrame
            (holeWire := childResult.holeWire) localWire sourceFocus targetFocus
            sourceAt targetAt frame sourceNested.toFocus.context
            (childResult.holeRelsEq.symm ▸ targetNested.toFocus.context)
            childContexts
          exact {
            holeRelsEq := childResult.holeRelsEq
            holeWire := childResult.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using bubbleContexts
            before := childResult.before
            after := childResult.after
            rewrite := childResult.rewrite
            target_iso := childResult.target_iso
            source_iso := childResult.source_iso
          }

end VisualProof.Refinement.Implementation.WireJoinPairedContext
