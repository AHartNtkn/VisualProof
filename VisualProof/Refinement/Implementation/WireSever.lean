import VisualProof.Concrete.Step
import VisualProof.Rule.WireSever
import VisualProof.Refinement.Implementation.WireSeverCore

namespace VisualProof.Refinement.Implementation.WireSever

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private theorem wireSever_castArity
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (step : Rule.WireSever source target) :
    Rule.WireSever (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using step

private def reindexOpen
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity) : OpenDiagram targetArity where
  externalClasses := diagram.externalClasses
  boundary := fun position => diagram.boundary (Fin.cast equality.symm position)
  boundary_surjective := by
    intro external
    obtain ⟨position, rfl⟩ := diagram.boundary_surjective external
    exact ⟨Fin.cast equality position, by simp [Fin.cast]⟩
  body := diagram.body

private theorem reindexOpen_eq_castArity
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity) :
    reindexOpen diagram equality = diagram.castArity equality := by
  subst targetArity
  rfl

def canonicalOpen
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed) :
    Concrete.CheckedOpen :=
  ⟨VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep,
    VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_wellFormed source wire keep
      targetWellFormed⟩

def separatedOpen
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed) :
    Concrete.CheckedOpen := {
  val := {
    diagram := Concrete.severWireRaw source.checked.val.diagram wire keep
    boundary := List.ofFn (Concrete.severBoundaryImage source wire boundary)
  }
  property := {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := by
      intro targetWire targetMem
      obtain ⟨position, rfl⟩ := List.mem_ofFn.mp targetMem
      exact Concrete.severBoundaryImage_rootScoped source wire keep boundary
        position
  }
}

private def concreteIsoOfEq {source target : Concrete.Diagram}
    (equality : source = target) : Concrete.Iso source target := by
  subst target
  exact Concrete.Iso.refl source

private theorem concreteIsoOfEq_wires {source target : Concrete.Diagram}
    (equality : source = target) (wire : Fin source.wireCount) :
    (concreteIsoOfEq equality).wires wire =
      Fin.cast (congrArg Concrete.Diagram.wireCount equality) wire := by
  subst target
  rfl

def resultOpenIso
    (orientation : Concrete.Orientation)
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (result : Concrete.OperationReceipt source.diagram)
    (success : Concrete.applyWireSever orientation source.diagram wire keep =
      .ok result) :
    Concrete.OpenIso
      (separatedOpen source wire keep boundary
        ((Concrete.applyWireSever_preserves_raw success) ▸
          result.result.property)).val
      (Concrete.wireSeverResultOpen orientation source wire keep boundary result
        success).val := by
  let rawEq := Concrete.applyWireSever_preserves_raw success
  refine {
    diagram := concreteIsoOfEq rawEq.symm
    boundary := ?_
  }
  simp only [separatedOpen, Concrete.wireSeverResultOpen, List.map_ofFn]
  change List.ofFn
      ((concreteIsoOfEq rawEq.symm).wires ∘
        Concrete.severBoundaryImage source wire boundary) =
    List.ofFn fun position => Fin.cast
      (congrArg Concrete.Diagram.wireCount rawEq).symm
      (Concrete.severBoundaryImage source wire boundary position)
  apply congrArg List.ofFn
  funext position
  exact concreteIsoOfEq_wires rawEq.symm _

private def swapEquiv (left right : Fin count) (distinct : left ≠ right) :
    FiniteEquiv (Fin count) (Fin count) where
  toFun candidate :=
    if candidate = left then right
    else if candidate = right then left
    else candidate
  invFun candidate :=
    if candidate = left then right
    else if candidate = right then left
    else candidate
  left_inv := by
    intro candidate
    by_cases candidateLeft : candidate = left
    · subst candidate
      simp [Ne.symm distinct]
    · by_cases candidateRight : candidate = right
      · subst candidate
        simp [Ne.symm distinct]
      · simp [candidateLeft, candidateRight]
  right_inv := by
    intro candidate
    by_cases candidateLeft : candidate = left
    · subst candidate
      simp [Ne.symm distinct]
    · by_cases candidateRight : candidate = right
      · subst candidate
        simp [Ne.symm distinct]
      · simp [candidateLeft, candidateRight]

@[simp] private theorem swapEquiv_left (left right : Fin count)
    (distinct : left ≠ right) :
    swapEquiv left right distinct left = right := by
  simp [swapEquiv]

@[simp] private theorem swapEquiv_right (left right : Fin count)
    (distinct : left ≠ right) :
    swapEquiv left right distinct right = left := by
  simp [swapEquiv, Ne.symm distinct]

private theorem swapEquiv_other (left right candidate : Fin count)
    (distinct : left ≠ right)
    (notLeft : candidate ≠ left) (notRight : candidate ≠ right) :
    swapEquiv left right distinct candidate = candidate := by
  simp [swapEquiv, notLeft, notRight]

private noncomputable def boundaryRepresentative
    (diagram : OpenDiagram arity)
    (external : Fin diagram.externalClasses) : Fin arity :=
  Classical.choose (diagram.boundary_surjective external)

private theorem boundaryRepresentative_spec
    (diagram : OpenDiagram arity)
    (external : Fin diagram.externalClasses) :
    diagram.boundary (boundaryRepresentative diagram external) = external :=
  Classical.choose_spec (diagram.boundary_surjective external)

private theorem castArity_boundary_eq_iff
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (left right : Fin targetArity) :
    (diagram.castArity equality).boundary left =
        (diagram.castArity equality).boundary right ↔
      diagram.boundary (Fin.cast equality.symm left) =
        diagram.boundary (Fin.cast equality.symm right) := by
  subst targetArity
  rfl

private noncomputable def boundaryMap
    (source target : OpenDiagram arity) :
    Fin target.externalClasses → Fin source.externalClasses :=
  fun external => source.boundary (boundaryRepresentative target external)

private theorem boundaryMap_boundary
    (source target : OpenDiagram arity)
    (refines : ∀ left right,
      target.boundary left = target.boundary right →
        source.boundary left = source.boundary right)
    (position : Fin arity) :
    boundaryMap source target (target.boundary position) =
      source.boundary position := by
  apply refines
  exact boundaryRepresentative_spec target (target.boundary position)

private theorem boundaryMap_surjective
    (source target : OpenDiagram arity)
    (refines : ∀ left right,
      target.boundary left = target.boundary right →
        source.boundary left = source.boundary right) :
    Function.Surjective (boundaryMap source target) := by
  intro external
  obtain ⟨position, rfl⟩ := source.boundary_surjective external
  exact ⟨target.boundary position,
    boundaryMap_boundary source target refines position⟩

private noncomputable def boundaryEquiv
    (source target : OpenDiagram arity)
    (refines : ∀ left right,
      target.boundary left = target.boundary right →
        source.boundary left = source.boundary right)
    (reflects : ∀ left right,
      source.boundary left = source.boundary right →
        target.boundary left = target.boundary right) :
    FiniteEquiv (Fin target.externalClasses) (Fin source.externalClasses) where
  toFun := boundaryMap source target
  invFun := boundaryMap target source
  left_inv := by
    intro external
    obtain ⟨position, rfl⟩ := target.boundary_surjective external
    rw [boundaryMap_boundary source target refines,
      boundaryMap_boundary target source reflects]
  right_inv := by
    intro external
    obtain ⟨position, rfl⟩ := source.boundary_surjective external
    rw [boundaryMap_boundary target source reflects,
      boundaryMap_boundary source target refines]

private theorem binaryBoundaryDichotomy
    (source target : OpenDiagram arity)
    (side : Fin arity → Bool)
    (classes : ∀ left right,
      target.boundary left = target.boundary right ↔
        source.boundary left = source.boundary right ∧
          side left = side right)
    (true_alias : ∀ left right,
      side left = true → side right = true →
        source.boundary left = source.boundary right) :
    (∀ left right,
      source.boundary left = source.boundary right →
        target.boundary left = target.boundary right) ∨
      Nonempty (FiniteEquiv (Fin target.externalClasses)
        (Fin (source.externalClasses + 1))) := by
  classical
  by_cases reflects : ∀ left right,
      source.boundary left = source.boundary right →
        target.boundary left = target.boundary right
  · exact Or.inl reflects
  · have witness : ∃ left right,
        source.boundary left = source.boundary right ∧
          target.boundary left ≠ target.boundary right := by
      exact Classical.byContradiction fun absent => reflects (by
        intro left right sourceAlias
        exact Classical.byContradiction fun targetDistinct =>
          absent ⟨left, right, sourceAlias, targetDistinct⟩)
    obtain ⟨left, right, sourceAlias, targetDistinct⟩ := witness
    have sideDistinct : side left ≠ side right := by
      intro sideEq
      exact targetDistinct ((classes left right).2 ⟨sourceAlias, sideEq⟩)
    have split
        (falsePosition truePosition : Fin arity)
        (falseSide : side falsePosition = false)
        (trueSide : side truePosition = true)
        (sourceAlias : source.boundary falsePosition =
          source.boundary truePosition) :
        Nonempty (FiniteEquiv (Fin target.externalClasses)
          (Fin (source.externalClasses + 1))) := by
      let falseRepresentative : Fin source.externalClasses → Fin arity :=
        fun external =>
          if external = source.boundary falsePosition then falsePosition
          else boundaryRepresentative source external
      have falseRepresentative_source (external : Fin source.externalClasses) :
          source.boundary (falseRepresentative external) = external := by
        by_cases same : external = source.boundary falsePosition
        · simp [falseRepresentative, same]
        · simp [falseRepresentative, same, boundaryRepresentative_spec]
      have falseRepresentative_side (external : Fin source.externalClasses) :
          side (falseRepresentative external) = false := by
        by_cases same : external = source.boundary falsePosition
        · simpa [falseRepresentative, same] using falseSide
        · have sourceClass := falseRepresentative_source external
          have notTrue : side (falseRepresentative external) ≠ true := by
            intro isTrue
            have alias := true_alias (falseRepresentative external)
              truePosition isTrue trueSide
            exact same (by
              rw [← sourceClass, alias, ← sourceAlias])
          cases sideValue : side (falseRepresentative external)
          · rfl
          · exact False.elim (notTrue sideValue)
      let lower : Fin (source.externalClasses + 1) →
          Fin target.externalClasses :=
        Fin.lastCases (target.boundary truePosition)
          (fun external => target.boundary (falseRepresentative external))
      let upper : Fin target.externalClasses →
          Fin (source.externalClasses + 1) :=
        fun external =>
          let position := boundaryRepresentative target external
          if side position then
            Fin.last source.externalClasses
          else
            (source.boundary position).castSucc
      have upper_lower : ∀ index, upper (lower index) = index := by
        intro index
        refine Fin.lastCases (motive := fun index => upper (lower index) = index)
          ?_ (fun external => ?_) index
        · let position := boundaryRepresentative target
            (target.boundary truePosition)
          have targetAlias : target.boundary position =
              target.boundary truePosition := by
            exact boundaryRepresentative_spec target _
          have sideEq := (classes position truePosition).1 targetAlias |>.2
          simp [upper, lower, position, sideEq, trueSide]
        · let position := boundaryRepresentative target
            (target.boundary (falseRepresentative external))
          have targetAlias : target.boundary position =
              target.boundary (falseRepresentative external) := by
            exact boundaryRepresentative_spec target _
          have classData := (classes position
            (falseRepresentative external)).1 targetAlias
          have sideEq : side position = false :=
            classData.2.trans (falseRepresentative_side external)
          have sourceEq : source.boundary position = external :=
            classData.1.trans (falseRepresentative_source external)
          apply Fin.ext
          simp [upper, lower, position, sideEq, sourceEq]
      have lower_upper : ∀ external, lower (upper external) = external := by
        intro external
        let position := boundaryRepresentative target external
        have targetAtPosition : target.boundary position = external :=
          boundaryRepresentative_spec target external
        by_cases isTrue : side position = true
        · have sourceAtPosition : source.boundary position =
              source.boundary truePosition :=
            true_alias position truePosition isTrue trueSide
          have targetAlias : target.boundary position =
              target.boundary truePosition :=
            (classes position truePosition).2 ⟨sourceAtPosition,
              isTrue.trans trueSide.symm⟩
          have upperEq : upper external = Fin.last source.externalClasses := by
            simp [upper, position, isTrue]
          rw [upperEq]
          simp only [lower, Fin.lastCases_last]
          change target.boundary truePosition = external
          exact targetAlias.symm.trans targetAtPosition
        · have isFalse : side position = false := by
            cases sideValue : side position
            · rfl
            · exact False.elim (isTrue sideValue)
          have sourceAtRepresentative := falseRepresentative_source
            (source.boundary position)
          have targetAlias :
              target.boundary
                  (falseRepresentative (source.boundary position)) =
                target.boundary position :=
            (classes _ position).2 ⟨sourceAtRepresentative,
              (falseRepresentative_side _).trans isFalse.symm⟩
          have upperEq : upper external =
              (source.boundary position).castSucc := by
            simp [upper, position, isFalse]
          rw [upperEq]
          simp only [lower, Fin.lastCases_castSucc]
          change target.boundary
              (falseRepresentative (source.boundary position)) = external
          exact targetAlias.trans targetAtPosition
      exact ⟨{
        toFun := upper
        invFun := lower
        left_inv := lower_upper
        right_inv := upper_lower
      }⟩
    cases leftSide : side left <;> cases rightSide : side right
    · exact False.elim (sideDistinct (leftSide.trans rightSide.symm))
    · exact Or.inr (split left right leftSide rightSide sourceAlias)
    · exact Or.inr (split right left rightSide leftSide sourceAlias.symm)
    · exact False.elim (sideDistinct (leftSide.trans rightSide.symm))

theorem severBoundaryImage_collapse
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (position : Fin arity) :
    VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
        (Concrete.severBoundaryImage source wire boundary position) =
      source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position) := by
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  change VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
    (if sourceWire = wire ∧ boundary.side position then
      Fin.last source.checked.val.diagram.wireCount
    else sourceWire.castSucc) = sourceWire
  split
  · rename_i selected
    simpa using selected.1.symm
  · simp

theorem severBoundaryImage_eq_fresh_iff
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (boundary : Concrete.WireSeverBoundary source wire)
    (position : Fin arity) :
    Concrete.severBoundaryImage source wire boundary position =
        Fin.last source.checked.val.diagram.wireCount ↔
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm position) = wire ∧
        boundary.side position = true := by
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  change (if sourceWire = wire ∧ boundary.side position then
      Fin.last source.checked.val.diagram.wireCount
    else sourceWire.castSucc) =
      Fin.last source.checked.val.diagram.wireCount ↔
    sourceWire = wire ∧ boundary.side position = true
  by_cases selected : sourceWire = wire ∧ boundary.side position = true
  · simp [selected]
  · rw [if_neg (by simpa using selected)]
    constructor
    · intro equality
      have values := congrArg Fin.val equality
      simp only [Fin.val_castSucc, Fin.val_last] at values
      exact False.elim (Nat.ne_of_lt sourceWire.isLt values)
    · exact fun selected' => False.elim (selected selected')

theorem severBoundaryImage_eq_iff
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (boundary : Concrete.WireSeverBoundary source wire)
    (left right : Fin arity) :
    Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right ↔
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) ∧
      boundary.side left = boundary.side right := by
  let leftWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm left)
  let rightWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm right)
  change (if leftWire = wire ∧ boundary.side left then
        Fin.last source.checked.val.diagram.wireCount
      else leftWire.castSucc) =
      (if rightWire = wire ∧ boundary.side right then
        Fin.last source.checked.val.diagram.wireCount
      else rightWire.castSucc) ↔
    leftWire = rightWire ∧ boundary.side left = boundary.side right
  have castSucc_eq_iff (first second :
      Fin source.checked.val.diagram.wireCount) :
      first.castSucc = second.castSucc ↔ first = second := by
    constructor
    · intro equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (source.checked.val.diagram.wireCount + 1) =>
          value.val) equality
    · intro equality
      exact congrArg Fin.castSucc equality
  have last_ne_castSucc (candidate :
      Fin source.checked.val.diagram.wireCount) :
      Fin.last source.checked.val.diagram.wireCount ≠ candidate.castSucc := by
    intro equality
    have values := congrArg Fin.val equality
    simp only [Fin.val_last, Fin.val_castSucc] at values
    exact Nat.ne_of_gt candidate.isLt values
  have castSucc_ne_last (candidate :
      Fin source.checked.val.diagram.wireCount) :
      candidate.castSucc ≠ Fin.last source.checked.val.diagram.wireCount :=
    fun equality => last_ne_castSucc candidate equality.symm
  by_cases leftIsSplit : leftWire = wire
  · by_cases rightIsSplit : rightWire = wire
    · cases leftSide : boundary.side left <;>
          cases rightSide : boundary.side right <;>
        simp [leftIsSplit, rightIsSplit, last_ne_castSucc,
          castSucc_ne_last]
    · have rightSide := boundary.other right rightIsSplit
      cases leftSide : boundary.side left <;>
        simp [leftIsSplit, rightIsSplit, rightSide, castSucc_eq_iff,
          last_ne_castSucc]
  · have leftSide := boundary.other left leftIsSplit
    by_cases rightIsSplit : rightWire = wire
    · cases rightSide : boundary.side right <;>
        simp [leftIsSplit, rightIsSplit, leftSide, castSucc_eq_iff,
          castSucc_ne_last]
    · have rightSide := boundary.other right rightIsSplit
      simp [leftIsSplit, rightIsSplit, leftSide, rightSide,
        castSucc_eq_iff]

theorem severBoundary_true_alias
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (boundary : Concrete.WireSeverBoundary source wire)
    (left right : Fin arity)
    (leftSide : boundary.side left = true)
    (rightSide : boundary.side right = true) :
    source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm left) =
      source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm right) := by
  have leftWire : source.checked.val.boundary.get
      (Fin.cast source.boundary_length.symm left) = wire := by
    exact Classical.byContradiction fun distinct =>
      Bool.noConfusion (leftSide.symm.trans (boundary.other left distinct))
  have rightWire : source.checked.val.boundary.get
      (Fin.cast source.boundary_length.symm right) = wire := by
    exact Classical.byContradiction fun distinct =>
      Bool.noConfusion (rightSide.symm.trans (boundary.other right distinct))
  exact leftWire.trans rightWire.symm

theorem separatedBoundaryDichotomy
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed) :
    let target := separatedOpen source wire keep boundary targetWellFormed
    let targetLength : target.val.boundary.length = arity := by
      simp [target, separatedOpen]
    let sourceDiagram :=
      source.checked.elaborate.castArity source.boundary_length
    let targetDiagram := target.elaborate.castArity targetLength
    (∀ left right,
      sourceDiagram.boundary left = sourceDiagram.boundary right →
        targetDiagram.boundary left = targetDiagram.boundary right) ∨
      Nonempty (FiniteEquiv (Fin targetDiagram.externalClasses)
        (Fin (sourceDiagram.externalClasses + 1))) := by
  dsimp only
  let target := separatedOpen source wire keep boundary targetWellFormed
  let targetLength : target.val.boundary.length = arity := by
    simp [target, separatedOpen]
  let sourceDiagram :=
    source.checked.elaborate.castArity source.boundary_length
  let targetDiagram := target.elaborate.castArity targetLength
  apply binaryBoundaryDichotomy sourceDiagram targetDiagram boundary.side
  · intro left right
    rw [castArity_boundary_eq_iff, castArity_boundary_eq_iff]
    change target.val.boundaryClass
        (Fin.cast targetLength.symm left) =
          target.val.boundaryClass (Fin.cast targetLength.symm right) ↔
      source.checked.val.boundaryClass
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundaryClass
          (Fin.cast source.boundary_length.symm right) ∧
      boundary.side left = boundary.side right
    rw [Concrete.OpenDiagram.boundaryClass_eq_iff,
      Concrete.OpenDiagram.boundaryClass_eq_iff]
    simpa [target, separatedOpen, targetLength] using
      severBoundaryImage_eq_iff source wire boundary left right
  · intro left right leftSide rightSide
    apply (castArity_boundary_eq_iff source.checked.elaborate
      source.boundary_length left right).2
    change source.checked.val.boundaryClass
        (Fin.cast source.boundary_length.symm left) =
      source.checked.val.boundaryClass
        (Fin.cast source.boundary_length.symm right)
    rw [Concrete.OpenDiagram.boundaryClass_eq_iff]
    exact severBoundary_true_alias source wire boundary left right
      leftSide rightSide

theorem separatedBoundaryDichotomyRaw
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed) :
    let target := separatedOpen source wire keep boundary targetWellFormed
    let targetLength : target.val.boundary.length = arity := by
      simp [target, separatedOpen]
    let sourceDiagram :=
      source.checked.elaborate.castArity source.boundary_length
    let targetDiagram := target.elaborate.castArity targetLength
    (∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) ∨
      Nonempty (FiniteEquiv (Fin targetDiagram.externalClasses)
        (Fin (sourceDiagram.externalClasses + 1))) := by
  dsimp only
  obtain reflects | split :=
    separatedBoundaryDichotomy source wire keep boundary targetWellFormed
  · exact Or.inl (by
      intro left right sourceEq
      have sourceClassEq :
          (source.checked.elaborate.castArity
              source.boundary_length).boundary left =
            (source.checked.elaborate.castArity
              source.boundary_length).boundary right := by
        apply (castArity_boundary_eq_iff source.checked.elaborate
          source.boundary_length left right).2
        change source.checked.val.boundaryClass
            (Fin.cast source.boundary_length.symm left) =
          source.checked.val.boundaryClass
            (Fin.cast source.boundary_length.symm right)
        rw [Concrete.OpenDiagram.boundaryClass_eq_iff]
        exact sourceEq
      have targetClassEq := reflects left right sourceClassEq
      have targetClassEq' :=
        (castArity_boundary_eq_iff
          (separatedOpen source wire keep boundary targetWellFormed).elaborate
          (by simp [separatedOpen]) left right).1 targetClassEq
      have rawBoundaryEq :=
        (Concrete.OpenDiagram.boundaryClass_eq_iff
          (separatedOpen source wire keep boundary targetWellFormed).val
          _ _).mp targetClassEq'
      simpa [separatedOpen] using rawBoundaryEq)
  · exact Or.inr split

private def rootNormalization
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed) :
    FiniteEquiv
      (Fin (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount)
      (Fin (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount) :=
  let target := separatedOpen source wire keep boundary targetWellFormed
  let old := wire.castSucc
  let fresh := Fin.last source.checked.val.diagram.wireCount
  if fresh ∈ target.val.exposedWires then
    swapEquiv old fresh (by
      intro equality
      have values := congrArg Fin.val equality
      exact Nat.ne_of_lt wire.isLt values)
  else
    FiniteEquiv.refl _

theorem rootNormalization_boundary
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (position : Fin arity) :
    rootNormalization source wire keep boundary targetWellFormed
        (Concrete.severBoundaryImage source wire boundary position) =
      (source.checked.val.boundary.get
        (Fin.cast source.boundary_length.symm position)).castSucc := by
  let target := separatedOpen source wire keep boundary targetWellFormed
  let sourceWire := source.checked.val.boundary.get
    (Fin.cast source.boundary_length.symm position)
  let old := wire.castSucc
  let fresh := Fin.last source.checked.val.diagram.wireCount
  have oldFresh : old ≠ fresh := by
    intro equality
    have values := congrArg Fin.val equality
    simp only [old, fresh, Fin.val_castSucc, Fin.val_last] at values
    exact Nat.ne_of_lt wire.isLt values
  by_cases freshExposed : fresh ∈ target.val.exposedWires
  · have freshBoundary : fresh ∈ target.val.boundary :=
      (Concrete.OpenDiagram.mem_exposedWires target.val fresh).1 freshExposed
    obtain ⟨freshPosition, freshEq⟩ := List.mem_ofFn.mp freshBoundary
    have freshImage : Concrete.severBoundaryImage source wire boundary
        freshPosition = fresh := freshEq
    have freshData := (severBoundaryImage_eq_fresh_iff source wire boundary
      freshPosition).1 freshImage
    by_cases isSplit : sourceWire = wire
    · have imageEq := reflects position freshPosition
          (isSplit.trans freshData.1.symm)
      have imageFresh : Concrete.severBoundaryImage source wire boundary
          position = fresh := imageEq.trans freshImage
      rw [imageFresh]
      change (if fresh ∈ target.val.exposedWires then
          swapEquiv old fresh oldFresh else FiniteEquiv.refl _) fresh =
        sourceWire.castSucc
      rw [if_pos freshExposed, swapEquiv_right]
      exact congrArg Fin.castSucc isSplit.symm
    · have sideFalse := boundary.other position isSplit
      have imageOld : Concrete.severBoundaryImage source wire boundary
          position = sourceWire.castSucc := by
        simp [Concrete.severBoundaryImage, sourceWire, sideFalse]
      rw [imageOld]
      have notOld : sourceWire.castSucc ≠ old := by
        intro equality
        apply isSplit
        apply Fin.ext
        exact congrArg
          (fun value : Fin (source.checked.val.diagram.wireCount + 1) =>
            value.val)
          equality
      have notFresh : sourceWire.castSucc ≠ fresh := by
        intro equality
        have values := congrArg Fin.val equality
        simp only [fresh, Fin.val_castSucc, Fin.val_last] at values
        exact Nat.ne_of_lt sourceWire.isLt values
      change (if fresh ∈ target.val.exposedWires then
          swapEquiv old fresh oldFresh else FiniteEquiv.refl _)
          sourceWire.castSucc = sourceWire.castSucc
      rw [if_pos freshExposed]
      exact swapEquiv_other old fresh sourceWire.castSucc oldFresh notOld
        notFresh
  · have imageNotFresh :
        Concrete.severBoundaryImage source wire boundary position ≠ fresh := by
      intro imageFresh
      apply freshExposed
      apply (Concrete.OpenDiagram.mem_exposedWires target.val fresh).2
      exact List.mem_ofFn.mpr ⟨position, imageFresh⟩
    have imageOld : Concrete.severBoundaryImage source wire boundary position =
        sourceWire.castSucc := by
      unfold Concrete.severBoundaryImage
      dsimp only [sourceWire]
      split
      · rename_i selected
        apply False.elim
        apply imageNotFresh
        change (if sourceWire = wire ∧ boundary.side position then
            Fin.last source.checked.val.diagram.wireCount
          else sourceWire.castSucc) = fresh
        rw [if_pos selected]
      · rfl
    rw [imageOld]
    change (if fresh ∈ target.val.exposedWires then
        swapEquiv old fresh oldFresh else FiniteEquiv.refl _)
        sourceWire.castSucc = sourceWire.castSucc
    rw [if_neg freshExposed]
    rfl

theorem rootNormalization_collapse
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (candidate : Fin
      (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount) :
    VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
        (rootNormalization source wire keep boundary targetWellFormed candidate) =
      VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
        candidate := by
  let target := separatedOpen source wire keep boundary targetWellFormed
  let old := wire.castSucc
  let fresh := Fin.last source.checked.val.diagram.wireCount
  have oldFresh : old ≠ fresh := by
    intro equality
    have values := congrArg Fin.val equality
    exact Nat.ne_of_lt wire.isLt values
  by_cases freshExposed : fresh ∈ target.val.exposedWires
  · change fresh ∈ (separatedOpen source wire keep boundary
        targetWellFormed).val.exposedWires at freshExposed
    dsimp [rootNormalization]
    rw [if_pos freshExposed]
    change VisualProof.Refinement.Implementation.WireSever.severWireCollapse _ wire keep
        (swapEquiv old fresh oldFresh candidate) =
      VisualProof.Refinement.Implementation.WireSever.severWireCollapse _ wire keep candidate
    by_cases candidateOld : candidate = old
    · subst candidate
      rw [swapEquiv_left]
      simp [old, fresh]
    · by_cases candidateFresh : candidate = fresh
      · subst candidate
        rw [swapEquiv_right]
        simp [old, fresh]
      · rw [swapEquiv_other old fresh candidate oldFresh candidateOld
          candidateFresh]
  · change fresh ∉ (separatedOpen source wire keep boundary
        targetWellFormed).val.exposedWires at freshExposed
    dsimp [rootNormalization]
    rw [if_neg freshExposed]
    change VisualProof.Refinement.Implementation.WireSever.severWireCollapse _ wire keep
        ((FiniteEquiv.refl _) candidate) = _
    rfl

theorem rootNormalization_scope
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (candidate : Fin
      (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount) :
    ((Concrete.severWireRaw source.checked.val.diagram wire keep).wires
      (rootNormalization source wire keep boundary targetWellFormed candidate)).scope =
    ((Concrete.severWireRaw source.checked.val.diagram wire keep).wires
      candidate).scope := by
  rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_scope_collapse,
    VisualProof.Refinement.Implementation.WireSever.severWireRaw_scope_collapse,
    rootNormalization_collapse]

theorem rootNormalization_boundaryList
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    (separatedOpen source wire keep boundary targetWellFormed).val.boundary.map
        (rootNormalization source wire keep boundary targetWellFormed) =
      (canonicalOpen source.checked wire keep targetWellFormed).val.boundary := by
  apply List.ext_get
  · simpa [separatedOpen, canonicalOpen,
      VisualProof.Refinement.Implementation.WireSever.severWireRawOpen] using source.boundary_length.symm
  · intro index targetBound canonicalBound
    let position : Fin arity := ⟨index, by
      simpa [separatedOpen] using targetBound⟩
    have normalized := rootNormalization_boundary source wire keep boundary
      targetWellFormed reflects position
    simpa [separatedOpen, canonicalOpen, VisualProof.Refinement.Implementation.WireSever.severWireRawOpen,
      position, List.get_eq_getElem, List.getElem_ofFn] using normalized

theorem rootNormalization_exposed_mem_iff
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (candidate : Fin
      (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount) :
    rootNormalization source wire keep boundary targetWellFormed candidate ∈
        (canonicalOpen source.checked wire keep targetWellFormed).val.exposedWires ↔
      candidate ∈
        (separatedOpen source wire keep boundary targetWellFormed).val.exposedWires := by
  let normalization := rootNormalization source wire keep boundary
    targetWellFormed
  have mapped : normalization candidate ∈
        List.map normalization
          (separatedOpen source wire keep boundary targetWellFormed).val.boundary ↔
      candidate ∈
        (separatedOpen source wire keep boundary targetWellFormed).val.boundary := by
    constructor
    · intro member
      obtain ⟨original, originalMember, imageEq⟩ := List.mem_map.mp member
      exact (normalization.injective imageEq).symm ▸ originalMember
    · intro member
      exact List.mem_map.mpr ⟨candidate, member, rfl⟩
  calc
    normalization candidate ∈
        (canonicalOpen source.checked wire keep targetWellFormed).val.exposedWires ↔
      normalization candidate ∈
        (canonicalOpen source.checked wire keep targetWellFormed).val.boundary :=
      Concrete.OpenDiagram.mem_exposedWires _ _
    _ ↔ normalization candidate ∈
        List.map normalization
          (separatedOpen source wire keep boundary targetWellFormed).val.boundary := by
      rw [rootNormalization_boundaryList source wire keep boundary
        targetWellFormed reflects]
      rfl
    _ ↔ candidate ∈
        (separatedOpen source wire keep boundary targetWellFormed).val.boundary :=
      mapped
    _ ↔ candidate ∈
        (separatedOpen source wire keep boundary targetWellFormed).val.exposedWires :=
      (Concrete.OpenDiagram.mem_exposedWires _ _).symm

theorem rootNormalization_hidden_mem_iff
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (candidate : Fin
      (Concrete.severWireRaw source.checked.val.diagram wire keep).wireCount) :
    rootNormalization source wire keep boundary targetWellFormed candidate ∈
        (canonicalOpen source.checked wire keep targetWellFormed).val.hiddenWires ↔
      candidate ∈
        (separatedOpen source wire keep boundary targetWellFormed).val.hiddenWires := by
  let normalization := rootNormalization source wire keep boundary
    targetWellFormed
  let canonical := canonicalOpen source.checked wire keep targetWellFormed
  let target := separatedOpen source wire keep boundary targetWellFormed
  have facts :
      ((canonical.val.diagram.wires (normalization candidate)).scope =
          canonical.val.diagram.root ∧
        normalization candidate ∉ canonical.val.exposedWires) ↔
      ((target.val.diagram.wires candidate).scope = target.val.diagram.root ∧
        candidate ∉ target.val.exposedWires) := by
    constructor
    · intro data
      exact ⟨(rootNormalization_scope source wire keep boundary
        targetWellFormed candidate).symm.trans data.1,
        fun exposed => data.2
          ((rootNormalization_exposed_mem_iff source wire keep boundary
            targetWellFormed reflects candidate).2 exposed)⟩
    · intro data
      exact ⟨(rootNormalization_scope source wire keep boundary
        targetWellFormed candidate).trans data.1,
        fun exposed => data.2
          ((rootNormalization_exposed_mem_iff source wire keep boundary
            targetWellFormed reflects candidate).1 exposed)⟩
  calc
    normalization candidate ∈ canonical.val.hiddenWires ↔
      (canonical.val.diagram.wires (normalization candidate)).scope =
          canonical.val.diagram.root ∧
        normalization candidate ∉ canonical.val.exposedWires :=
      Concrete.OpenDiagram.mem_hiddenWires _ _
    _ ↔ (target.val.diagram.wires candidate).scope = target.val.diagram.root ∧
        candidate ∉ target.val.exposedWires := facts
    _ ↔ candidate ∈ target.val.hiddenWires :=
      (Concrete.OpenDiagram.mem_hiddenWires _ _).symm

noncomputable def rootExternalEquiv
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    FiniteEquiv
      (Fin (separatedOpen source wire keep boundary
        targetWellFormed).val.exposedWires.length)
      (Fin (canonicalOpen source.checked wire keep
        targetWellFormed).val.exposedWires.length) :=
  FiniteEquiv.restrictLists
    (rootNormalization source wire keep boundary targetWellFormed)
    (separatedOpen source wire keep boundary targetWellFormed).val.exposedWires
    (canonicalOpen source.checked wire keep targetWellFormed).val.exposedWires
    (separatedOpen source wire keep boundary
      targetWellFormed).val.exposedWires_nodup
    (canonicalOpen source.checked wire keep
      targetWellFormed).val.exposedWires_nodup
    (rootNormalization_exposed_mem_iff source wire keep boundary
      targetWellFormed reflects)

theorem rootExternalEquiv_spec
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (index : Fin (separatedOpen source wire keep boundary
      targetWellFormed).val.exposedWires.length) :
    (canonicalOpen source.checked wire keep targetWellFormed).val.exposedWires.get
        (rootExternalEquiv source wire keep boundary targetWellFormed
          reflects index) =
      rootNormalization source wire keep boundary targetWellFormed
        ((separatedOpen source wire keep boundary
          targetWellFormed).val.exposedWires.get index) := by
  exact FiniteEquiv.restrictLists_spec _ _ _ _ _ _ index

theorem rootExternalEquiv_boundaryClass
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (position : Fin arity) :
    rootExternalEquiv source wire keep boundary targetWellFormed reflects
        ((separatedOpen source wire keep boundary
          targetWellFormed).val.boundaryClass
            (Fin.cast (by simp [separatedOpen]) position)) =
      (canonicalOpen source.checked wire keep
        targetWellFormed).val.boundaryClass
          (Fin.cast (by
            simpa [canonicalOpen, VisualProof.Refinement.Implementation.WireSever.severWireRawOpen] using
              source.boundary_length.symm) position) := by
  apply Concrete.OpenDiagram.boundaryClass_complete
  rw [rootExternalEquiv_spec,
    Concrete.OpenDiagram.boundaryClass_sound]
  simpa [separatedOpen, canonicalOpen, VisualProof.Refinement.Implementation.WireSever.severWireRawOpen,
    List.get_eq_getElem, List.getElem_ofFn] using
      rootNormalization_boundary source wire keep boundary targetWellFormed
        reflects position

noncomputable def rootLocalEquiv
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    FiniteEquiv
      (Fin (separatedOpen source wire keep boundary
        targetWellFormed).val.hiddenWires.length)
      (Fin (canonicalOpen source.checked wire keep
        targetWellFormed).val.hiddenWires.length) :=
  FiniteEquiv.restrictLists
    (rootNormalization source wire keep boundary targetWellFormed)
    (separatedOpen source wire keep boundary targetWellFormed).val.hiddenWires
    (canonicalOpen source.checked wire keep targetWellFormed).val.hiddenWires
    (separatedOpen source wire keep boundary
      targetWellFormed).val.hiddenWires_nodup
    (canonicalOpen source.checked wire keep
      targetWellFormed).val.hiddenWires_nodup
    (rootNormalization_hidden_mem_iff source wire keep boundary
      targetWellFormed reflects)

theorem rootLocalEquiv_spec
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (index : Fin (separatedOpen source wire keep boundary
      targetWellFormed).val.hiddenWires.length) :
    (canonicalOpen source.checked wire keep targetWellFormed).val.hiddenWires.get
        (rootLocalEquiv source wire keep boundary targetWellFormed
          reflects index) =
      rootNormalization source wire keep boundary targetWellFormed
        ((separatedOpen source wire keep boundary
          targetWellFormed).val.hiddenWires.get index) := by
  exact FiniteEquiv.restrictLists_spec _ _ _ _ _ _ index

noncomputable def rootCoordinateEquiv
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    FiniteEquiv
      (Fin (separatedOpen source wire keep boundary
        targetWellFormed).val.rootWires.length)
      (Fin (canonicalOpen source.checked wire keep
        targetWellFormed).val.rootWires.length) :=
  let target := separatedOpen source wire keep boundary targetWellFormed
  let canonical := canonicalOpen source.checked wire keep targetWellFormed
  let targetEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let canonicalEq : canonical.val.rootWires.length =
      canonical.val.exposedWires.length + canonical.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  (FiniteEquiv.finCast targetEq).trans
    ((extendWireEquiv
      (rootExternalEquiv source wire keep boundary targetWellFormed reflects)
      (rootLocalEquiv source wire keep boundary targetWellFormed reflects)).trans
      (FiniteEquiv.finCast canonicalEq.symm))

theorem rootCoordinateEquiv_spec
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right)
    (index : Fin (separatedOpen source wire keep boundary
      targetWellFormed).val.rootWires.length) :
    (canonicalOpen source.checked wire keep targetWellFormed).val.rootWires.get
        (rootCoordinateEquiv source wire keep boundary targetWellFormed
          reflects index) =
      rootNormalization source wire keep boundary targetWellFormed
        ((separatedOpen source wire keep boundary
          targetWellFormed).val.rootWires.get index) := by
  let target := separatedOpen source wire keep boundary targetWellFormed
  let canonical := canonicalOpen source.checked wire keep targetWellFormed
  let targetEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let canonicalEq : canonical.val.rootWires.length =
      canonical.val.exposedWires.length + canonical.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let position := Fin.cast targetEq index
  generalize positionEq : position = split
  revert positionEq
  refine Fin.addCases (fun external positionEq => ?_)
    (fun localIndex positionEq => ?_) split
  · have externalSpec := rootExternalEquiv_spec source wire keep boundary
      targetWellFormed reflects external
    have indexEq : index = Fin.cast targetEq.symm
        (Fin.castAdd target.val.hiddenWires.length external) := by
      apply Fin.ext
      have values := congrArg Fin.val positionEq
      simpa [position] using values
    rw [indexEq]
    have coordinateEq :
        rootCoordinateEquiv source wire keep boundary targetWellFormed reflects
            (Fin.cast targetEq.symm
              (Fin.castAdd target.val.hiddenWires.length external)) =
          Fin.cast canonicalEq.symm
            (Fin.castAdd canonical.val.hiddenWires.length
              (rootExternalEquiv source wire keep boundary targetWellFormed
                reflects external)) := by
      apply Fin.ext
      simp [rootCoordinateEquiv, target, canonical,
        extendWireEquiv, FiniteEquiv.finCast]
    rw [coordinateEq]
    simpa [target, canonical, targetEq, canonicalEq,
      Concrete.OpenDiagram.rootWires] using externalSpec
  · have localSpec := rootLocalEquiv_spec source wire keep boundary
      targetWellFormed reflects localIndex
    have indexEq : index = Fin.cast targetEq.symm
        (Fin.natAdd target.val.exposedWires.length localIndex) := by
      apply Fin.ext
      have values := congrArg Fin.val positionEq
      simpa [position] using values
    rw [indexEq]
    have coordinateEq :
        rootCoordinateEquiv source wire keep boundary targetWellFormed reflects
            (Fin.cast targetEq.symm
              (Fin.natAdd target.val.exposedWires.length localIndex)) =
          Fin.cast canonicalEq.symm
            (Fin.natAdd canonical.val.exposedWires.length
              (rootLocalEquiv source wire keep boundary targetWellFormed
                reflects localIndex)) := by
      apply Fin.ext
      simp [rootCoordinateEquiv, target, canonical,
        extendWireEquiv, FiniteEquiv.finCast]
    rw [coordinateEq]
    simpa [target, canonical, targetEq, canonicalEq,
      Concrete.OpenDiagram.rootWires] using localSpec

noncomputable def targetRootCollapse
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed) :
    VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse source.checked.val.diagram wire keep
      (separatedOpen source wire keep boundary targetWellFormed).val.rootWires
      source.checked.val.rootWires :=
  .ofMem (by
    intro candidate
    rw [Concrete.OpenDiagram.mem_rootWires_iff source.checked.val
      source.checked.property]
    constructor
    · intro sourceScope
      apply (Concrete.OpenDiagram.mem_rootWires_iff
        (separatedOpen source wire keep boundary targetWellFormed).val
        (separatedOpen source wire keep boundary targetWellFormed).property
        candidate).2
      change ((Concrete.severWireRaw source.checked.val.diagram wire keep).wires
        candidate).scope =
          (Concrete.severWireRaw source.checked.val.diagram wire keep).root
      rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_scope_collapse,
        VisualProof.Refinement.Implementation.WireSever.severWireRaw_root]
      exact sourceScope
    · intro targetMember
      have targetScope := (Concrete.OpenDiagram.mem_rootWires_iff
        (separatedOpen source wire keep boundary targetWellFormed).val
        (separatedOpen source wire keep boundary targetWellFormed).property
        candidate).1 targetMember
      change ((Concrete.severWireRaw source.checked.val.diagram wire keep).wires
        candidate).scope =
          (Concrete.severWireRaw source.checked.val.diagram wire keep).root
          at targetScope
      rwa [VisualProof.Refinement.Implementation.WireSever.severWireRaw_scope_collapse,
        VisualProof.Refinement.Implementation.WireSever.severWireRaw_root] at targetScope)

theorem severCompileSiteItems_of_nodes_children
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (separateContext : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep))
    (joinedContext : Concrete.Elaboration.WireContext input)
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse
      input wire keep separateContext joinedContext)
    (binders : Concrete.Elaboration.BinderContext input rels)
    (region : Fin input.regionCount)
    (fuel : Nat)
    (joinedNodup : joinedContext.Nodup)
    (inputDisjoint : input.WireEndpointsAreDisjoint)
    (children : forall {childRels : RelCtx} child
      (childBinders : Concrete.Elaboration.BinderContext input childRels),
      Concrete.Elaboration.LocalOccurrence.child child ∈
          Concrete.Elaboration.localOccurrences input region ->
      Concrete.Elaboration.compileRegion? input fuel child joinedContext
          childBinders =
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw input wire keep) fuel child separateContext
          childBinders).map (Region.renameWires collapse.indexMap)) :
    Concrete.Elaboration.compileOccurrencesWith? input
        (Concrete.Elaboration.compileRegion? input fuel)
        joinedContext binders
        (Concrete.Elaboration.localOccurrences input region) =
      (Concrete.Elaboration.compileOccurrencesWith?
        (Concrete.severWireRaw input wire keep)
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw input wire keep) fuel)
        separateContext binders
        (Concrete.Elaboration.localOccurrences
          (Concrete.severWireRaw input wire keep)
          region)).map
            (ItemSeq.renameWires collapse.indexMap) := by
  rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences]
  simpa using Concrete.Elaboration.compileOccurrencesWith?_map
    (Concrete.Elaboration.compileRegion?
      (Concrete.severWireRaw input wire keep) fuel)
    (Concrete.Elaboration.compileRegion? input fuel)
    separateContext joinedContext binders binders id collapse.indexMap
    (Concrete.Elaboration.localOccurrences input region)
    (by
      intro occurrence member
      cases occurrence with
      | node node =>
          simpa [Concrete.Elaboration.compileOccurrenceWith?] using
            VisualProof.Refinement.Implementation.WireSever.severWireRaw_compileNode?_collapse
              input wire keep separateContext joinedContext collapse binders
              joinedNodup inputDisjoint node
      | child child =>
          cases kind : input.regions child with
          | sheet => simp [Concrete.Elaboration.compileOccurrenceWith?, kind]
          | cut parent =>
              have mapped := children child binders member
              simp only [id_eq, Concrete.Elaboration.compileOccurrenceWith?,
                kind, VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions]
              rw [mapped]
              cases hrecursive : Concrete.Elaboration.compileRegion?
                (Concrete.severWireRaw input wire keep) fuel child
                separateContext binders <;>
                simp [Item.renameWires]
          | bubble parent arity =>
              have mapped := children child (binders.push child arity) member
              simp only [id_eq, Concrete.Elaboration.compileOccurrenceWith?,
                kind, VisualProof.Refinement.Implementation.WireSever.severWireRaw_regions]
              rw [mapped]
              change
                (Option.map (Region.renameWires collapse.indexMap)
                    (Concrete.Elaboration.compileRegion?
                      (Concrete.severWireRaw input wire keep) fuel child
                      separateContext (binders.push child arity))).bind
                    (fun body => some (Item.bubble arity body)) =
                  Option.map (Item.renameWires collapse.indexMap)
                    ((Concrete.Elaboration.compileRegion?
                      (Concrete.severWireRaw input wire keep) fuel child
                      separateContext (binders.push child arity)).bind
                        (fun body => some (Item.bubble arity body)))
              rw [Option.bind_map, Option.map_bind]
              rfl)

noncomputable def severExtendedMapOfNe
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      separateContext joinedContext)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope) :
    Fin (separateContext.extend region).length ->
      Fin (joinedContext.extend region).length :=
  fun index =>
    Fin.cast
      ((congrArg (fun localCount => joinedContext.length + localCount)
          (VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne
            input wire keep region hne)).trans
        (Concrete.Elaboration.WireContext.length_extend joinedContext
          region).symm)
      (extendWireRenaming collapse.indexMap
        (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).length
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend separateContext
            region) index))

theorem severExtendedMapOfNe_spec
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      separateContext joinedContext)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (index : Fin (separateContext.extend region).length) :
    (joinedContext.extend region).get
        (severExtendedMapOfNe collapse region hne index) =
      VisualProof.Refinement.Implementation.WireSever.severWireCollapse input wire keep
        ((separateContext.extend region).get index) := by
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend separateContext region)
    index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend separateContext
        region).symm split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have mapEq : severExtendedMapOfNe collapse region hne
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend separateContext
            region).symm
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires
              (Concrete.severWireRaw input wire keep) region).length
            inherited)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend joinedContext
          region).symm
        (Fin.castAdd
          (Concrete.Elaboration.exactScopeWires input region).length
          (collapse.indexMap inherited)) := by
      apply Fin.ext
      simp [severExtendedMapOfNe, extendWireRenaming]
    rw [mapEq]
    simpa [Concrete.Elaboration.WireContext.extend] using collapse.get inherited
  · let localEq :=
      VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne
        input wire keep region hne
    have mapEq : severExtendedMapOfNe collapse region hne
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend separateContext
            region).symm
          (Fin.natAdd separateContext.length localIndex)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend joinedContext
          region).symm
        (Fin.natAdd joinedContext.length (Fin.cast localEq localIndex)) := by
      apply Fin.ext
      simp [severExtendedMapOfNe, extendWireRenaming]
    rw [mapEq]
    have listEq := VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_of_ne
      input wire keep region hne
    let sourceLocal := Fin.cast localEq localIndex
    have targetLocal :
        (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw input wire keep) region).get localIndex =
        Fin.castSucc
          ((Concrete.Elaboration.exactScopeWires input region).get
            sourceLocal) := by
      have getEq := VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq listEq localIndex
      have indexEq :
          Fin.cast
              (List.length_map
                (as := Concrete.Elaboration.exactScopeWires input region)
                Fin.castSucc).symm sourceLocal =
            Fin.cast (congrArg List.length listEq) localIndex := by
        apply Fin.ext
        rfl
      rw [← indexEq] at getEq
      exact getEq.trans
          (VisualProof.Refinement.Implementation.WireSever.listGet_map_cast_soundness
            (Concrete.Elaboration.exactScopeWires input region) Fin.castSucc
            sourceLocal)
    have joinedGet :
        (joinedContext.extend region).get
            (Fin.cast
              (Concrete.Elaboration.WireContext.length_extend joinedContext
                region).symm
              (Fin.natAdd joinedContext.length sourceLocal)) =
          (Concrete.Elaboration.exactScopeWires input region).get
            sourceLocal := by
      simpa only [List.get_eq_getElem, Fin.val_cast] using
        Concrete.Elaboration.WireContext.extend_local joinedContext region
          sourceLocal
    have separateGet :
        (separateContext.extend region).get
            (Fin.cast
              (Concrete.Elaboration.WireContext.length_extend separateContext
                region).symm
              (Fin.natAdd separateContext.length localIndex)) =
          (Concrete.Elaboration.exactScopeWires
            (Concrete.severWireRaw input wire keep) region).get
              localIndex := by
      simpa only [List.get_eq_getElem, Fin.val_cast] using
        Concrete.Elaboration.WireContext.extend_local separateContext region
          localIndex
    rw [show Fin.cast localEq localIndex = sourceLocal from rfl,
      joinedGet, separateGet]
    rw [targetLocal]
    exact (VisualProof.Refinement.Implementation.WireSever.severWireCollapse_old input wire _ keep).symm

theorem SeverContextCollapse.extend_index_eq_map_of_ne
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse input wire keep
      separateContext joinedContext)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (joinedNodup : (joinedContext.extend region).Nodup)
    (index : Fin (separateContext.extend region).length) :
    (collapse.extend region).indexMap index =
      severExtendedMapOfNe collapse region hne index := by
  apply Fin.ext
  exact (List.getElem_inj joinedNodup).mp (by
    simpa only [List.get_eq_getElem] using
      (collapse.extend region).get index |>.trans
        (severExtendedMapOfNe_spec collapse region hne index).symm)

private theorem region_mk_eq_of_local_eq
    {outer leftLocal rightLocal : Nat}
    (hlocal : leftLocal = rightLocal)
    (left : ItemSeq (outer + leftLocal) rels)
    (right : ItemSeq (outer + rightLocal) rels)
    (hitems : left.castWiresEq
      (congrArg (fun localCount => outer + localCount) hlocal) = right) :
    Region.mk leftLocal left = Region.mk rightLocal right := by
  subst rightLocal
  cases hitems
  rfl

theorem finishRegion_collapse_of_ne
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (separateContext : Concrete.Elaboration.WireContext
      (Concrete.severWireRaw input wire keep))
    (joinedContext : Concrete.Elaboration.WireContext input)
    (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse
      input wire keep separateContext joinedContext)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires wire).scope)
    (items : ItemSeq (separateContext.extend region).length rels) :
    Concrete.Elaboration.finishRegion input joinedContext region
        (items.renameWires
          (severExtendedMapOfNe collapse region hne)) =
      Region.renameWires collapse.indexMap
        (Concrete.Elaboration.finishRegion
          (Concrete.severWireRaw input wire keep) separateContext region items) := by
  unfold Concrete.Elaboration.finishRegion
  simp only [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp, Region.renameWires]
  let hlength := VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires_length_of_ne
    input wire keep region hne
  apply region_mk_eq_of_local_eq hlength.symm
  rw [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp]
  congr 1

private theorem direct_child_encloses
    {input : Concrete.Diagram} {parent child : Fin input.regionCount}
    (hparent : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  have positive : 0 < input.regionCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  change (match (input.regions child).parent? with
    | none => none
    | some directParent => input.climb 0 directParent) = some parent
  rw [hparent]
  rfl

theorem compileRegion_collapse_of_not_encloses
    (input : Concrete.Diagram)
    (wire : Fin input.wireCount)
    (keep : List (Concrete.CEndpoint input.nodeCount))
    (inputWellFormed : input.WellFormed)
    (separateWellFormed :
      (Concrete.severWireRaw input wire keep).WellFormed) :
    ∀ {rels : RelCtx} (fuel : Nat) (region : Fin input.regionCount)
      (separateContext : Concrete.Elaboration.WireContext
        (Concrete.severWireRaw input wire keep))
      (joinedContext : Concrete.Elaboration.WireContext input)
      (collapse : VisualProof.Refinement.Implementation.WireSever.SeverContextCollapse
        input wire keep separateContext joinedContext)
      (binders : Concrete.Elaboration.BinderContext input rels),
      ¬ input.Encloses region (input.wires wire).scope →
      (separateContext.extend region).Exact region →
      (joinedContext.extend region).Exact region →
      Concrete.Elaboration.compileRegion? input fuel region joinedContext
          binders =
        (Concrete.Elaboration.compileRegion?
          (Concrete.severWireRaw input wire keep) fuel region separateContext
          binders).map (Region.renameWires collapse.indexMap) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region separateContext joinedContext collapse binders hnotAbove
        separateExact joinedExact
      rfl
  | succ fuel ih =>
      intro region separateContext joinedContext collapse binders hnotAbove
        separateExact joinedExact
      have regionNe : region ≠ (input.wires wire).scope := by
        intro equality
        subst region
        exact hnotAbove
          (Concrete.Diagram.Encloses.refl input (input.wires wire).scope)
      simp only [Concrete.Elaboration.compileRegion?]
      rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_localOccurrences]
      let separateExtended := separateContext.extend region
      let joinedExtended := joinedContext.extend region
      let extendedCollapse := collapse.extend region
      have sequence :
          Concrete.Elaboration.compileOccurrencesWith? input
              (Concrete.Elaboration.compileRegion? input fuel)
              joinedExtended binders
              (Concrete.Elaboration.localOccurrences input region) =
            (Concrete.Elaboration.compileOccurrencesWith?
              (Concrete.severWireRaw input wire keep)
              (Concrete.Elaboration.compileRegion?
                (Concrete.severWireRaw input wire keep) fuel)
              separateExtended binders
              (Concrete.Elaboration.localOccurrences input region)).map
                (ItemSeq.renameWires extendedCollapse.indexMap) := by
        apply severCompileSiteItems_of_nodes_children input wire keep
          separateExtended joinedExtended extendedCollapse binders region fuel
          joinedExact.nodup inputWellFormed.wire_endpoints_are_disjoint
        intro childRels child childBinders member
        have parent :=
          (Concrete.Elaboration.mem_localOccurrences_child input region child).mp
            member
        have regionChild : input.Encloses region child :=
          direct_child_encloses parent
        have childNotAbove :
            ¬ input.Encloses child (input.wires wire).scope := by
          intro childAbove
          exact hnotAbove (Concrete.Elaboration.checked_encloses_trans
            inputWellFormed regionChild childAbove)
        have separateChild := separateExact.extend_child separateWellFormed parent
        have joinedChild := joinedExact.extend_child inputWellFormed parent
        exact ih child separateExtended joinedExtended extendedCollapse
          childBinders childNotAbove separateChild joinedChild
      cases separateItemsEq : Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.severWireRaw input wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw input wire keep) fuel)
          separateExtended binders
          (Concrete.Elaboration.localOccurrences input region) with
      | none =>
          have joinedItemsEq := sequence
          rw [separateItemsEq] at joinedItemsEq
          simp only [Option.map_none] at joinedItemsEq
          change
            (Concrete.Elaboration.compileOccurrencesWith? input
              (Concrete.Elaboration.compileRegion? input fuel)
              joinedExtended binders
              (Concrete.Elaboration.localOccurrences input region)).bind
                (fun items => some (Concrete.Elaboration.finishRegion input
                  joinedContext region items)) = none
          rw [joinedItemsEq]
          rfl
      | some items =>
          have joinedItemsEq := sequence
          rw [separateItemsEq] at joinedItemsEq
          simp only [Option.map_some] at joinedItemsEq
          change
            (Concrete.Elaboration.compileOccurrencesWith? input
              (Concrete.Elaboration.compileRegion? input fuel)
              joinedExtended binders
              (Concrete.Elaboration.localOccurrences input region)).bind
                (fun current => some (Concrete.Elaboration.finishRegion input
                  joinedContext region current)) =
              some (Region.renameWires collapse.indexMap
                (Concrete.Elaboration.finishRegion
                  (Concrete.severWireRaw input wire keep) separateContext
                  region items))
          rw [joinedItemsEq]
          simp only [Option.bind_some]
          have wireMap : extendedCollapse.indexMap =
              severExtendedMapOfNe collapse region regionNe := by
            funext index
            exact SeverContextCollapse.extend_index_eq_map_of_ne collapse
              region regionNe joinedExact.nodup index
          rw [wireMap]
          exact congrArg some
            (finishRegion_collapse_of_ne input wire keep separateContext
              joinedContext collapse region regionNe items)

theorem canonicalRootWires
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (scopeRoot :
      (source.val.diagram.wires wire).scope = source.val.diagram.root) :
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires =
      source.val.rootWires.map Fin.castSucc ++
        [Fin.last source.val.diagram.wireCount] := by
  rw [VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootWires, if_pos scopeRoot.symm]

theorem canonicalRootWires_length
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (scopeRoot :
      (source.val.diagram.wires wire).scope = source.val.diagram.root) :
    (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires.length =
      source.val.rootWires.length + 1 := by
  have equality := congrArg List.length
    (canonicalRootWires source wire keep scopeRoot)
  calc
    _ = (source.val.rootWires.map Fin.castSucc ++
        [Fin.last source.val.diagram.wireCount]).length := equality
    _ = source.val.rootWires.length + 1 := by
      rw [List.length_append, List.length_map]
      rfl

theorem canonicalRootCollapse_old
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.val.diagram.wires wire).scope = source.val.diagram.root)
    (index : Fin source.val.rootWires.length) :
    let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire
      keep targetWellFormed
    let lengthEq := canonicalRootWires_length source wire keep scopeRoot
    collapse.indexMap (Fin.cast lengthEq.symm index.castSucc) = index := by
  dsimp only
  let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire
    keep targetWellFormed
  have lengthEq := canonicalRootWires_length source wire keep scopeRoot
  let targetIndex := Fin.cast lengthEq.symm index.castSucc
  apply Fin.ext
  apply (List.getElem_inj source.val.rootWires_nodup).mp
  simpa only [List.get_eq_getElem] using
    (show source.val.rootWires.get (collapse.indexMap targetIndex) =
        source.val.rootWires.get index by
      calc
        source.val.rootWires.get (collapse.indexMap targetIndex) =
            VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.val.diagram wire keep
              ((VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires.get
                targetIndex) :=
          collapse.get targetIndex
        _ = source.val.rootWires.get index := by
          have targetGet := VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq
            (canonicalRootWires source wire keep scopeRoot) targetIndex
          let canonicalLength :
              (source.val.rootWires.map Fin.castSucc ++
                [Fin.last source.val.diagram.wireCount]).length =
              source.val.rootWires.length + 1 := by
            rw [List.length_append, List.length_map]
            rfl
          let canonicalOldIndex := Fin.cast canonicalLength.symm index.castSucc
          have targetIndexEq : Fin.cast
              (congrArg List.length
                (canonicalRootWires source wire keep scopeRoot)) targetIndex =
              canonicalOldIndex := by
            apply Fin.ext
            rfl
          rw [targetIndexEq] at targetGet
          change
            (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen source.val wire keep).rootWires.get
                targetIndex =
              (source.val.rootWires.map Fin.castSucc ++
                [Fin.last source.val.diagram.wireCount]).get
                  canonicalOldIndex
              at targetGet
          rw [targetGet]
          simp [canonicalOldIndex, List.get_eq_getElem,
            VisualProof.Refinement.Implementation.WireSever.severWireCollapse])

theorem canonicalRootCollapse_factor
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.val.diagram.wires wire).scope = source.val.diagram.root) :
    let target := canonicalOpen source wire keep targetWellFormed
    let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire
      keep targetWellFormed
    let sourceTotal := source.val.exposedWires.length +
      source.val.hiddenWires.length
    let sourceLength : source.val.rootWires.length = sourceTotal := by
      simp [Concrete.OpenDiagram.rootWires, sourceTotal]
    let targetLength : target.val.rootWires.length = sourceTotal + 1 := by
      exact (canonicalRootWires_length source wire keep scopeRoot).trans
        (congrArg (fun count => count + 1) sourceLength)
    let fresh := Fin.cast
      (canonicalRootWires_length source wire keep scopeRoot).symm
      (Fin.last source.val.rootWires.length)
    let joined := Fin.cast sourceLength (collapse.indexMap fresh)
    ∀ index,
      Fin.cast sourceLength (collapse.indexMap index) =
        VisualProof.Rule.WireSever.collapseLocal
          source.val.exposedWires.length source.val.hiddenWires.length joined
          (Fin.cast targetLength index) := by
  dsimp only
  intro index
  let lengthEq := canonicalRootWires_length source wire keep scopeRoot
  have totalEq : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  by_cases oldBound : index.val < source.val.rootWires.length
  · let old : Fin source.val.rootWires.length := ⟨index.val, oldBound⟩
    have indexEq : index = Fin.cast lengthEq.symm old.castSucc := by
      apply Fin.ext
      rfl
    have mappedOld :
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
          targetWellFormed).indexMap (Fin.cast lengthEq.symm old.castSucc) =
          old := by
      simpa only [lengthEq] using
        canonicalRootCollapse_old source wire keep targetWellFormed
          scopeRoot old
    have mappedCurrent :
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
          targetWellFormed).indexMap index = old :=
      (congrArg
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
          targetWellFormed).indexMap indexEq).trans mappedOld
    apply Fin.ext
    have mappedVal := congrArg Fin.val mappedCurrent
    have oldVal : old.val = index.val := rfl
    have oldTotal : index.val < source.val.exposedWires.length +
        source.val.hiddenWires.length := by omega
    simp only [Fin.val_cast] at mappedVal ⊢
    unfold VisualProof.Rule.WireSever.collapseLocal
    rw [dif_pos (by simpa only [Fin.val_cast] using oldTotal)]
    simp only [Fin.val_cast]
    omega

  · have indexVal : index.val = source.val.rootWires.length := by
      have bound' := (Fin.cast lengthEq index).isLt
      simp only [Fin.val_cast] at bound'
      omega
    let fresh := Fin.cast lengthEq.symm
      (Fin.last source.val.rootWires.length)
    have indexEq : index = fresh := by
      apply Fin.ext
      exact indexVal
    apply Fin.ext
    have mappedFresh := congrArg
      (fun candidate =>
        (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire keep
          targetWellFormed).indexMap candidate) indexEq
    have mappedFreshVal := congrArg Fin.val mappedFresh
    have indexEqVal := congrArg Fin.val indexEq
    have freshVal : fresh.val = source.val.rootWires.length := by
      simp [fresh]
    unfold VisualProof.Rule.WireSever.collapseLocal
    rw [dif_neg (by
      simp only [Fin.val_cast]
      omega)]
    simp only [Fin.val_cast]
    omega

theorem targetRootCollapse_factor
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.checked.val.diagram.wires wire).scope =
        source.checked.val.diagram.root)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    let canonical := canonicalOpen source.checked wire keep targetWellFormed
    let canonicalCollapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse
      source.checked wire keep targetWellFormed
    let sourceLength : source.checked.val.rootWires.length =
      source.checked.val.exposedWires.length +
        source.checked.val.hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let canonicalLength : canonical.val.rootWires.length =
      source.checked.val.exposedWires.length +
        (source.checked.val.hiddenWires.length + 1) :=
      (canonicalRootWires_length source.checked wire keep scopeRoot).trans
        (congrArg (fun count => count + 1) sourceLength)
    let fresh := Fin.cast
      (canonicalRootWires_length source.checked wire keep scopeRoot).symm
      (Fin.last source.checked.val.rootWires.length)
    let joined := Fin.cast sourceLength (canonicalCollapse.indexMap fresh)
    ∀ index,
      Fin.cast sourceLength
          ((targetRootCollapse source wire keep boundary
            targetWellFormed).indexMap index) =
        VisualProof.Rule.WireSever.collapseLocal
          source.checked.val.exposedWires.length
          source.checked.val.hiddenWires.length joined
          (Fin.cast canonicalLength
            (rootCoordinateEquiv source wire keep boundary targetWellFormed
              reflects index)) := by
  dsimp only
  intro index
  let actualCollapse := targetRootCollapse source wire keep boundary
    targetWellFormed
  let canonicalCollapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse
    source.checked wire keep targetWellFormed
  let coordinate := rootCoordinateEquiv source wire keep boundary
    targetWellFormed reflects
  have coordinateSpec := rootCoordinateEquiv_spec source wire keep boundary
    targetWellFormed reflects index
  have collapseNormalized := rootNormalization_collapse source wire keep
    boundary targetWellFormed
      ((separatedOpen source wire keep boundary
        targetWellFormed).val.rootWires.get index)
  have mappedEq : actualCollapse.indexMap index =
      canonicalCollapse.indexMap (coordinate index) := by
    apply Fin.ext
    apply (List.getElem_inj source.checked.val.rootWires_nodup).mp
    simpa only [List.get_eq_getElem] using
      (actualCollapse.get index).trans
        ((collapseNormalized.symm.trans
          (congrArg
            (VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire
              keep) coordinateSpec.symm)).trans
          (canonicalCollapse.get (coordinate index)).symm)
  rw [mappedEq]
  exact canonicalRootCollapse_factor source.checked wire keep targetWellFormed
    scopeRoot (coordinate index)

theorem canonicalRoot
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.val.diagram.wires wire).scope = source.val.diagram.root) :
    let target := canonicalOpen source wire keep targetWellFormed
    Rule.WireSever source.elaborate
      (target.elaborate.castArity
        (VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.val wire keep)) := by
  dsimp only
  let target := canonicalOpen source wire keep targetWellFormed
  obtain ⟨sourceItems, sourceItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete source
  obtain ⟨targetItems, targetItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete target
  let collapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse source wire
    keep targetWellFormed
  have sequence := severCompileSiteItems_of_nodes_children
    source.val.diagram wire keep target.val.rootWires source.val.rootWires
    collapse Concrete.Elaboration.BinderContext.empty source.val.diagram.root
    source.val.diagram.regionCount source.val.rootWires_nodup
    source.property.diagram_well_formed.wire_endpoints_are_disjoint (by
      intro childRels child childBinders member
      have parent :=
        (Concrete.Elaboration.mem_localOccurrences_child source.val.diagram
          source.val.diagram.root child).mp member
      have childNotRoot :
          ¬ source.val.diagram.Encloses child source.val.diagram.root :=
        Concrete.Elaboration.checked_direct_child_not_encloses_parent
          source.property.diagram_well_formed parent
      have targetRootExact :=
        Concrete.Elaboration.openRootWires_exact target.property
      have sourceRootExact :=
        Concrete.Elaboration.openRootWires_exact source.property
      exact compileRegion_collapse_of_not_encloses source.val.diagram wire keep
        source.property.diagram_well_formed target.property.diagram_well_formed
        source.val.diagram.regionCount child target.val.rootWires
        source.val.rootWires collapse childBinders (by
          simpa only [scopeRoot] using childNotRoot)
        (targetRootExact.extend_child target.property.diagram_well_formed parent)
        (sourceRootExact.extend_child source.property.diagram_well_formed parent))
  have targetItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.severWireRaw source.val.diagram wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw source.val.diagram wire keep)
            source.val.diagram.regionCount)
          target.val.rootWires Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences
            (Concrete.severWireRaw source.val.diagram wire keep)
            source.val.diagram.root) = some targetItems := by
    simpa [target, canonicalOpen] using targetItemsCompiled
  have mappedTarget := congrArg
    (Option.map (ItemSeq.renameWires collapse.indexMap)) targetItemsCompiled'
  have sourceSome : some sourceItems =
      some (targetItems.renameWires collapse.indexMap) := by
    exact sourceItemsCompiled.symm.trans
      (sequence.trans (mappedTarget.trans (by rfl)))
  have itemsEq : sourceItems =
      targetItems.renameWires collapse.indexMap :=
    Option.some.inj sourceSome
  obtain ⟨sourceBody, sourceRootCompiled, sourceElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation source
  have sourceItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith? source.val.diagram
          (Concrete.Elaboration.compileRegion? source.val.diagram
            source.val.diagram.regionCount)
          (source.val.exposedWires ++ source.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences source.val.diagram
            source.val.diagram.root) = some sourceItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using sourceItemsCompiled
  have sourceBodyEq : source.elaborate.body =
      Concrete.Elaboration.finishRoot source.val.exposedWires
        source.val.hiddenWires sourceItems := by
    rw [sourceElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at sourceRootCompiled
    rw [sourceItemsCompiled'] at sourceRootCompiled
    exact Option.some.inj sourceRootCompiled.symm
  obtain ⟨targetBody, targetRootCompiled, targetElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation target
  have targetItemsCompiled'' :
      Concrete.Elaboration.compileOccurrencesWith? target.val.diagram
          (Concrete.Elaboration.compileRegion? target.val.diagram
            target.val.diagram.regionCount)
          (target.val.exposedWires ++ target.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences target.val.diagram
            target.val.diagram.root) = some targetItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using targetItemsCompiled
  have targetBodyEq : target.elaborate.body =
      Concrete.Elaboration.finishRoot target.val.exposedWires
        target.val.hiddenWires targetItems := by
    rw [targetElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at targetRootCompiled
    rw [targetItemsCompiled''] at targetRootCompiled
    exact Option.some.inj targetRootCompiled.symm
  have externalEq : target.val.exposedWires.length =
      source.val.exposedWires.length := by
    have equality := congrArg List.length
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_exposedWires source.val wire keep)
    change target.val.exposedWires.length =
      (source.val.exposedWires.map Fin.castSucc).length at equality
    exact equality.trans (List.length_map (as := source.val.exposedWires)
      Fin.castSucc)
  have localEq : target.val.hiddenWires.length =
      source.val.hiddenWires.length + 1 := by
    have equality := congrArg List.length
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.val wire keep)
    rw [if_pos scopeRoot.symm] at equality
    change target.val.hiddenWires.length =
      (source.val.hiddenWires.map Fin.castSucc ++
        [Fin.last source.val.diagram.wireCount]).length at equality
    calc
      _ = _ := equality
      _ = source.val.hiddenWires.length + 1 := by
        rw [List.length_append, List.length_map]
        rfl
  let sourceLength : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let targetSourceLength : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let targetLength : target.val.rootWires.length =
      source.val.exposedWires.length + (source.val.hiddenWires.length + 1) :=
    targetSourceLength.trans
      ((congrArg (fun count => count + target.val.hiddenWires.length)
        externalEq).trans
      (congrArg (fun count => source.val.exposedWires.length + count) localEq))
  let external : FiniteEquiv (Fin target.val.exposedWires.length)
      (Fin source.val.exposedWires.length) := {
    toFun := VisualProof.Refinement.Implementation.WireSever.severExposedIndex source.val wire keep
    invFun := Fin.cast externalEq.symm
    left_inv := by intro index; apply Fin.ext; rfl
    right_inv := by intro index; apply Fin.ext; rfl
  }
  let localEquiv : FiniteEquiv (Fin target.val.hiddenWires.length)
      (Fin (source.val.hiddenWires.length + 1)) :=
    FiniteEquiv.finCast localEq
  have rootWireEq : Concrete.Elaboration.castFinEquiv targetSourceLength
        targetLength (extendWireEquiv external localEquiv) =
      FiniteEquiv.refl (Fin target.val.rootWires.length) := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    let split := Fin.cast targetSourceLength index
    have preservesValue :
        (extendWireEquiv external localEquiv split).val = split.val := by
      refine Fin.addCases (motive := fun split =>
        (extendWireEquiv external localEquiv split).val = split.val)
        (fun outerIndex => ?_) (fun localIndex => ?_) split
      · simp [external, localEquiv, VisualProof.Refinement.Implementation.WireSever.severExposedIndex,
          FiniteEquiv.finCast]
      · simp [external, localEquiv, VisualProof.Refinement.Implementation.WireSever.severExposedIndex,
          FiniteEquiv.finCast, externalEq]
    exact preservesValue
  let separate : ItemSeq
      (source.val.exposedWires.length +
        (source.val.hiddenWires.length + 1)) [] :=
    targetItems.castWiresEq targetLength
  let targetBodyIsoRaw : RegionIso external []
      (Concrete.Elaboration.finishRoot target.val.exposedWires
        target.val.hiddenWires targetItems)
      (.mk (source.val.hiddenWires.length + 1) separate) := by
    unfold Concrete.Elaboration.finishRoot separate
    apply Concrete.Elaboration.regionIso_of_cast targetSourceLength
      targetLength external localEquiv targetItems targetItems
    rw [rootWireEq]
    exact ItemSeqIso.refl targetItems
  have targetBodyIso : RegionIso external [] target.elaborate.body
      (.mk (source.val.hiddenWires.length + 1) separate) := by
    rw [targetBodyEq]
    exact targetBodyIsoRaw
  let canonicalLength := canonicalRootWires_length source wire keep scopeRoot
  let sourceRootLength : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let fresh := Fin.cast canonicalLength.symm
    (Fin.last source.val.rootWires.length)
  let joined := Fin.cast sourceRootLength (collapse.indexMap fresh)
  let before : Region source.val.exposedWires.length [] :=
    .mk source.val.hiddenWires.length
      (separate.renameWires
        (VisualProof.Rule.WireSever.collapseLocal
          source.val.exposedWires.length source.val.hiddenWires.length joined))
  have beforeEq : source.elaborate.body = before := by
    rw [sourceBodyEq]
    unfold Concrete.Elaboration.finishRoot before separate
    apply congrArg (Region.mk source.val.hiddenWires.length)
    rw [itemsEq]
    simp only [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_comp]
    refine (ItemSeq.renameWires_comp targetItems collapse.indexMap
      (Fin.cast sourceLength)).trans ?_
    apply congrArg (fun wireMap => targetItems.renameWires wireMap)
    funext index
    exact canonicalRootCollapse_factor source wire keep targetWellFormed
      scopeRoot index
  let after : Region source.val.exposedWires.length [] :=
    .mk (source.val.hiddenWires.length + 1) separate
  let occurrence : Occurrence before source.elaborate := {
    interface := source.elaborate
    context := .hole
    host_iso := {
      external := FiniteEquiv.refl _
      boundary := fun _ => rfl
      body := by
        rw [← beforeEq]
        exact RegionIso.refl source.elaborate.body
    }
  }
  let boundaryLength := VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.val wire keep
  let hostToTarget : OpenDiagramIso
      (occurrence.interface.withBody (occurrence.context.fill after))
      (target.elaborate.castArity boundaryLength) :=
    OpenDiagramIso.ofArityEq boundaryLength.symm external.symm (by
      intro position
      have boundaryClass :=
        VisualProof.Refinement.Implementation.WireSever.severBoundaryClass source.val wire keep position
      calc
        external.symm
            ((occurrence.interface.withBody
              (occurrence.context.fill after)).boundary position) =
            external.symm
              (external
                (target.elaborate.boundary
                  (Fin.cast boundaryLength.symm position))) := by
              apply congrArg external.symm
              simpa [target, canonicalOpen, occurrence, external] using
                boundaryClass.symm
        _ = target.elaborate.boundary
              (Fin.cast boundaryLength.symm position) :=
          external.left_inv _)
      (by simpa [occurrence, after] using targetBodyIso.symm)
  let targetIso : OpenDiagramIso
      (target.elaborate.castArity boundaryLength)
      (occurrence.interface.withBody (occurrence.context.fill after)) := by
    simpa [hostToTarget] using hostToTarget.symm
  exact Or.inl ⟨source.val.exposedWires.length, [], before, after,
    occurrence, targetIso,
    VisualProof.Rule.WireSever.Local.sever joined separate⟩

theorem root
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.checked.val.diagram.wires wire).scope =
        source.checked.val.diagram.root)
    (reflects : ∀ left right,
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) →
      Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right) :
    let target := separatedOpen source wire keep boundary targetWellFormed
    let targetLength : target.val.boundary.length = arity := by
      simp [target, separatedOpen]
    Rule.WireSever
      (source.checked.elaborate.castArity source.boundary_length)
      (target.elaborate.castArity targetLength) := by
  dsimp only
  let target := separatedOpen source wire keep boundary targetWellFormed
  let canonical := canonicalOpen source.checked wire keep targetWellFormed
  let collapse := targetRootCollapse source wire keep boundary targetWellFormed
  obtain ⟨sourceItems, sourceItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete source.checked
  obtain ⟨targetItems, targetItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete target
  have sequence := severCompileSiteItems_of_nodes_children
    source.checked.val.diagram wire keep target.val.rootWires
    source.checked.val.rootWires collapse
    Concrete.Elaboration.BinderContext.empty
    source.checked.val.diagram.root source.checked.val.diagram.regionCount
    source.checked.val.rootWires_nodup
    source.checked.property.diagram_well_formed.wire_endpoints_are_disjoint (by
      intro childRels child childBinders member
      have parent :=
        (Concrete.Elaboration.mem_localOccurrences_child
          source.checked.val.diagram source.checked.val.diagram.root child).mp
          member
      have childNotRoot : ¬ source.checked.val.diagram.Encloses child
          source.checked.val.diagram.root :=
        Concrete.Elaboration.checked_direct_child_not_encloses_parent
          source.checked.property.diagram_well_formed parent
      have targetRootExact :=
        Concrete.Elaboration.openRootWires_exact target.property
      have sourceRootExact :=
        Concrete.Elaboration.openRootWires_exact source.checked.property
      exact compileRegion_collapse_of_not_encloses
        source.checked.val.diagram wire keep
        source.checked.property.diagram_well_formed targetWellFormed
        source.checked.val.diagram.regionCount child target.val.rootWires
        source.checked.val.rootWires collapse childBinders (by
          simpa only [scopeRoot] using childNotRoot)
        (targetRootExact.extend_child targetWellFormed parent)
        (sourceRootExact.extend_child
          source.checked.property.diagram_well_formed parent))
  have targetItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.severWireRaw source.checked.val.diagram wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw source.checked.val.diagram wire keep)
            source.checked.val.diagram.regionCount)
          target.val.rootWires Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences
            (Concrete.severWireRaw source.checked.val.diagram wire keep)
            source.checked.val.diagram.root) = some targetItems := by
    simpa [target, separatedOpen] using targetItemsCompiled
  have mappedTarget := congrArg
    (Option.map (ItemSeq.renameWires collapse.indexMap)) targetItemsCompiled'
  have sourceSome : some sourceItems =
      some (targetItems.renameWires collapse.indexMap) :=
    sourceItemsCompiled.symm.trans
      (sequence.trans (mappedTarget.trans (by rfl)))
  have itemsEq : sourceItems =
      targetItems.renameWires collapse.indexMap := Option.some.inj sourceSome
  obtain ⟨sourceBody, sourceRootCompiled, sourceElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation source.checked
  have sourceItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith?
          source.checked.val.diagram
          (Concrete.Elaboration.compileRegion? source.checked.val.diagram
            source.checked.val.diagram.regionCount)
          (source.checked.val.exposedWires ++ source.checked.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences source.checked.val.diagram
            source.checked.val.diagram.root) = some sourceItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using sourceItemsCompiled
  have sourceBodyEq : source.checked.elaborate.body =
      Concrete.Elaboration.finishRoot source.checked.val.exposedWires
        source.checked.val.hiddenWires sourceItems := by
    rw [sourceElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at sourceRootCompiled
    rw [sourceItemsCompiled'] at sourceRootCompiled
    exact Option.some.inj sourceRootCompiled.symm
  obtain ⟨targetBody, targetRootCompiled, targetElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation target
  have targetItemsCompiled'' :
      Concrete.Elaboration.compileOccurrencesWith? target.val.diagram
          (Concrete.Elaboration.compileRegion? target.val.diagram
            target.val.diagram.regionCount)
          (target.val.exposedWires ++ target.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences target.val.diagram
            target.val.diagram.root) = some targetItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using targetItemsCompiled
  have targetBodyEq : target.elaborate.body =
      Concrete.Elaboration.finishRoot target.val.exposedWires
        target.val.hiddenWires targetItems := by
    rw [targetElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at targetRootCompiled
    rw [targetItemsCompiled''] at targetRootCompiled
    exact Option.some.inj targetRootCompiled.symm
  have canonicalExternalEq : canonical.val.exposedWires.length =
      source.checked.val.exposedWires.length := by
    have equality := congrArg List.length
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_exposedWires source.checked.val wire keep)
    change canonical.val.exposedWires.length =
      (source.checked.val.exposedWires.map Fin.castSucc).length at equality
    exact equality.trans (List.length_map
      (as := source.checked.val.exposedWires) Fin.castSucc)
  have canonicalLocalEq : canonical.val.hiddenWires.length =
      source.checked.val.hiddenWires.length + 1 := by
    have equality := congrArg List.length
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_hiddenWires source.checked.val wire keep)
    rw [if_pos scopeRoot.symm] at equality
    change canonical.val.hiddenWires.length =
      (source.checked.val.hiddenWires.map Fin.castSucc ++
        [Fin.last source.checked.val.diagram.wireCount]).length at equality
    calc
      _ = _ := equality
      _ = source.checked.val.hiddenWires.length + 1 := by
        rw [List.length_append, List.length_map]
        rfl
  let external :=
    (rootExternalEquiv source wire keep boundary targetWellFormed reflects).trans
      (FiniteEquiv.finCast canonicalExternalEq)
  let localEquiv :=
    (rootLocalEquiv source wire keep boundary targetWellFormed reflects).trans
      (FiniteEquiv.finCast canonicalLocalEq)
  let targetRootEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let sourceRootEq : source.checked.val.rootWires.length =
      source.checked.val.exposedWires.length +
        source.checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let canonicalLength : canonical.val.rootWires.length =
      source.checked.val.exposedWires.length +
        (source.checked.val.hiddenWires.length + 1) :=
    (canonicalRootWires_length source.checked wire keep scopeRoot).trans
      (congrArg (fun count => count + 1) sourceRootEq)
  let targetIntrinsic := targetItems.castWiresEq targetRootEq
  let separate := targetIntrinsic.renameWires
    (extendWireEquiv external localEquiv)
  let after : Region source.checked.val.exposedWires.length [] :=
    .mk (source.checked.val.hiddenWires.length + 1) separate
  have targetBodyIso : RegionIso external [] target.elaborate.body after := by
    rw [targetBodyEq]
    unfold Concrete.Elaboration.finishRoot after separate targetIntrinsic
    exact RegionIso.mk localEquiv
      (ItemSeqIso.renameWiresEquiv _ (extendWireEquiv external localEquiv))
  let canonicalCollapse := VisualProof.Refinement.Implementation.WireSever.severWireRawOpen_rootCollapse
    source.checked wire keep targetWellFormed
  let canonicalFresh := Fin.cast
    (canonicalRootWires_length source.checked wire keep scopeRoot).symm
    (Fin.last source.checked.val.rootWires.length)
  let joined := Fin.cast sourceRootEq
    (canonicalCollapse.indexMap canonicalFresh)
  let before : Region source.checked.val.exposedWires.length [] :=
    .mk source.checked.val.hiddenWires.length
      (separate.renameWires
        (VisualProof.Rule.WireSever.collapseLocal
          source.checked.val.exposedWires.length
          source.checked.val.hiddenWires.length joined))
  have transportEq (index : Fin target.val.rootWires.length) :
      Fin.cast canonicalLength
          (rootCoordinateEquiv source wire keep boundary targetWellFormed
            reflects index) =
        extendWireEquiv external localEquiv (Fin.cast targetRootEq index) := by
    let split := Fin.cast targetRootEq index
    generalize splitEq : split = position
    revert splitEq
    refine Fin.addCases (fun externalIndex splitEq => ?_)
      (fun localIndex splitEq => ?_) position
    · apply Fin.ext
      simp [rootCoordinateEquiv, external, localEquiv, split, splitEq,
        FiniteEquiv.finCast, extendWireEquiv]
      rw [Fin.addCases_left, Fin.addCases_left]
      simp only [Fin.val_castAdd, Fin.val_cast]
    · apply Fin.ext
      simp [rootCoordinateEquiv, external, localEquiv, split, splitEq,
        FiniteEquiv.finCast, extendWireEquiv]
      rw [Fin.addCases_right, Fin.addCases_right]
      simp only [Fin.val_natAdd, Fin.val_cast]
      rw [canonicalExternalEq]
  have beforeEq : source.checked.elaborate.body = before := by
    rw [sourceBodyEq]
    unfold Concrete.Elaboration.finishRoot before separate targetIntrinsic
    apply congrArg (Region.mk source.checked.val.hiddenWires.length)
    rw [itemsEq]
    simp only [ItemSeq.castWiresEq_eq_renameWires]
    refine (ItemSeq.renameWires_comp targetItems collapse.indexMap
      (Fin.cast sourceRootEq)).trans ?_
    rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
    apply congrArg (fun wireMap => targetItems.renameWires wireMap)
    funext index
    exact (targetRootCollapse_factor source wire keep boundary targetWellFormed
      scopeRoot reflects index).trans
        (congrArg
          (VisualProof.Rule.WireSever.collapseLocal
            source.checked.val.exposedWires.length
            source.checked.val.hiddenWires.length joined)
          (transportEq index))
  let targetLength : target.val.boundary.length = arity := by
    simp [target, separatedOpen]
  let targetToSource : target.val.boundary.length =
      source.checked.val.boundary.length :=
    targetLength.trans source.boundary_length.symm
  let targetDiagram := reindexOpen target.elaborate targetToSource
  have baseStep : Rule.WireSever source.checked.elaborate targetDiagram := by
    let occurrence : Occurrence before source.checked.elaborate := {
      interface := source.checked.elaborate
      context := .hole
      host_iso := {
        external := FiniteEquiv.refl _
        boundary := fun _ => rfl
        body := by
          rw [← beforeEq]
          exact RegionIso.refl source.checked.elaborate.body
      }
    }
    let targetIso : OpenDiagramIso targetDiagram
        (occurrence.interface.withBody (occurrence.context.fill after)) := {
      external := external
      boundary := by
        intro position
        let actualPosition := Fin.cast source.boundary_length position
        have normalizedClass := rootExternalEquiv_boundaryClass source wire keep
          boundary targetWellFormed reflects actualPosition
        have canonicalClass := VisualProof.Refinement.Implementation.WireSever.severBoundaryClass
          source.checked.val wire keep position
        have combined :=
          (congrArg (FiniteEquiv.finCast canonicalExternalEq) normalizedClass).trans
            canonicalClass
        simpa [targetDiagram, reindexOpen, targetToSource, actualPosition,
          occurrence, external, canonicalOpen,
          Concrete.CheckedOpen.elaborate_boundary] using combined
      body := by
        simpa [targetDiagram, reindexOpen, occurrence, after] using targetBodyIso
    }
    exact Or.inl ⟨source.checked.val.exposedWires.length, [], before, after,
      occurrence, targetIso,
      VisualProof.Rule.WireSever.Local.sever joined separate⟩
  rw [show targetDiagram = target.elaborate.castArity targetToSource from
    reindexOpen_eq_castArity target.elaborate targetToSource] at baseStep
  have castStep := wireSever_castArity source.boundary_length baseStep
  rw [castArity_castArity] at castStep
  have targetProof : targetToSource.trans source.boundary_length =
      targetLength := Subsingleton.elim _ _
  simpa only [targetProof] using castStep

end VisualProof.Refinement.Implementation.WireSever
