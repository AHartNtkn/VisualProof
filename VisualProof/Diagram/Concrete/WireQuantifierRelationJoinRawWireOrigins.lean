import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawConstructionAtlasConformance

namespace VisualProof

namespace ConcreteWireQuantifier

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

/-- Occurrence-indexed origins of internal content wires.  `head` is the
current construction occurrence and `tail` advances through later accepted
occurrences; the position is the checked attachment's construction-order
internal-wire position. -/
inductive ConstructionWireOrigin :
    (steps : List (RelationJoinStep source dying content)) → Type
  | head {step rest}
      (position : Fin step.attachment.fragmentInternalWires.length) :
      ConstructionWireOrigin (step :: rest)
  | tail {step rest}
      (origin : ConstructionWireOrigin rest) :
      ConstructionWireOrigin (step :: rest)
  deriving DecidableEq

/-- Terminal raw wire origins: one surviving source wire, or one internal
content-wire position at an accepted construction occurrence. -/
abbrev FinalWireOrigin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :=
  { wire : source.val.WireId // wire ≠ dying } ⊕
    ConstructionWireOrigin result.steps

private theorem sourceWireCount_positive
    (dying : source.val.WireId) : 0 < source.val.wireCount :=
  Nat.zero_lt_of_lt dying.isLt

theorem sourceSurvivingWireCount_add_one
    (dying : source.val.WireId) :
    source.val.wireCount - 1 + 1 = source.val.wireCount := by
  have := sourceWireCount_positive dying
  omega

private def removedSourceWire : Fin (source.val.wireCount - 1 + 1) :=
  Fin.cast (sourceSurvivingWireCount_add_one dying).symm dying

/-- The surviving source wire at one direct singleton-deletion position. -/
def survivingSourceWireAt
    (position : Fin (source.val.wireCount - 1)) :
    { wire : source.val.WireId // wire ≠ dying } :=
  let restored := restoreFin (removedSourceWire (dying := dying)) position
  ⟨Fin.cast (sourceSurvivingWireCount_add_one dying) restored, by
    intro same
    apply restoreFin_ne (removedSourceWire (dying := dying)) position
    apply Fin.ext
    simpa [removedSourceWire] using congrArg Fin.val same⟩

/-- Direct singleton-deletion position of one surviving source wire. -/
def survivingSourceWirePosition
    (wire : { wire : source.val.WireId // wire ≠ dying }) :
    Fin (source.val.wireCount - 1) :=
  dropFin (removedSourceWire (dying := dying))
    (Fin.cast (sourceSurvivingWireCount_add_one dying).symm wire.1)
    (by
      intro same
      apply wire.2
      apply Fin.ext
      simpa [removedSourceWire] using congrArg Fin.val same)

@[simp] theorem survivingSourceWireAt_position
    (wire : { wire : source.val.WireId // wire ≠ dying }) :
    survivingSourceWireAt (dying := dying)
        (survivingSourceWirePosition (dying := dying) wire) = wire := by
  apply Subtype.ext
  apply Fin.ext
  simp [survivingSourceWireAt, survivingSourceWirePosition,
    removedSourceWire]

@[simp] theorem survivingSourceWirePosition_at
    (position : Fin (source.val.wireCount - 1)) :
    survivingSourceWirePosition (dying := dying)
        (survivingSourceWireAt (dying := dying) position) = position := by
  apply Fin.ext
  simp [survivingSourceWireAt, survivingSourceWirePosition,
    removedSourceWire]

private def allFinPosition (position : Fin count) :
    Fin (Data.Finite.allFin count).length :=
  Fin.cast (by simp [Data.Finite.allFin_eq_finRange]) position

@[simp] private theorem allFin_get_allFinPosition
    (position : Fin count) :
    (Data.Finite.allFin count).get (allFinPosition position) = position := by
  apply Fin.ext
  simp [allFinPosition, Data.Finite.allFin_eq_finRange,
    List.get_eq_getElem]

/-- Exact occurrence-order rows for internal content-wire origins. -/
def constructionWireOriginRows :
    (steps : List (RelationJoinStep source dying content)) →
      List (ConstructionWireOrigin steps)
  | [] => []
  | step :: rest =>
      (Data.Finite.allFin
          step.attachment.fragmentInternalWires.length).map
        ConstructionWireOrigin.head ++
      (constructionWireOriginRows rest).map ConstructionWireOrigin.tail

theorem constructionWireOriginRows_length
    (steps : List (RelationJoinStep source dying content)) :
    (constructionWireOriginRows steps).length =
      (steps.map fun step =>
        step.attachment.fragmentInternalWires.length).sum := by
  induction steps with
  | nil => rfl
  | cons step rest induction =>
      simp [constructionWireOriginRows, induction,
        Data.Finite.allFin_eq_finRange]

theorem constructionWireOriginRows_nodup
    (steps : List (RelationJoinStep source dying content)) :
    (constructionWireOriginRows steps).Nodup := by
  induction steps with
  | nil => simp [constructionWireOriginRows]
  | cons step rest induction =>
      rw [constructionWireOriginRows, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact (Data.Finite.allFin_nodup _).map _ (by
          intro left right different same
          exact different (ConstructionWireOrigin.head.inj same))
      · exact induction.map _ (by
          intro left right different same
          exact different (ConstructionWireOrigin.tail.inj same))
      · intro head headMember tail tailMember same
        rcases List.mem_map.mp headMember with ⟨position, _, rfl⟩
        rcases List.mem_map.mp tailMember with ⟨origin, _, rfl⟩
        contradiction

/-- A Type-valued exact landing in one wire-origin row list. -/
structure WireOriginLands
    (rows : List α) (origin : α) (position : Fin rows.length) : Type where
  exact : rows.get position = origin

private theorem listGet_injective_of_nodup [DecidableEq α]
    {rows : List α} (nodup : rows.Nodup) : Function.Injective rows.get := by
  intro left right same
  apply Fin.ext
  have valuesSame : rows[left.val]? = rows[right.val]? := by
    rw [List.getElem?_eq_getElem left.isLt,
      List.getElem?_eq_getElem right.isLt]
    exact congrArg some same
  exact (List.getElem?_inj left.isLt nodup).mp valuesSame

/-- Direct construction-order locator for an internal wire origin. -/
def locateConstructionWireOrigin :
    ∀ {steps : List (RelationJoinStep source dying content)}
      (origin : ConstructionWireOrigin steps),
      Σ position, WireOriginLands (constructionWireOriginRows steps)
        origin position
  | [], origin => nomatch origin
  | step :: rest, .head position => by
      let localPosition := allFinPosition position
      let rawTarget :=
        Fin.castAdd (constructionWireOriginRows rest).length localPosition
      let target : Fin (constructionWireOriginRows (step :: rest)).length :=
        Fin.cast (by simp [constructionWireOriginRows]) rawTarget
      exact ⟨target, ⟨by
        simp [constructionWireOriginRows, target, rawTarget]
        exact allFin_get_allFinPosition position⟩⟩
  | step :: rest, .tail origin => by
      let landing := locateConstructionWireOrigin origin
      let current := Data.Finite.allFin
        step.attachment.fragmentInternalWires.length
      let rawTarget :=
        Fin.natAdd current.length landing.1
      let target : Fin (constructionWireOriginRows (step :: rest)).length :=
        Fin.cast (by simp [constructionWireOriginRows, current]) rawTarget
      exact ⟨target, ⟨by
        simp [constructionWireOriginRows, target, rawTarget, current]
        exact landing.2.exact⟩⟩

/-- The sole terminal wire-origin row list, in checked construction order. -/
def finalWireOriginRows
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    List (FinalWireOrigin result) :=
  (Data.Finite.allFin (source.val.wireCount - 1)).map
      (fun position => Sum.inl (survivingSourceWireAt position)) ++
    (constructionWireOriginRows result.steps).map Sum.inr

theorem finalWireOriginRows_nodup
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    (finalWireOriginRows result).Nodup := by
  rw [finalWireOriginRows, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (Data.Finite.allFin_nodup _).map _ (by
      intro left right different same
      apply different
      have sourceSame := Sum.inl.inj same
      have positions := congrArg
        (survivingSourceWirePosition (dying := dying)) sourceSame
      simpa using positions)
  · exact (constructionWireOriginRows_nodup result.steps).map _ (by
      intro left right different same
      exact different (Sum.inr.inj same))
  · intro sourceRow sourceMember internalRow internalMember same
    rcases List.mem_map.mp sourceMember with ⟨position, _, rfl⟩
    rcases List.mem_map.mp internalMember with ⟨origin, _, rfl⟩
    contradiction

theorem RelationJoinConstructionTrace.boundWireCount_exact
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope) :
    final.val.wireCount = source.val.wireCount +
      (constructionWireOriginRows steps).length := by
  induction trace with
  | nil => simp [constructionWireOriginRows]
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      rw [step.checked_wireCount, induction,
        constructionWireOriginRows_length,
        constructionWireOriginRows_length]
      simp
      omega

/-- Exact terminal carrier count for the sole wire-origin row list. -/
theorem finalWireOriginRows_length
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    (finalWireOriginRows result).length =
      result.plainFinal.val.wireCount := by
  have boundCount := result.construction_trace.boundWireCount_exact
  have deletionCount := result.plainFinal_wireCount_add_one
  have sourcePositive := sourceWireCount_positive dying
  simp [finalWireOriginRows, Data.Finite.allFin_eq_finRange,
    constructionWireOriginRows_length] at ⊢
  rw [constructionWireOriginRows_length] at boundCount
  omega

/-- Constructive exact locator into the sole terminal wire-origin rows. -/
def locateFinalWireOrigin
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    Σ position, WireOriginLands (finalWireOriginRows result)
      origin position := by
  cases origin with
  | inl wire =>
      let localPosition := allFinPosition
        (survivingSourceWirePosition (dying := dying) wire)
      let rawTarget :=
        Fin.castAdd (constructionWireOriginRows result.steps).length
          localPosition
      let target : Fin (finalWireOriginRows result).length :=
        Fin.cast (by simp [finalWireOriginRows]) rawTarget
      exact ⟨target, ⟨by
        simp [finalWireOriginRows, target, rawTarget]
        change survivingSourceWireAt
            ((Data.Finite.allFin (source.val.wireCount - 1)).get localPosition) =
          wire
        rw [show
          (Data.Finite.allFin (source.val.wireCount - 1)).get localPosition =
            survivingSourceWirePosition (dying := dying) wire by
          exact allFin_get_allFinPosition _]
        exact survivingSourceWireAt_position wire⟩⟩
  | inr internal =>
      let landing := locateConstructionWireOrigin internal
      let sourceRows := Data.Finite.allFin (source.val.wireCount - 1)
      let rawTarget :=
        Fin.natAdd sourceRows.length landing.1
      let target : Fin (finalWireOriginRows result).length :=
        Fin.cast (by simp [finalWireOriginRows, sourceRows]) rawTarget
      exact ⟨target, ⟨by
        simp [finalWireOriginRows, target, rawTarget, sourceRows]
        exact landing.2.exact⟩⟩

/-- Direct terminal wire-origin equivalence: forward is exact row lookup and
inverse is the constructive Sigma locator target. -/
def finalWireOriginEquiv
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters) :
    Data.Finite.FiniteEquiv result.plainFinal.val.WireId
      (FinalWireOrigin result) where
  toFun target :=
    (finalWireOriginRows result).get
      (Fin.cast (finalWireOriginRows_length result).symm target)
  invFun origin :=
    Fin.cast (finalWireOriginRows_length result)
      (locateFinalWireOrigin result origin).1
  left_inv target := by
    let forwardPosition : Fin (finalWireOriginRows result).length :=
      Fin.cast (finalWireOriginRows_length result).symm target
    let landing := locateFinalWireOrigin result
      ((finalWireOriginRows result).get forwardPosition)
    have positionExact : landing.1 = forwardPosition :=
      listGet_injective_of_nodup (finalWireOriginRows_nodup result)
        landing.2.exact
    apply Fin.ext
    simpa [landing, forwardPosition] using congrArg Fin.val positionExact
  right_inv origin := by
    change (finalWireOriginRows result).get
        (Fin.cast (finalWireOriginRows_length result).symm
          (Fin.cast (finalWireOriginRows_length result)
            (locateFinalWireOrigin result origin).1)) = origin
    have targetExact :
        Fin.cast (finalWireOriginRows_length result).symm
            (Fin.cast (finalWireOriginRows_length result)
              (locateFinalWireOrigin result origin).1) =
          (locateFinalWireOrigin result origin).1 := by
      apply Fin.ext
      rfl
    rw [targetExact]
    exact (locateFinalWireOrigin result origin).2.exact

end ConcreteWireQuantifier

end VisualProof
