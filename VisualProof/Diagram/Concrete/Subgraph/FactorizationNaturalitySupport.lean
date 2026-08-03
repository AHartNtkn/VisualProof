import VisualProof.Diagram.Concrete.Subgraph.FactorizationRenaming

namespace VisualProof

namespace ConcreteElaboration.WireValues

private def append
    (left : ConcreteElaboration.WireValues pre leftSigs)
    (right : ConcreteElaboration.WireValues pre rightSigs) :
    ConcreteElaboration.WireValues pre (leftSigs ++ rightSigs) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (append tail right)

end ConcreteElaboration.WireValues

namespace InsertionCompilation
namespace NaturalityInternal

def appendLeftIds
    (diagram : ConcreteDiagram definitionCount)
    (rightIds : List diagram.WireId) :
    {leftIds : List diagram.WireId} → {sig : Sig} →
      Var (leftIds.map fun wire => (diagram.wires wire).sig) sig →
        Var ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig) sig
  | [], _, value => nomatch value
  | _ :: _, _, .here => .here
  | _ :: tail, _, .there value =>
      .there (appendLeftIds diagram rightIds (leftIds := tail) value)

private def mapAppendSigsExact
    (diagram : ConcreteDiagram definitionCount) :
    (leftIds rightIds : List diagram.WireId) →
      (leftIds ++ rightIds).map (fun wire => (diagram.wires wire).sig) =
        leftIds.map (fun wire => (diagram.wires wire).sig) ++
          rightIds.map (fun wire => (diagram.wires wire).sig)
  | [], _ => rfl
  | head :: tail, rightIds =>
      congrArg (List.cons (diagram.wires head).sig)
        (mapAppendSigsExact diagram tail rightIds)

private theorem castVar_cons_here
    (same : left = right) :
    congrArg (List.cons head) same ▸
        (Var.here : Var (head :: left) head) =
      (Var.here : Var (head :: right) head) := by
  cases same
  rfl

private theorem castVar_cons_there
    (same : left = right)
    (value : Var left signature) :
    congrArg (List.cons head) same ▸
        (Var.there value : Var (head :: left) signature) =
      (Var.there (same ▸ value) : Var (head :: right) signature) := by
  cases same
  rfl

/-- Identifier-level left embedding is exactly ordinary typed left embedding
after reindexing the mapped append equality. -/
theorem appendLeftIds_reindex
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (leftIds.map fun wire => (diagram.wires wire).sig) sig) :
    mapAppendSigsExact diagram leftIds rightIds ▸
        (appendLeftIds diagram rightIds value) =
      Var.appendLeft value
        (rightIds.map fun wire => (diagram.wires wire).sig) := by
  induction leftIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          exact castVar_cons_here
            (mapAppendSigsExact diagram tail rightIds)
      | there value =>
          change
            congrArg (List.cons (diagram.wires head).sig)
                (mapAppendSigsExact diagram tail rightIds) ▸
                Var.there (appendLeftIds diagram rightIds value) =
              Var.there (Var.appendLeft value
                (rightIds.map fun wire => (diagram.wires wire).sig))
          calc
            _ = Var.there
                  (mapAppendSigsExact diagram tail rightIds ▸
                    appendLeftIds diagram rightIds value) :=
              castVar_cons_there
                (mapAppendSigsExact diagram tail rightIds) _
            _ = _ := congrArg Var.there (induction value)

def castPacked
    (same : source = target) :
    PackedVar source → PackedVar target
  | ⟨sig, value⟩ => ⟨sig, same ▸ value⟩

def packedOrigin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) :
    PackedVar
        (ids.map (fun wire => (diagram.wires wire).sig)) →
      diagram.WireId
  | ⟨_, value⟩ =>
      ConcreteElaboration.WireContext.origin diagram ids value

private def varOffset : Var context sig → Nat
  | .here => 0
  | .there value => varOffset value + 1

def packedOffset : PackedVar context → Nat
  | ⟨_, value⟩ => varOffset value

theorem packedOffset_castPacked
    (same : source = target)
    (value : PackedVar source) :
    packedOffset (castPacked same value) =
      packedOffset value := by
  cases same
  rfl

theorem packedOrigin_get?
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (value :
      PackedVar
        (ids.map (fun wire => (diagram.wires wire).sig))) :
    ids[packedOffset value]? =
      some (packedOrigin diagram ids value) := by
  rcases value with ⟨sig, value⟩
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there tailValue =>
          simpa [packedOffset, varOffset, packedOrigin,
            ConcreteElaboration.WireContext.origin] using
              induction tailValue

private def appendLeftPacked
    (suffixSigs : List Sig) :
    PackedVar prefixContext →
      PackedVar (prefixContext ++ suffixSigs)
  | ⟨sig, value⟩ => ⟨sig, Var.appendLeft value suffixSigs⟩

private def appendRightPacked
    (prefixSigs : List Sig) :
    PackedVar suffixContext →
      PackedVar (prefixSigs ++ suffixContext)
  | ⟨sig, value⟩ => ⟨sig, Var.appendRight prefixSigs value⟩

private theorem varOffset_appendLeft
    (value : Var context sig)
    (suffix : List Sig) :
    varOffset (Var.appendLeft value suffix) = varOffset value := by
  induction value with
  | here => rfl
  | there value induction =>
      simp only [Var.appendLeft, varOffset, induction]

private theorem varOffset_appendRight
    (leading : List Sig)
    (value : Var context sig) :
    varOffset (Var.appendRight leading value) =
      leading.length + varOffset value := by
  induction leading with
  | nil => simp [Var.appendRight]
  | cons head tail induction =>
      simp only [Var.appendRight, varOffset, List.length_cons, induction]
      omega

private theorem packedOffset_appendLeft
    (value : PackedVar context)
    (suffix : List Sig) :
    packedOffset (appendLeftPacked suffix value) =
      packedOffset value := by
  rcases value with ⟨sig, value⟩
  exact varOffset_appendLeft value suffix

private theorem packedOffset_appendRight
    (leading : List Sig)
    (value : PackedVar context) :
    packedOffset (appendRightPacked leading value) =
      leading.length + packedOffset value := by
  rcases value with ⟨sig, value⟩
  exact varOffset_appendRight leading value

private theorem packedOrigin_cast_appendLeft_of_allocation
    (sourceDiagram : ConcreteDiagram sourceDefinitionCount)
    (targetDiagram : ConcreteDiagram targetDefinitionCount)
    (sourceIds : List sourceDiagram.WireId)
    (targetIds suffixIds : List targetDiagram.WireId)
    (wireMap : sourceDiagram.WireId → targetDiagram.WireId)
    (allocation :
      targetIds = sourceIds.map wireMap ++ suffixIds)
    (suffixSigs : List Sig)
    (sigs :
      targetIds.map (fun wire => (targetDiagram.wires wire).sig) =
        sourceIds.map (fun wire => (sourceDiagram.wires wire).sig) ++
          suffixSigs)
    (value : PackedVar
      (sourceIds.map fun wire => (sourceDiagram.wires wire).sig)) :
    packedOrigin targetDiagram targetIds
        (castPacked sigs.symm (appendLeftPacked suffixSigs value)) =
      wireMap (packedOrigin sourceDiagram sourceIds value) := by
  let mapped := castPacked sigs.symm (appendLeftPacked suffixSigs value)
  have mappedOffset : packedOffset mapped = packedOffset value := by
    exact
      (packedOffset_castPacked sigs.symm
        (appendLeftPacked suffixSigs value)).trans
        (packedOffset_appendLeft value suffixSigs)
  have targetLookup := packedOrigin_get? targetDiagram targetIds mapped
  have sourceLookup := packedOrigin_get? sourceDiagram sourceIds value
  obtain ⟨offsetBound, _⟩ :=
    List.getElem?_eq_some_iff.mp sourceLookup
  have allocationAt :=
    congrArg (fun ids => ids[packedOffset value]?) allocation
  change
    targetIds[packedOffset value]? =
      (sourceIds.map wireMap ++ suffixIds)[packedOffset value]?
    at allocationAt
  rw [List.getElem?_append_left
        (by simpa only [List.length_map] using offsetBound),
      List.getElem?_map, sourceLookup] at allocationAt
  simp only [Option.map_some] at allocationAt
  have targetAt :
      targetIds[packedOffset value]? =
        some (packedOrigin targetDiagram targetIds mapped) :=
    (congrArg (fun offset => targetIds[offset]?) mappedOffset).symm.trans
      targetLookup
  exact Option.some.inj (targetAt.symm.trans allocationAt)

private theorem packedOrigin_cast_appendRight_of_allocation
    (sourceDiagram : ConcreteDiagram sourceDefinitionCount)
    (targetDiagram : ConcreteDiagram targetDefinitionCount)
    (sourceIds : List sourceDiagram.WireId)
    (targetIds leadingIds : List targetDiagram.WireId)
    (wireMap : sourceDiagram.WireId → targetDiagram.WireId)
    (allocation :
      targetIds = leadingIds ++ sourceIds.map wireMap)
    (leadingSigs : List Sig)
    (sigs :
      targetIds.map (fun wire => (targetDiagram.wires wire).sig) =
        leadingSigs ++
          sourceIds.map (fun wire => (sourceDiagram.wires wire).sig))
    (leadingLength : leadingIds.length = leadingSigs.length)
    (value : PackedVar
      (sourceIds.map fun wire => (sourceDiagram.wires wire).sig)) :
    packedOrigin targetDiagram targetIds
        (castPacked sigs.symm (appendRightPacked leadingSigs value)) =
      wireMap (packedOrigin sourceDiagram sourceIds value) := by
  let mapped := castPacked sigs.symm
    (appendRightPacked leadingSigs value)
  have mappedOffset :
      packedOffset mapped = leadingIds.length + packedOffset value := by
    calc
      packedOffset mapped =
          leadingSigs.length + packedOffset value :=
        (packedOffset_castPacked sigs.symm
          (appendRightPacked leadingSigs value)).trans
          (packedOffset_appendRight leadingSigs value)
      _ = leadingIds.length + packedOffset value := by
        rw [leadingLength]
  have targetLookup := packedOrigin_get? targetDiagram targetIds mapped
  have sourceLookup := packedOrigin_get? sourceDiagram sourceIds value
  have allocationAt :=
    congrArg
      (fun ids => ids[leadingIds.length + packedOffset value]?)
      allocation
  change
    targetIds[leadingIds.length + packedOffset value]? =
      (leadingIds ++ sourceIds.map wireMap)[
        leadingIds.length + packedOffset value]?
    at allocationAt
  rw [List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, List.getElem?_map, sourceLookup]
    at allocationAt
  simp only [Option.map_some] at allocationAt
  have targetAt :
      targetIds[leadingIds.length + packedOffset value]? =
        some (packedOrigin targetDiagram targetIds mapped) :=
    (congrArg (fun offset => targetIds[offset]?) mappedOffset).symm.trans
      targetLookup
  exact Option.some.inj (targetAt.symm.trans allocationAt)

def wireValue
    (values : ConcreteElaboration.WireValues pre sigs) :
    {sig : Sig} → Var sigs sig → pre.Domain sig
  | _, value =>
      match values, value with
      | .cons head _, .here => head
      | .cons _ tail, .there rest => wireValue tail rest

private theorem wireValue_appendLeft
    (left : ConcreteElaboration.WireValues pre leftSigs)
    (right : ConcreteElaboration.WireValues pre rightSigs)
    {sig : Sig} (value : Var leftSigs sig) :
    wireValue (ConcreteElaboration.WireValues.append left right)
        (Var.appendLeft value rightSigs) =
      wireValue left value := by
  induction left with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

private theorem wireValue_appendRight
    (left : ConcreteElaboration.WireValues pre leftSigs)
    (right : ConcreteElaboration.WireValues pre rightSigs)
    {sig : Sig} (value : Var rightSigs sig) :
    wireValue (ConcreteElaboration.WireValues.append left right)
        (Var.appendRight leftSigs value) =
      wireValue right value := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      exact induction

private theorem packedOrigin_transport_ids
    (diagram : ConcreteDiagram definitionCount)
    {leftIds rightIds : List diagram.WireId}
    (same : leftIds = rightIds)
    (value :
      PackedVar
        (rightIds.map fun wire => (diagram.wires wire).sig)) :
    packedOrigin diagram leftIds
        (castPacked
          (congrArg
            (List.map fun wire => (diagram.wires wire).sig)
            same).symm
          value) =
      packedOrigin diagram rightIds value := by
  cases same
  rfl

theorem wireValues_cast_cancel
    (same : source = target)
    (values : ConcreteElaboration.WireValues pre source) :
    same.symm ▸ (same ▸ values) = values := by
  cases same
  rfl

theorem wireValue_cast
    (same : source = target)
    (values : ConcreteElaboration.WireValues pre source)
    {sig : Sig}
    (value : Var source sig) :
    wireValue (same ▸ values) (same ▸ value) =
      wireValue values value := by
  cases same
  rfl

theorem appendLeftIds_origin
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (leftIds.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram
        (leftIds ++ rightIds)
        (appendLeftIds diagram rightIds value) =
      ConcreteElaboration.WireContext.origin diagram leftIds value := by
  induction leftIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

theorem extendEnvironment_outer
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value : Var context.sigs sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (ConcreteElaboration.appendRightVar diagram
          (diagram.wiresAt region) value) =
      outerEnv sig value :=
  ConcreteElaboration.extendEnvironment_appendRightVar diagram context
    region values outerEnv value

private theorem extendEnvironmentFor_outer
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (values : ConcreteElaboration.WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    {sig : Sig}
    (value : Var
      (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.extendEnvironmentFor diagram outerIds localIds
        values outerEnv sig
        (ConcreteElaboration.appendRightVar diagram localIds value) =
      outerEnv sig value := by
  induction localIds with
  | nil =>
      cases values
      rfl
  | cons head tail induction =>
      cases values with
      | cons headValue tailValues =>
          exact induction tailValues

private theorem extendEnvironmentFor_local
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (values : ConcreteElaboration.WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    {sig : Sig}
    (value : Var
      (localIds.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.extendEnvironmentFor diagram outerIds localIds
        values outerEnv sig
        (appendLeftIds diagram outerIds value) =
      wireValue values value := by
  induction localIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases values with
      | cons headValue tailValues =>
          cases value with
          | here => rfl
          | there rest =>
              exact induction tailValues rest

theorem extendEnvironment_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value :
      Var
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig)
        sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (appendLeftIds diagram context.ids value) =
      wireValue values value := by
  unfold ConcreteElaboration.extendEnvironment
  revert values sig value
  generalize diagram.wiresAt region = localIds
  induction localIds with
  | nil =>
      intro values sig value
      nomatch value
  | cons head tail induction =>
      intro values sig value
      cases values with
      | cons headValue tailValues =>
          cases value with
          | here => rfl
          | there rest =>
              exact induction tailValues rest

theorem var_append_cases
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {sig : Sig}
    (value :
      Var ((leftIds ++ rightIds).map
        fun wire => (diagram.wires wire).sig) sig) :
    (∃ localValue :
        Var (leftIds.map fun wire => (diagram.wires wire).sig) sig,
      value = appendLeftIds diagram rightIds localValue) ∨
    (∃ outerValue :
        Var (rightIds.map fun wire => (diagram.wires wire).sig) sig,
      value =
        ConcreteElaboration.appendRightVar diagram leftIds outerValue) := by
  induction leftIds with
  | nil =>
      exact Or.inr ⟨value, rfl⟩
  | cons head tail induction =>
      cases value with
      | here =>
          exact Or.inl ⟨.here, rfl⟩
      | there rest =>
          rcases induction rest with
            ⟨localValue, same⟩ | ⟨outerValue, same⟩
          · exact Or.inl ⟨.there localValue, congrArg Var.there same⟩
          · exact Or.inr ⟨outerValue, congrArg Var.there same⟩

theorem option_bind₂_eq_some
    {first : Option α} {second : Option β}
    {combine : α → β → γ} {result : γ}
    (equation :
      (do
        let left ← first
        let right ← second
        pure (combine left right)) = some result) :
    ∃ left right,
      first = some left ∧ second = some right ∧
        combine left right = result := by
  cases first with
  | none => simp at equation
  | some left =>
      cases second with
      | none => simp at equation
      | some right =>
          exact ⟨left, right, rfl, rfl, Option.some.inj equation⟩

theorem compileNodes_cons_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (tail : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: tail) = some items) :
    ∃ head rest,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some (.cons head .nil) ∧
      ConcreteElaboration.compileNodes? definitions diagram context tail =
          some rest ∧
      items = .cons head rest := by
  rw [ConcreteElaboration.compileNodes?_equation] at compiled
  obtain ⟨head, rest, headEquation, restEquation, itemsEquation⟩ :=
    option_bind₂_eq_some compiled
  subst items
  refine ⟨head, rest, ?_, restEquation, rfl⟩
  rw [ConcreteElaboration.compileNodes?_equation]
  dsimp only
  rw [headEquation]
  rw [ConcreteElaboration.compileNodes?_equation]
  rfl

private theorem compileNodes_append
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (left ++ right) =
      (do
        let leftItems ←
          ConcreteElaboration.compileNodes? definitions diagram context left
        let rightItems ←
          ConcreteElaboration.compileNodes? definitions diagram context right
        pure (leftItems.append rightItems)) := by
  induction left with
  | nil =>
      rw [List.nil_append]
      rw [ConcreteElaboration.compileNodes?_equation definitions diagram
        context []]
      dsimp only
      simp [ItemSeq.append]
  | cons head tail induction =>
      rw [List.cons_append]
      rw [ConcreteElaboration.compileNodes?_equation definitions diagram
        context (head :: (tail ++ right))]
      rw [ConcreteElaboration.compileNodes?_equation definitions diagram
        context (head :: tail)]
      dsimp only
      rw [induction]
      simp [Option.bind_assoc, ItemSeq.append]

theorem compileNodes_append_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (left ++ right) = some items) :
    ∃ leftItems rightItems,
      ConcreteElaboration.compileNodes? definitions diagram context left =
          some leftItems ∧
      ConcreteElaboration.compileNodes? definitions diagram context right =
          some rightItems ∧
      items = leftItems.append rightItems := by
  rw [compileNodes_append] at compiled
  obtain ⟨leftItems, leftCompiled, remainder⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨rightItems, rightCompiled, combined⟩ :=
    Option.bind_eq_some_iff.mp remainder
  exact
    ⟨leftItems, rightItems, leftCompiled, rightCompiled,
      (Option.some.inj combined).symm⟩

theorem compileChildren_cons_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (child : diagram.RegionId)
    (tail : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context (child :: tail) =
        some items) :
    ∃ body rest,
      recurse child context = some body ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context tail =
        some rest ∧
      items = .cons (.cut body) rest := by
  simp only [ConcreteElaboration.compileChildrenWith?] at compiled
  obtain ⟨body, rest, bodyEquation, restEquation, itemsEquation⟩ :=
    option_bind₂_eq_some compiled
  subst items
  exact ⟨body, rest, bodyEquation, restEquation, rfl⟩

private theorem compileChildren_append
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.RegionId) :
    ConcreteElaboration.compileChildrenWith? definitions diagram recurse
        context (left ++ right) =
      (do
        let leftItems ←
          ConcreteElaboration.compileChildrenWith? definitions diagram
            recurse context left
        let rightItems ←
          ConcreteElaboration.compileChildrenWith? definitions diagram
            recurse context right
        pure (leftItems.append rightItems)) := by
  induction left with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?, ItemSeq.append]
  | cons head tail induction =>
      simp only [List.cons_append,
        ConcreteElaboration.compileChildrenWith?]
      rw [induction]
      simp [Option.bind_assoc, ItemSeq.append]

theorem compileChildren_append_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context (left ++ right) = some items) :
    ∃ leftItems rightItems,
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context left = some leftItems ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context right = some rightItems ∧
      items = leftItems.append rightItems := by
  rw [compileChildren_append] at compiled
  obtain ⟨leftItems, leftCompiled, remainder⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨rightItems, rightCompiled, combined⟩ :=
    Option.bind_eq_some_iff.mp remainder
  exact
    ⟨leftItems, rightItems, leftCompiled, rightCompiled,
      (Option.some.inj combined).symm⟩

theorem compileChildren_denotation_transport
    (definitions : List (List Sig))
    (source target : ConcreteDiagram definitions.length)
    (sourceRecurse : (region : source.RegionId) →
      (context : ConcreteElaboration.WireContext source) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : target.RegionId) →
      (context : ConcreteElaboration.WireContext target) →
        Option (Region definitions context.sigs))
    (sourceContext : ConcreteElaboration.WireContext source)
    (targetContext : ConcreteElaboration.WireContext target)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (children : List source.RegionId)
    (mapRegion : source.RegionId → target.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source
          sourceRecurse sourceContext children = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions target
          targetRecurse targetContext (children.map mapRegion) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (regions :
      ∀ child, child ∈ children →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse (mapRegion child) targetContext =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv rho) sourceBody)) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv rho) sourceItems := by
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp only [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      have sourceEmpty : sourceItems = .nil :=
        Option.some.inj sourceCompiled.symm
      have targetEmpty : targetItems = .nil :=
        Option.some.inj targetCompiled.symm
      subst sourceItems
      subst targetItems
      simp
  | cons child tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceEquation⟩ :=
        compileChildren_cons_components definitions source sourceRecurse
          sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetBody, targetRest, targetBodyCompiled,
          targetRestCompiled, targetEquation⟩ :=
        compileChildren_cons_components definitions target targetRecurse
          targetContext (mapRegion child) (tail.map mapRegion)
          targetItems targetCompiled
      subst sourceItems
      subst targetItems
      rw [denoteItemSeq_cons, denoteItemSeq_cons,
        cut_denotes_negation, cut_denotes_negation]
      exact and_congr
        (not_congr
          (regions child (by simp) sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled))
        (induction sourceRest targetRest sourceRestCompiled
          targetRestCompiled (by
            intro candidate member sourceBody targetBody sourceBodyCompiled
              targetBodyCompiled
            exact
              regions candidate (List.mem_cons_of_mem child member)
                sourceBody targetBody sourceBodyCompiled
                targetBodyCompiled))

def varForMember
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) → (wire : diagram.WireId) →
      wire ∈ ids →
      Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig
  | [], wire, member => by simp at member
  | head :: tail, wire, member =>
      if same : wire = head then
        same ▸ .here
      else
        .there
          (varForMember diagram tail wire (by simpa [same] using member))

theorem varForMember_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (varForMember diagram ids wire member) = wire := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      unfold varForMember
      split
      · rename_i same
        subst wire
        rfl
      · rename_i different
        exact induction (by simpa [different] using member)

def castVar
    (same : source = target)
    (value : Var context source) :
    Var context target :=
  same ▸ value

theorem origin_castVar
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (same : source = target)
    (value : Var
      (ids.map fun wire => (diagram.wires wire).sig) source) :
    ConcreteElaboration.WireContext.origin diagram ids
        (castVar same value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases same
  rfl

def contextEmbedding
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount) :
    (sourceIds : List source.WireId) →
    (targetIds : List target.WireId) →
    (mapWire : source.WireId → target.WireId) →
    (signature :
      ∀ wire,
        (target.wires (mapWire wire)).sig =
          (source.wires wire).sig) →
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds) →
    WireRenaming
      (sourceIds.map fun wire => (source.wires wire).sig)
      (targetIds.map fun wire => (target.wires wire).sig)
  | [], _, _, _, _ => fun value => nomatch value
  | head :: tail, targetIds, mapWire, signature, visible =>
      fun value =>
        match value with
        | Var.here =>
            castVar (signature head)
              (varForMember target targetIds (mapWire head)
                (visible head (by simp)))
        | Var.there rest =>
            contextEmbedding source target tail targetIds mapWire signature
              (fun wire member =>
                visible wire (List.mem_cons_of_mem head member))
              rest

theorem contextEmbedding_origin
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (sourceIds : List source.WireId)
    (targetIds : List target.WireId)
    (mapWire : source.WireId → target.WireId)
    (signature :
      ∀ wire,
        (target.wires (mapWire wire)).sig =
          (source.wires wire).sig)
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds)
    {sig : Sig}
    (value :
      Var (sourceIds.map fun wire => (source.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin target targetIds
        (contextEmbedding source target sourceIds targetIds mapWire
          signature visible value) =
      mapWire
        (ConcreteElaboration.WireContext.origin source sourceIds value) := by
  induction sourceIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          unfold contextEmbedding
          change
            ConcreteElaboration.WireContext.origin target targetIds
                (castVar (signature head)
                  (varForMember target targetIds (mapWire head)
                    (visible head (by simp)))) =
              mapWire head
          rw [origin_castVar, varForMember_origin]
      | there rest =>
          change
            ConcreteElaboration.WireContext.origin target targetIds
                (contextEmbedding source target tail targetIds mapWire
                  signature
                  (fun wire member =>
                    visible wire (List.mem_cons_of_mem head member))
                  rest) =
              mapWire
                (ConcreteElaboration.WireContext.origin source tail rest)
          exact
            induction
              (fun wire member =>
                visible wire (List.mem_cons_of_mem head member))
              rest

def hostContext
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val) :
    ConcreteElaboration.WireContext attachment.diagram :=
  ⟨context.ids.map attachment.hostWire⟩

def hostContextRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val) :
    WireRenaming context.sigs (hostContext attachment context).sigs :=
  contextEmbedding base.val attachment.diagram context.ids
    (hostContext attachment context).ids attachment.hostWire
    attachment.diagram_wire_hostWire
    (fun wire member => List.mem_map.mpr ⟨wire, member, rfl⟩)

theorem hostContextRenaming_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val)
    {sig : Sig} (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (hostContext attachment context).ids
        (hostContextRenaming attachment context value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val context.ids
          value) :=
  contextEmbedding_origin base.val attachment.diagram context.ids
    (hostContext attachment context).ids attachment.hostWire
    attachment.diagram_wire_hostWire
    (fun wire member => List.mem_map.mpr ⟨wire, member, rfl⟩)
    value

private def consHostSigsExact
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail) :
    leftHead :: leftTail = rightHead :: rightTail := by
  cases headExact
  cases tailExact
  rfl

private theorem cast_consHostSigsExact_here
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail) :
    consHostSigsExact headExact tailExact ▸
        (headExact ▸
          (Var.here : Var (leftHead :: leftTail) leftHead)) =
      (Var.here : Var (rightHead :: rightTail) rightHead) := by
  cases headExact
  cases tailExact
  rfl

private theorem cast_consHostSigsExact_there
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail)
    {sig : Sig}
    (value : Var leftTail sig) :
    consHostSigsExact headExact tailExact ▸ (Var.there value) =
      Var.there (tailExact ▸ value) := by
  cases headExact
  cases tailExact
  rfl

private def hostContextSigsStructural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    (ids : List base.val.WireId) →
      ((ids.map attachment.hostWire).map
        fun wire => (attachment.diagram.wires wire).sig) =
        ids.map fun wire => (base.val.wires wire).sig
  | [] => rfl
  | head :: tail =>
      consHostSigsExact
        (attachment.diagram_wire_hostWire head)
        (hostContextSigsStructural attachment tail)

private def positionalHostRenamingFor
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    (ids : List base.val.WireId) →
      WireRenaming
        (ids.map fun wire => (base.val.wires wire).sig)
        ((ids.map attachment.hostWire).map
          fun wire => (attachment.diagram.wires wire).sig)
  | [] => fun value => nomatch value
  | head :: tail =>
      fun value =>
        match value with
        | .here =>
            castVar (attachment.diagram_wire_hostWire head) .here
        | .there rest =>
            .there (positionalHostRenamingFor attachment tail rest)

private theorem positionalHostRenamingFor_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (ids : List base.val.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (base.val.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (ids.map attachment.hostWire)
        (positionalHostRenamingFor attachment ids value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val ids value) := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          simp only [positionalHostRenamingFor,
            ConcreteElaboration.WireContext.origin]
          exact origin_castVar attachment.diagram
            (head :: tail |>.map attachment.hostWire)
            (attachment.diagram_wire_hostWire head) .here
      | there value =>
          simpa only [positionalHostRenamingFor,
            ConcreteElaboration.WireContext.origin] using induction value

private theorem origin_injective_hostContext
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig} :
    Function.Injective
      (ConcreteElaboration.WireContext.origin diagram ids
        (sig := sig)) := by
  have originMember :
      ∀ {ids : List diagram.WireId} {sig : Sig}
        (value :
          Var (ids.map fun wire => (diagram.wires wire).sig) sig),
        ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
    intro ids sig value
    induction ids with
    | nil => nomatch value
    | cons head tail induction =>
        cases value with
        | here => simp [ConcreteElaboration.WireContext.origin]
        | there rest =>
            exact List.mem_cons_of_mem head (induction rest)
  intro left right same
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      have parts := List.pairwise_cons.mp nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there rest =>
              exact
                (parts.1 _
                  (originMember rest)
                  same).elim
      | there leftRest =>
          cases right with
          | here =>
              exact
                (parts.1 _
                  (originMember leftRest)
                  same.symm).elim
          | there rightRest =>
              exact congrArg Var.there
                (induction parts.2 same)

private theorem hostContextRenaming_eq_positional
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val)
    (targetNodup : (hostContext attachment context).ids.Nodup) :
    (hostContextRenaming attachment context :
      WireRenaming context.sigs (hostContext attachment context).sigs) =
      (positionalHostRenamingFor attachment context.ids :
        WireRenaming context.sigs
          (hostContext attachment context).sigs) := by
  funext sig value
  apply origin_injective_hostContext attachment.diagram
    (hostContext attachment context).ids targetNodup
  rw [hostContextRenaming_origin]
  exact positionalHostRenamingFor_origin attachment context.ids value |>.symm

private def hostContextSigsStructuralForContext
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val) :
    (hostContext attachment context).sigs = context.sigs :=
  hostContextSigsStructural attachment context.ids

theorem hostContext_sigs
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val) :
    (hostContext attachment context).sigs = context.sigs :=
  hostContextSigsStructuralForContext attachment context

/--
The host allocation preserves the ordered variable represented by every base
wire.  Reindexing its exact mapped signature vector back to the base vector
turns the canonical host-context renaming into the identity renaming.
-/
theorem hostContextRenaming_reindex_identity
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (context : ConcreteElaboration.WireContext base.val)
    (targetNodup : (hostContext attachment context).ids.Nodup) :
    (fun {sig} (value : Var context.sigs sig) =>
      (hostContext_sigs attachment context) ▸
        hostContextRenaming attachment context value) =
      (fun {_} (value : Var context.sigs _) => value) := by
  have sigsExact :
      hostContext_sigs attachment context =
        hostContextSigsStructuralForContext attachment context :=
    Subsingleton.elim _ _
  rw [sigsExact]
  funext sig value
  have renamingExact :=
    congrFun
      (congrFun
        (hostContextRenaming_eq_positional attachment context targetNodup)
        sig)
      value
  rw [renamingExact]
  cases context with
  | mk ids =>
      induction ids with
      | nil => nomatch value
      | cons head tail induction =>
          cases value with
          | here =>
              change
                consHostSigsExact
                    (attachment.diagram_wire_hostWire head)
                    (hostContextSigsStructural attachment tail) ▸
                    castVar (attachment.diagram_wire_hostWire head)
                      Var.here =
                  Var.here
              unfold castVar
              exact
                cast_consHostSigsExact_here
                  (attachment.diagram_wire_hostWire head)
                  (hostContextSigsStructural attachment tail)
          | there value =>
              change
                consHostSigsExact
                    (attachment.diagram_wire_hostWire head)
                    (hostContextSigsStructural attachment tail) ▸
                    Var.there
                      (positionalHostRenamingFor attachment tail value) =
                  Var.there value
              rw [cast_consHostSigsExact_there
                (attachment.diagram_wire_hostWire head)
                (hostContextSigsStructural attachment tail)]
              have tailNodup :
                  (hostContext attachment
                    ({ ids := tail } :
                      ConcreteElaboration.WireContext base.val)).ids.Nodup := by
                simpa [hostContext] using
                  (List.nodup_cons.mp targetNodup).2
              have tailRenamingExact :=
                congrFun
                  (congrFun
                    (hostContextRenaming_eq_positional attachment
                      ({ ids := tail } :
                        ConcreteElaboration.WireContext base.val)
                      tailNodup)
                    sig)
                  value
              exact
                congrArg Var.there
                  (induction tailNodup (Subsingleton.elim _ _) value
                    tailRenamingExact)

def generatedSiteContext
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (outer : ConcreteElaboration.WireContext base.val) :
    ConcreteElaboration.WireContext attachment.diagram :=
  (hostContext attachment outer).extend (attachment.hostRegion site)

private theorem generatedSiteContext_ids
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val) :
    (generatedSiteContext attachment outer).ids =
      (base.val.wiresAt site).map attachment.hostWire ++
        (ConcreteElaboration.openRootLocalWires fragment.val).map
            attachment.fragmentWire ++
          outer.ids.map attachment.hostWire := by
  unfold generatedSiteContext ConcreteElaboration.WireContext.extend
    hostContext
  change
    attachment.diagram.wiresAt (attachment.hostRegion site) ++
        (outer.ids.map attachment.hostWire :
          List attachment.diagram.WireId) =
      _
  rw [compiled.site_wires]
  rfl

theorem fragmentWire_signature
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId) :
    (attachment.diagram.wires (attachment.fragmentWire wire)).sig =
      (fragment.val.diagram.wires wire).sig := by
  unfold ConcreteSpliceAttachment.fragmentWire
  split
  · rename_i boundary
    rw [ConcreteSpliceAttachment.diagram_wire_hostWire]
    let position := attachment.representativePosition wire boundary
    have retrieved : fragment.val.boundary.get position = wire :=
      DenseList.get_index _ _ _
    change
      (base.val.wires (attachment.target position)).sig =
        (fragment.val.diagram.wires wire).sig
    exact (attachment.signature position).trans
      (congrArg
        (fun source => (fragment.val.diagram.wires source).sig)
        retrieved)
  · unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
    rw [DenseList.get_index]

private theorem generatedSiteLocalSigs_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    (attachment.diagram.wiresAt
        (attachment.hostRegion site)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (base.val.wiresAt site).map
            (fun wire => (base.val.wires wire).sig) ++
      (ConcreteElaboration.openRootLocalWires fragment.val).map
          (fun wire => (fragment.val.diagram.wires wire).sig) := by
  rw [compiled.site_wires]
  calc
    _ =
        ((base.val.wiresAt site).map attachment.hostWire).map
            (fun wire => (attachment.diagram.wires wire).sig) ++
          ((ConcreteElaboration.openRootLocalWires fragment.val).map
              attachment.fragmentWire).map
            (fun wire => (attachment.diagram.wires wire).sig) := by
      exact List.map_append
    _ =
        (base.val.wiresAt site).map
            (fun wire =>
              (attachment.diagram.wires
                (attachment.hostWire wire)).sig) ++
          (ConcreteElaboration.openRootLocalWires fragment.val).map
            (fun wire =>
              (attachment.diagram.wires
                (attachment.fragmentWire wire)).sig) := by
      congr 1
      · exact List.map_map
      · exact List.map_map
    _ = _ := by
      congr 1
      · apply List.map_congr_left
        intro wire _
        exact attachment.diagram_wire_hostWire wire
      · apply List.map_congr_left
        intro wire _
        exact fragmentWire_signature attachment wire

private theorem generatedSiteHostLocal_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (value :
      PackedVar
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig)) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt (attachment.hostRegion site))
        (castPacked (generatedSiteLocalSigs_eq compiled).symm
          (appendLeftPacked
            ((ConcreteElaboration.openRootLocalWires fragment.val).map
              fun wire => (fragment.val.diagram.wires wire).sig)
            value)) =
      attachment.hostWire
        (packedOrigin base.val (base.val.wiresAt site) value) := by
  exact packedOrigin_cast_appendLeft_of_allocation
    base.val attachment.diagram
    (base.val.wiresAt site)
    (attachment.diagram.wiresAt (attachment.hostRegion site))
    ((ConcreteElaboration.openRootLocalWires fragment.val).map
      attachment.fragmentWire)
    attachment.hostWire compiled.site_wires
    ((ConcreteElaboration.openRootLocalWires fragment.val).map
      fun wire => (fragment.val.diagram.wires wire).sig)
    (generatedSiteLocalSigs_eq compiled) value

private theorem generatedSiteFragmentLocal_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (value :
      PackedVar
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig)) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt (attachment.hostRegion site))
        (castPacked (generatedSiteLocalSigs_eq compiled).symm
          (appendRightPacked
            ((base.val.wiresAt site).map
              fun wire => (base.val.wires wire).sig)
            value)) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram
          (ConcreteElaboration.openRootLocalWires fragment.val)
          value) := by
  exact packedOrigin_cast_appendRight_of_allocation
    fragment.val.diagram attachment.diagram
    (ConcreteElaboration.openRootLocalWires fragment.val)
    (attachment.diagram.wiresAt (attachment.hostRegion site))
    ((base.val.wiresAt site).map attachment.hostWire)
    attachment.fragmentWire compiled.site_wires
    ((base.val.wiresAt site).map
      fun wire => (base.val.wires wire).sig)
    (generatedSiteLocalSigs_eq compiled) (by simp) value

def generatedSiteValues
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (baseValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (fragmentValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig)) :
    ConcreteElaboration.WireValues pre
      ((attachment.diagram.wiresAt
        (attachment.hostRegion site)).map
          fun wire => (attachment.diagram.wires wire).sig) :=
  (generatedSiteLocalSigs_eq compiled).symm ▸
    ConcreteElaboration.WireValues.append baseValues fragmentValues

private theorem generatedSiteValues_host
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (baseValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (fragmentValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig)
        sig) :
    wireValue (generatedSiteValues compiled baseValues fragmentValues)
        ((generatedSiteLocalSigs_eq compiled).symm ▸
          Var.appendLeft value
            ((ConcreteElaboration.openRootLocalWires fragment.val).map
              fun wire => (fragment.val.diagram.wires wire).sig)) =
      wireValue baseValues value := by
  exact
    (wireValue_cast
      (generatedSiteLocalSigs_eq compiled).symm
      (ConcreteElaboration.WireValues.append baseValues fragmentValues)
      (Var.appendLeft value
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig))).trans
      (wireValue_appendLeft baseValues fragmentValues value)

private theorem generatedSiteValues_fragment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (baseValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (fragmentValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig)
        sig) :
    wireValue (generatedSiteValues compiled baseValues fragmentValues)
        ((generatedSiteLocalSigs_eq compiled).symm ▸
          Var.appendRight
            ((base.val.wiresAt site).map
              fun wire => (base.val.wires wire).sig)
            value) =
      wireValue fragmentValues value := by
  exact
    (wireValue_cast
      (generatedSiteLocalSigs_eq compiled).symm
      (ConcreteElaboration.WireValues.append baseValues fragmentValues)
      (Var.appendRight
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig)
        value)).trans
      (wireValue_appendRight baseValues fragmentValues value)

theorem generatedSiteContext_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)) :
    (generatedSiteContext attachment outer).ids.Nodup :=
  ConcreteElaboration.extend_nodup definitions attachment.diagram
    compiled.generated_wellFormed (hostContext attachment outer)
    (attachment.hostRegion site) targetAbove

private theorem generatedSite_host_visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (wire : base.val.WireId)
    (member : wire ∈ (outer.extend site).ids) :
    attachment.hostWire wire ∈
      (generatedSiteContext attachment outer).ids := by
  rw [generatedSiteContext_ids compiled outer]
  change wire ∈ base.val.wiresAt site ++ outer.ids at member
  rcases List.mem_append.mp member with localMember | outerMember
  · apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨wire, localMember, rfl⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨wire, outerMember, rfl⟩

def generatedSiteHostRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val) :
    WireRenaming (outer.extend site).sigs
      (generatedSiteContext attachment outer).sigs :=
  contextEmbedding base.val attachment.diagram
    (outer.extend site).ids
    (generatedSiteContext attachment outer).ids
    attachment.hostWire attachment.diagram_wire_hostWire
    (generatedSite_host_visible compiled outer)

theorem generatedSiteHostRenaming_contextAction
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    {sig : Sig} (value : Var (outer.extend site).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteHostRenaming compiled outer value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val
          (outer.extend site).ids value) :=
  contextEmbedding_origin base.val attachment.diagram
    (outer.extend site).ids
    (generatedSiteContext attachment outer).ids
    attachment.hostWire attachment.diagram_wire_hostWire
    (generatedSite_host_visible compiled outer) value

def fragmentRootContext
    (fragment : CheckedOpenDiagram definitions) :
    ConcreteElaboration.WireContext fragment.val.diagram :=
  ⟨ConcreteElaboration.openRootLocalWires fragment.val ++
    ConcreteElaboration.openBoundaryWires fragment.val⟩

theorem openRoot_compile_components
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    ∃ nodes children :
        ItemSeq definitions (fragmentRootContext fragment).sigs,
      ConcreteElaboration.compileNodes? definitions fragment.val.diagram
          (fragmentRootContext fragment)
          (fragment.val.diagram.nodesAt fragment.val.diagram.root) =
        some nodes ∧
      ConcreteElaboration.compileChildrenWith? definitions
          fragment.val.diagram
          (ConcreteElaboration.compileRegion? definitions
            fragment.val.diagram fragment.val.diagram.regionCount)
          (fragmentRootContext fragment)
          (fragment.val.diagram.childrenOf fragment.val.diagram.root) =
        some children := by
  have bodyCompiled := compiled.body_generated
  rw [ConcreteElaboration.compileOpenRoot?_equation] at bodyCompiled
  obtain ⟨nodes, nodesCompiled, remainder⟩ :=
    Option.bind_eq_some_iff.mp bodyCompiled
  obtain ⟨children, childrenCompiled, _⟩ :=
    Option.bind_eq_some_iff.mp remainder
  exact ⟨nodes, children, nodesCompiled, childrenCompiled⟩

private theorem generatedSite_fragment_visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ (fragmentRootContext fragment).ids) :
    attachment.fragmentWire wire ∈
      (generatedSiteContext attachment outer).ids := by
  change
    wire ∈ ConcreteElaboration.openRootLocalWires fragment.val ++
      ConcreteElaboration.openBoundaryWires fragment.val at member
  rcases List.mem_append.mp member with localMember | boundary
  · rw [generatedSiteContext_ids compiled outer]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨wire, localMember, rfl⟩
  · have boundaryMember : wire ∈ fragment.val.boundary := by
      simpa [ConcreteElaboration.openBoundaryWires] using boundary
    let position :=
      attachment.representativePosition wire boundaryMember
    have targetMember :
        attachment.target position ∈ (outer.extend site).ids := by
      rw [← visibleEquality]
      exact compiled.target_visible position
    have hostMember :=
      generatedSite_host_visible compiled outer
        (attachment.target position) targetMember
    simpa [ConcreteSpliceAttachment.fragmentWire, boundaryMember,
      ConcreteSpliceAttachment.representativeTarget, position] using
        hostMember

def generatedSiteFragmentRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site) :
    WireRenaming (fragmentRootContext fragment).sigs
      (generatedSiteContext attachment outer).sigs :=
  contextEmbedding fragment.val.diagram attachment.diagram
    (fragmentRootContext fragment).ids
    (generatedSiteContext attachment outer).ids
    attachment.fragmentWire (fragmentWire_signature attachment)
    (generatedSite_fragment_visible compiled outer visibleEquality)

theorem generatedSiteFragmentRenaming_contextAction
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    {sig : Sig} (value : Var (fragmentRootContext fragment).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteFragmentRenaming compiled outer visibleEquality value) =
      attachment.fragmentWire
        (ConcreteElaboration.WireContext.origin fragment.val.diagram
          (fragmentRootContext fragment).ids value) :=
  contextEmbedding_origin fragment.val.diagram attachment.diagram
    (fragmentRootContext fragment).ids
    (generatedSiteContext attachment outer).ids
    attachment.fragmentWire (fragmentWire_signature attachment)
    (generatedSite_fragment_visible compiled outer visibleEquality) value

theorem origin_member
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there rest =>
          exact List.mem_cons_of_mem head (induction rest)

theorem origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig} :
    Function.Injective
      (ConcreteElaboration.WireContext.origin diagram ids
        (sig := sig)) := by
  intro left right same
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      have parts := List.pairwise_cons.mp nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there rest =>
              exact
                (parts.1 _
                  (origin_member diagram tail rest)
                  same).elim
      | there leftRest =>
          cases right with
          | here =>
              exact
                (parts.1 _
                  (origin_member diagram tail leftRest)
                  same.symm).elim
          | there rightRest =>
              exact congrArg Var.there
                (induction parts.2 same)

theorem packedOrigin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup) :
    Function.Injective (packedOrigin diagram ids) := by
  intro left right same
  rcases left with ⟨leftSig, leftVar⟩
  rcases right with ⟨rightSig, rightVar⟩
  have leftSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids leftVar
  have rightSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids rightVar
  change
    ConcreteElaboration.WireContext.origin diagram ids leftVar =
      ConcreteElaboration.WireContext.origin diagram ids rightVar at same
  rw [same] at leftSignature
  have signatureEquality : leftSig = rightSig :=
    leftSignature.symm.trans rightSignature
  cases signatureEquality
  have variableEquality :=
    origin_injective diagram ids nodup same
  cases variableEquality
  rfl

def evaluatePacked
    (env : Env pre context) :
    PackedVar context → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private theorem evaluatePacked_renamePacked
    (env : Env pre target)
    (rho : WireRenaming source target)
    (value : PackedVar source) :
    evaluatePacked env
        (InsertionCompilation.renamePacked rho value) =
      evaluatePacked (Env.comp env rho) value := by
  rcases value with ⟨sig, value⟩
  rfl

private theorem evaluatePacked_castPacked
    (env : Env pre target)
    (same : source = target)
    (value : PackedVar source) :
    evaluatePacked env (castPacked same value) =
      evaluatePacked
        (Env.comp env
          (fun {sig} (value : Var source sig) => same ▸ value)) value := by
  cases same
  rcases value with ⟨sig, value⟩
  rfl

theorem Vars.denote_eq_of_entries
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (entriesEqual :
      ∀ position : Fin args.length,
        evaluatePacked left
            (sources.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩) =
          evaluatePacked right
            (targets.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩)) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil =>
      cases targets
      rfl
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          have headEqual := entriesEqual ⟨0, by simp⟩
          simp only [Vars.entries, List.get_eq_getElem,
            List.getElem_cons_zero] at headEqual
          have tailEntriesEqual :
              ∀ position : Fin tailArgs.length,
                evaluatePacked left
                    (sourceTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) =
                  evaluatePacked right
                    (targetTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) := by
            intro position
            have atSuccessor :=
              entriesEqual
                ⟨position.val + 1, by
                  simp only [List.length_cons]
                  omega⟩
            simpa only [Vars.entries, List.get_eq_getElem,
              List.getElem_cons_succ] using atSuccessor
          have tailEqual := induction targetTail tailEntriesEqual
          simp only [Vars.denote_cons]
          apply Prod.ext
          · exact eq_of_heq (Sigma.mk.inj headEqual).2
          · exact tailEqual

theorem Vars.entries_eq_of_denote
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (valuesEqual :
      Vars.denote left sources = Vars.denote right targets)
    (position : Fin args.length) :
    evaluatePacked left
        (sources.entries.get
          ⟨position.val, by
            simpa only [ExtractedBoundaryCompiler.entries_length]
              using position.isLt⟩) =
      evaluatePacked right
        (targets.entries.get
          ⟨position.val, by
            simpa only [ExtractedBoundaryCompiler.entries_length]
              using position.isLt⟩) := by
  induction sources with
  | nil => nomatch position
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          rcases position with ⟨position, bound⟩
          cases position with
          | zero =>
              simp only [Vars.entries, List.get_eq_getElem,
                List.getElem_cons_zero]
              exact congrArg
                (fun value => (⟨sig, value⟩ : Sigma pre.Domain))
                (congrArg Prod.fst valuesEqual)
          | succ position =>
              have tailEqual :=
                induction targetTail (congrArg Prod.snd valuesEqual)
                  ⟨position, by
                    simp only [List.length_cons] at bound
                    omega⟩
              simpa only [Vars.entries, List.get_eq_getElem,
                List.getElem_cons_succ] using tailEqual

theorem generatedSiteHostRenaming_restrictEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (pre : PreModel)
    (targetValues :
      ConcreteElaboration.WireValues pre
        ((attachment.diagram.wiresAt
          (attachment.hostRegion site)).map
            fun wire => (attachment.diagram.wires wire).sig))
    (targetEnv : Env pre (hostContext attachment outer).sigs) :
    let generatedEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)
        targetValues targetEnv
    let sourceValues :=
      ConcreteElaboration.valuesFromEnvironmentFor base.val outer.ids
        (base.val.wiresAt site)
        (Env.comp generatedEnv
          (generatedSiteHostRenaming compiled outer))
    Env.comp generatedEnv
        (generatedSiteHostRenaming compiled outer) =
      ConcreteElaboration.extendEnvironment base.val outer site
        sourceValues
        (Env.comp targetEnv (hostContextRenaming attachment outer)) := by
  dsimp only
  symm
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  change
    ConcreteElaboration.extendEnvironment attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)
        targetValues targetEnv sig
        (generatedSiteHostRenaming compiled outer
          (ConcreteElaboration.appendRightVar base.val
            (base.val.wiresAt site) value)) =
      targetEnv sig (hostContextRenaming attachment outer value)
  have mappedOuter :
      generatedSiteHostRenaming compiled outer
          (ConcreteElaboration.appendRightVar base.val
            (base.val.wiresAt site) value) =
        ConcreteElaboration.appendRightVar attachment.diagram
          (attachment.diagram.wiresAt (attachment.hostRegion site))
          (hostContextRenaming attachment outer value) := by
    apply origin_injective attachment.diagram
      (generatedSiteContext attachment outer).ids
      (generatedSiteContext_nodup compiled outer targetAbove)
    rw [generatedSiteHostRenaming_contextAction]
    change
      attachment.hostWire
          (ConcreteElaboration.WireContext.origin base.val
            (base.val.wiresAt site ++ outer.ids)
            (ConcreteElaboration.appendRightVar base.val
              (base.val.wiresAt site) value)) =
        ConcreteElaboration.WireContext.origin attachment.diagram
          (attachment.diagram.wiresAt
              (attachment.hostRegion site) ++
            (hostContext attachment outer).ids)
          (ConcreteElaboration.appendRightVar attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.hostRegion site))
            (hostContextRenaming attachment outer value))
    rw [ConcreteElaboration.origin_appendRightVar,
      ConcreteElaboration.origin_appendRightVar,
      hostContextRenaming_origin]
  rw [mappedOuter]
  exact
    extendEnvironment_outer attachment.diagram
      (hostContext attachment outer) (attachment.hostRegion site)
      pre targetValues targetEnv
      (hostContextRenaming attachment outer value)

theorem generatedSiteHostRenaming_combinedEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (pre : PreModel)
    (baseValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (fragmentValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    (targetEnv : Env pre (hostContext attachment outer).sigs) :
    let targetValues :=
      generatedSiteValues compiled baseValues fragmentValues
    let generatedEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)
        targetValues targetEnv
    Env.comp generatedEnv
        (generatedSiteHostRenaming compiled outer) =
      ConcreteElaboration.extendEnvironment base.val outer site
        baseValues
        (Env.comp targetEnv
          (hostContextRenaming attachment outer)) := by
  dsimp only
  let targetValues :=
    generatedSiteValues compiled baseValues fragmentValues
  let generatedEnv :=
    ConcreteElaboration.extendEnvironment attachment.diagram
      (hostContext attachment outer) (attachment.hostRegion site)
      targetValues targetEnv
  funext sig value
  rcases
      var_append_cases base.val (base.val.wiresAt site) outer.ids value with
    ⟨localValue, same⟩ | ⟨outerValue, same⟩
  · subst value
    let fragmentLocalSigs :=
      (ConcreteElaboration.openRootLocalWires fragment.val).map
        fun wire => (fragment.val.diagram.wires wire).sig
    let targetLocal :=
      (generatedSiteLocalSigs_eq compiled).symm ▸
        Var.appendLeft localValue fragmentLocalSigs
    have mappedLocal :
        generatedSiteHostRenaming compiled outer
            (appendLeftIds base.val outer.ids localValue) =
          appendLeftIds attachment.diagram
            (hostContext attachment outer).ids targetLocal := by
      apply origin_injective attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteContext_nodup compiled outer targetAbove)
      rw [generatedSiteHostRenaming_contextAction]
      change
        attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              (base.val.wiresAt site ++ outer.ids)
              (appendLeftIds base.val outer.ids localValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.hostRegion site) ++
              (hostContext attachment outer).ids)
            (appendLeftIds attachment.diagram
              (hostContext attachment outer).ids targetLocal)
      rw [appendLeftIds_origin, appendLeftIds_origin]
      change
        attachment.hostWire
            (packedOrigin base.val (base.val.wiresAt site)
              (⟨sig, localValue⟩ : PackedVar
                ((base.val.wiresAt site).map
                  fun wire => (base.val.wires wire).sig))) =
          packedOrigin attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.hostRegion site))
            (castPacked (generatedSiteLocalSigs_eq compiled).symm
              (appendLeftPacked fragmentLocalSigs
                (⟨sig, localValue⟩ : PackedVar
                  ((base.val.wiresAt site).map
                    fun wire => (base.val.wires wire).sig))))
      exact
        (generatedSiteHostLocal_origin compiled
          (⟨sig, localValue⟩ : PackedVar
            ((base.val.wiresAt site).map
              fun wire => (base.val.wires wire).sig))).symm
    change
      generatedEnv sig
          (generatedSiteHostRenaming compiled outer
            (appendLeftIds base.val outer.ids localValue)) =
        ConcreteElaboration.extendEnvironment base.val outer site
          baseValues
          (Env.comp targetEnv
            (hostContextRenaming attachment outer))
          sig (appendLeftIds base.val outer.ids localValue)
    rw [mappedLocal]
    calc
      _ = wireValue targetValues targetLocal :=
        extendEnvironment_local attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          pre targetValues targetEnv targetLocal
      _ = wireValue baseValues localValue := by
        unfold targetValues targetLocal fragmentLocalSigs
        exact
          generatedSiteValues_host compiled baseValues fragmentValues
            localValue
      _ = _ :=
        (extendEnvironment_local base.val outer site pre baseValues
          (Env.comp targetEnv
            (hostContextRenaming attachment outer))
          localValue).symm
  · subst value
    have mappedOuter :
        generatedSiteHostRenaming compiled outer
            (ConcreteElaboration.appendRightVar base.val
              (base.val.wiresAt site) outerValue) =
          ConcreteElaboration.appendRightVar attachment.diagram
            (attachment.diagram.wiresAt (attachment.hostRegion site))
            (hostContextRenaming attachment outer outerValue) := by
      apply origin_injective attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteContext_nodup compiled outer targetAbove)
      rw [generatedSiteHostRenaming_contextAction]
      change
        attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              (base.val.wiresAt site ++ outer.ids)
              (ConcreteElaboration.appendRightVar base.val
                (base.val.wiresAt site) outerValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.hostRegion site) ++
              (hostContext attachment outer).ids)
            (ConcreteElaboration.appendRightVar attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.hostRegion site))
              (hostContextRenaming attachment outer outerValue))
      rw [ConcreteElaboration.origin_appendRightVar,
        ConcreteElaboration.origin_appendRightVar,
        hostContextRenaming_origin]
    change
      generatedEnv sig
          (generatedSiteHostRenaming compiled outer
            (ConcreteElaboration.appendRightVar base.val
              (base.val.wiresAt site) outerValue)) =
        ConcreteElaboration.extendEnvironment base.val outer site
          baseValues
          (Env.comp targetEnv
            (hostContextRenaming attachment outer))
          sig (ConcreteElaboration.appendRightVar base.val
            (base.val.wiresAt site) outerValue)
    rw [mappedOuter]
    calc
      _ = targetEnv sig
            (hostContextRenaming attachment outer outerValue) :=
        extendEnvironment_outer attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          pre targetValues targetEnv
          (hostContextRenaming attachment outer outerValue)
      _ = _ :=
        (extendEnvironment_outer base.val outer site pre baseValues
          (Env.comp targetEnv
            (hostContextRenaming attachment outer))
          outerValue).symm

def equalityRenaming
    (same : source = target) :
    WireRenaming source target :=
  fun {_} value => same ▸ value

theorem denoteRegion_castContext
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (same : source = target)
    (env : Env pre target)
    (body : Region definitions source) :
    denoteRegion pre definitionEnv env (same ▸ body) ↔
      denoteRegion pre definitionEnv
        (Env.comp env (equalityRenaming same)) body := by
  cases same
  rfl

private theorem targetPackedAt_cast_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (position : Fin fragment.val.boundary.length) :
    packedOrigin base.val (outer.extend site).ids
        (castPacked
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality)
          (compiled.targetPackedAt position)) =
      attachment.target position := by
  have transported :=
    packedOrigin_transport_ids base.val
      (congrArg ConcreteElaboration.WireContext.ids
        visibleEquality).symm
      (compiled.targetPackedAt position)
  exact transported.trans (compiled.targetPackedAt_origin position)

def generatedTargetPacked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (position : Fin fragment.val.boundary.length) :
    PackedVar (generatedSiteContext attachment outer).sigs :=
  InsertionCompilation.renamePacked
    (generatedSiteHostRenaming compiled outer)
    (castPacked
      (congrArg ConcreteElaboration.WireContext.sigs visibleEquality)
      (compiled.targetPackedAt position))

theorem generatedTargetPacked_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (position : Fin fragment.val.boundary.length) :
    packedOrigin attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedTargetPacked compiled outer visibleEquality position) =
      attachment.hostWire (attachment.target position) := by
  rcases packedEquation :
      castPacked
        (congrArg ConcreteElaboration.WireContext.sigs visibleEquality)
        (compiled.targetPackedAt position) with
    ⟨sig, value⟩
  unfold generatedTargetPacked InsertionCompilation.renamePacked
  rw [packedEquation]
  change
    ConcreteElaboration.WireContext.origin attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteHostRenaming compiled outer value) =
      attachment.hostWire (attachment.target position)
  rw [generatedSiteHostRenaming_contextAction]
  have sourceOrigin :=
    targetPackedAt_cast_origin compiled outer visibleEquality position
  have sourceOrigin' :
      ConcreteElaboration.WireContext.origin base.val
          (outer.extend site).ids value =
        attachment.target position := by
    exact
      (congrArg
        (packedOrigin base.val (outer.extend site).ids)
        packedEquation).symm.trans sourceOrigin
  exact congrArg attachment.hostWire sourceOrigin'

def generatedFrameEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (env : Env pre (generatedSiteContext attachment outer).sigs) :
    Env pre compiled.site.frame.visible.sigs :=
  Env.comp
    (Env.comp env (generatedSiteHostRenaming compiled outer))
    (equalityRenaming
      (congrArg ConcreteElaboration.WireContext.sigs visibleEquality))

theorem evaluate_generatedTargetPacked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (env : Env pre (generatedSiteContext attachment outer).sigs)
    (position : Fin fragment.val.boundary.length) :
    evaluatePacked env
        (generatedTargetPacked compiled outer visibleEquality position) =
      evaluatePacked
        (generatedFrameEnvironment compiled outer visibleEquality env)
        (compiled.targetPackedAt position) := by
  unfold generatedTargetPacked generatedFrameEnvironment
  rw [evaluatePacked_renamePacked, evaluatePacked_castPacked]
  rfl

private def fragmentBoundaryRenaming
    (fragment : CheckedOpenDiagram definitions) :
    WireRenaming
      (ConcreteElaboration.openBoundaryClassSigs fragment.val)
      (fragmentRootContext fragment).sigs :=
  fun {_} value =>
    ConcreteElaboration.appendRightVar fragment.val.diagram
      (ConcreteElaboration.openRootLocalWires fragment.val)
      value

private theorem extendOpenRootEnvironment_from_environment
    (fragment : CheckedOpenDiagram definitions)
    (pre : PreModel)
    (env : Env pre (fragmentRootContext fragment).sigs) :
    ConcreteElaboration.extendOpenRootEnvironment fragment.val
        (ConcreteElaboration.valuesFromEnvironmentFor
          fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (ConcreteElaboration.openRootLocalWires fragment.val) env)
        (Env.comp env
          (fragmentBoundaryRenaming fragment)) =
      env := by
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  rfl

private theorem extractedWireOfVar_eq_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var
        (ids.map fun wire => (diagram.wires wire).sig)
        sig) :
    ExtractedBoundaryCompiler.wireOfVar diagram value =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

private theorem fragmentBoundaryRenaming_origin
    {definitions : List (List Sig)}
    (fragment : CheckedOpenDiagram definitions)
    {sig : Sig}
    (value :
      Var
        (ConcreteElaboration.openBoundaryClassSigs fragment.val)
        sig) :
    ConcreteElaboration.WireContext.origin fragment.val.diagram
        (fragmentRootContext fragment).ids
        (fragmentBoundaryRenaming fragment value) =
      ExtractedBoundaryCompiler.wireOfVar
        fragment.val.diagram value := by
  change
    ConcreteElaboration.WireContext.origin fragment.val.diagram
        (ConcreteElaboration.openRootLocalWires fragment.val ++
          ConcreteElaboration.openBoundaryWires fragment.val)
        (ConcreteElaboration.appendRightVar fragment.val.diagram
          (ConcreteElaboration.openRootLocalWires fragment.val) value) =
      _
  rw [ConcreteElaboration.origin_appendRightVar]
  exact
    (extractedWireOfVar_eq_origin fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val) value).symm

private theorem generatedSite_boundary_variable
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    {sig : Sig}
    (fiber : Var fragmentCompiled.openDiagram.classes sig) :
    generatedSiteFragmentRenaming compiled outer visibleEquality
        (fragmentBoundaryRenaming fragment fiber) =
      generatedSiteHostRenaming compiled outer
        (equalityRenaming
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality)
          (compiled.intrinsicAttachment.classMap fiber)) := by
  apply origin_injective attachment.diagram
    (generatedSiteContext attachment outer).ids
    (generatedSiteContext_nodup compiled outer targetAbove)
  rw [generatedSiteFragmentRenaming_contextAction,
    generatedSiteHostRenaming_contextAction,
    fragmentBoundaryRenaming_origin]
  let source :=
    ExtractedBoundaryCompiler.wireOfPacked
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
      (⟨sig, fiber⟩ :
        PackedVar fragmentCompiled.openDiagram.classes)
  let member := compiled.intrinsicClassWire_mem_boundary fiber
  let representative :=
    attachment.representativePosition source member
  have classPackedEquality :=
    compiled.intrinsicAttachment_classMap_eq_representative fiber
  have castClassPackedEquality :=
    congrArg
      (castPacked
        (congrArg ConcreteElaboration.WireContext.sigs
          visibleEquality))
      classPackedEquality
  have castClassPackedEquality' :
      castPacked
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality)
          (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
            PackedVar compiled.site.frame.visible.sigs) =
        castPacked
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality)
          (compiled.targetPackedAt representative) := by
    simpa only [source, member, representative] using
      castClassPackedEquality
  have classOrigin :
      packedOrigin base.val (outer.extend site).ids
          (castPacked
            (congrArg ConcreteElaboration.WireContext.sigs
              visibleEquality)
            (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
              PackedVar compiled.site.frame.visible.sigs)) =
        attachment.target representative := by
    exact
      (congrArg
        (packedOrigin base.val (outer.extend site).ids)
        castClassPackedEquality').trans
        (targetPackedAt_cast_origin compiled outer visibleEquality
          representative)
  change
    attachment.fragmentWire source =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val
          (outer.extend site).ids
          (equalityRenaming
            (congrArg ConcreteElaboration.WireContext.sigs
              visibleEquality)
            (compiled.intrinsicAttachment.classMap fiber)))
  rw [show
    ConcreteElaboration.WireContext.origin base.val
        (outer.extend site).ids
        (equalityRenaming
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality)
          (compiled.intrinsicAttachment.classMap fiber)) =
      attachment.target representative by
        exact classOrigin]
  simp [ConcreteSpliceAttachment.fragmentWire, member,
    ConcreteSpliceAttachment.representativeTarget, representative, source]

theorem generatedSiteFragmentRenaming_restrictEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (pre : PreModel)
    (targetValues :
      ConcreteElaboration.WireValues pre
        ((attachment.diagram.wiresAt
          (attachment.hostRegion site)).map
            fun wire => (attachment.diagram.wires wire).sig))
    (targetEnv : Env pre (hostContext attachment outer).sigs) :
    let generatedEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)
        targetValues targetEnv
    let sourceSiteEnv :=
      Env.comp generatedEnv
        (generatedSiteHostRenaming compiled outer)
    let frameEnv :=
      Env.comp sourceSiteEnv
        (equalityRenaming
          (congrArg ConcreteElaboration.WireContext.sigs
            visibleEquality))
    let fragmentEnv :=
      Env.comp generatedEnv
        (generatedSiteFragmentRenaming compiled outer visibleEquality)
    let fragmentValues :=
      ConcreteElaboration.valuesFromEnvironmentFor
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val)
        (ConcreteElaboration.openRootLocalWires fragment.val)
        fragmentEnv
    fragmentEnv =
      ConcreteElaboration.extendOpenRootEnvironment fragment.val
        fragmentValues
        (Env.comp frameEnv
          compiled.intrinsicAttachment.classMap) := by
  dsimp only
  let generatedEnv :=
    ConcreteElaboration.extendEnvironment attachment.diagram
      (hostContext attachment outer) (attachment.hostRegion site)
      targetValues targetEnv
  let fragmentEnv :=
    Env.comp generatedEnv
      (generatedSiteFragmentRenaming compiled outer visibleEquality)
  have boundaryEquality :
      Env.comp fragmentEnv
          (fragmentBoundaryRenaming fragment) =
        Env.comp
          (Env.comp
            (Env.comp generatedEnv
              (generatedSiteHostRenaming compiled outer))
            (equalityRenaming
              (congrArg ConcreteElaboration.WireContext.sigs
                visibleEquality)))
          compiled.intrinsicAttachment.classMap := by
    funext sig fiber
    exact congrArg (generatedEnv sig)
      (generatedSite_boundary_variable compiled outer visibleEquality
        targetAbove fiber)
  have reconstructed :=
    extendOpenRootEnvironment_from_environment fragment pre fragmentEnv
  rw [boundaryEquality] at reconstructed
  exact reconstructed.symm

theorem generatedSiteFragmentRenaming_combinedEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (pre : PreModel)
    (baseValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt site).map
          fun wire => (base.val.wires wire).sig))
    (fragmentValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    (targetEnv : Env pre (hostContext attachment outer).sigs) :
    let targetValues :=
      generatedSiteValues compiled baseValues fragmentValues
    let generatedEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site)
        targetValues targetEnv
    Env.comp generatedEnv
        (generatedSiteFragmentRenaming compiled outer visibleEquality) =
      ConcreteElaboration.extendOpenRootEnvironment fragment.val
        fragmentValues
        (Env.comp
          (generatedFrameEnvironment compiled outer visibleEquality
            generatedEnv)
          compiled.intrinsicAttachment.classMap) := by
  dsimp only
  let targetValues :=
    generatedSiteValues compiled baseValues fragmentValues
  let generatedEnv :=
    ConcreteElaboration.extendEnvironment attachment.diagram
      (hostContext attachment outer) (attachment.hostRegion site)
      targetValues targetEnv
  let boundaryEnv :=
    Env.comp
      (generatedFrameEnvironment compiled outer visibleEquality
        generatedEnv)
      compiled.intrinsicAttachment.classMap
  funext sig value
  rcases
      var_append_cases fragment.val.diagram
        (ConcreteElaboration.openRootLocalWires fragment.val)
        (ConcreteElaboration.openBoundaryWires fragment.val)
        value with
    ⟨localValue, same⟩ | ⟨fiber, same⟩
  · subst value
    let baseLocalSigs :=
      (base.val.wiresAt site).map
        fun wire => (base.val.wires wire).sig
    let targetLocal :=
      (generatedSiteLocalSigs_eq compiled).symm ▸
        Var.appendRight baseLocalSigs localValue
    have mappedLocal :
        generatedSiteFragmentRenaming compiled outer visibleEquality
            (appendLeftIds fragment.val.diagram
              (ConcreteElaboration.openBoundaryWires fragment.val)
              localValue) =
          appendLeftIds attachment.diagram
            (hostContext attachment outer).ids targetLocal := by
      apply origin_injective attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteContext_nodup compiled outer targetAbove)
      rw [generatedSiteFragmentRenaming_contextAction]
      change
        attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram
              (ConcreteElaboration.openRootLocalWires fragment.val ++
                ConcreteElaboration.openBoundaryWires fragment.val)
              (appendLeftIds fragment.val.diagram
                (ConcreteElaboration.openBoundaryWires fragment.val)
                localValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.hostRegion site) ++
              (hostContext attachment outer).ids)
            (appendLeftIds attachment.diagram
              (hostContext attachment outer).ids targetLocal)
      rw [appendLeftIds_origin, appendLeftIds_origin]
      change
        attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (ConcreteElaboration.openRootLocalWires fragment.val)
              (⟨sig, localValue⟩ : PackedVar
                ((ConcreteElaboration.openRootLocalWires
                  fragment.val).map
                    fun wire =>
                      (fragment.val.diagram.wires wire).sig))) =
          packedOrigin attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.hostRegion site))
            (castPacked (generatedSiteLocalSigs_eq compiled).symm
              (appendRightPacked baseLocalSigs
                (⟨sig, localValue⟩ : PackedVar
                  ((ConcreteElaboration.openRootLocalWires
                    fragment.val).map
                      fun wire =>
                        (fragment.val.diagram.wires wire).sig))))
      exact
        (generatedSiteFragmentLocal_origin compiled
          (⟨sig, localValue⟩ : PackedVar
            ((ConcreteElaboration.openRootLocalWires fragment.val).map
              fun wire =>
                (fragment.val.diagram.wires wire).sig))).symm
    change
      generatedEnv sig
          (generatedSiteFragmentRenaming compiled outer visibleEquality
            (appendLeftIds fragment.val.diagram
              (ConcreteElaboration.openBoundaryWires fragment.val)
              localValue)) =
        ConcreteElaboration.extendEnvironmentFor
          fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (ConcreteElaboration.openRootLocalWires fragment.val)
          fragmentValues boundaryEnv sig
          (appendLeftIds fragment.val.diagram
            (ConcreteElaboration.openBoundaryWires fragment.val)
            localValue)
    rw [mappedLocal]
    calc
      _ = wireValue targetValues targetLocal :=
        extendEnvironment_local attachment.diagram
          (hostContext attachment outer) (attachment.hostRegion site)
          pre targetValues targetEnv targetLocal
      _ = wireValue fragmentValues localValue := by
        unfold targetValues targetLocal baseLocalSigs
        exact
          generatedSiteValues_fragment compiled baseValues fragmentValues
            localValue
      _ = _ :=
        (extendEnvironmentFor_local fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (ConcreteElaboration.openRootLocalWires fragment.val)
          fragmentValues boundaryEnv localValue).symm
  · subst value
    have mappedBoundary :
        generatedSiteFragmentRenaming compiled outer visibleEquality
            (ConcreteElaboration.appendRightVar fragment.val.diagram
              (ConcreteElaboration.openRootLocalWires fragment.val)
              fiber) =
          generatedSiteHostRenaming compiled outer
            (equalityRenaming
              (congrArg ConcreteElaboration.WireContext.sigs
                visibleEquality)
              (compiled.intrinsicAttachment.classMap fiber)) := by
      exact
        generatedSite_boundary_variable compiled outer visibleEquality
          targetAbove fiber
    change
      generatedEnv sig
          (generatedSiteFragmentRenaming compiled outer visibleEquality
            (ConcreteElaboration.appendRightVar fragment.val.diagram
              (ConcreteElaboration.openRootLocalWires fragment.val)
              fiber)) =
        ConcreteElaboration.extendEnvironmentFor
          fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (ConcreteElaboration.openRootLocalWires fragment.val)
          fragmentValues boundaryEnv sig
          (ConcreteElaboration.appendRightVar fragment.val.diagram
            (ConcreteElaboration.openRootLocalWires fragment.val)
            fiber)
    rw [mappedBoundary]
    calc
      _ = boundaryEnv sig fiber := rfl
      _ = _ :=
        (extendEnvironmentFor_outer fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (ConcreteElaboration.openRootLocalWires fragment.val)
          fragmentValues boundaryEnv fiber).symm


end NaturalityInternal
end InsertionCompilation
end VisualProof
