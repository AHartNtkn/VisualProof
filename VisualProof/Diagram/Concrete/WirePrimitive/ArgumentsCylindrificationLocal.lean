import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationSemantics

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ArgumentsSemantics

universe u

/--
Remove one distinguished relation head from a scope-local binder block.
The removed value is carried in an explicit semantic slot while every other
local binder remains available to the cylindrification checker.
-/
inductive LocalHeadRemoval (headSignature : Sig) :
    List Sig → List Sig → Type
  | here :
      LocalHeadRemoval headSignature
        (headSignature :: rest) rest
  | there
      (signature : Sig)
      (rest : LocalHeadRemoval headSignature bound reduced) :
      LocalHeadRemoval headSignature
        (signature :: bound) (signature :: reduced)

namespace LocalHeadRemoval

/-- Intrinsically typed classification of a variable in an appended context. -/
inductive AppendVariableClass (left right : List Sig) :
    {signature : Sig} → Var (left ++ right) signature → Type
  | left (value : Var left signature) :
      AppendVariableClass left right (Var.appendLeft value right)
  | right (value : Var right signature) :
      AppendVariableClass left right (Var.appendRight left value)

/-- Every variable in an appended context comes from exactly one typed side. -/
def classifyAppend :
    (left : List Sig) → (value : Var (left ++ right) signature) →
      AppendVariableClass left right value
  | [], value => .right value
  | _ :: _, .here => .left .here
  | head :: tail, .there rest =>
      match classifyAppend tail rest with
      | .left innerValue => .left (.there innerValue)
      | .right outer => .right outer

/-- Construct the unique removal selected by an intrinsically typed variable. -/
def ofVar :
    (head : Var bound headSignature) →
      Σ reduced, LocalHeadRemoval headSignature bound reduced
  | .here => ⟨_, .here⟩
  | .there tail =>
      let ⟨reduced, removal⟩ := ofVar tail
      ⟨_, .there _ removal⟩

/-- The original local variable selected by the removal. -/
def head :
    LocalHeadRemoval headSignature bound reduced →
      Var bound headSignature
  | .here => .here
  | .there _ rest => .there rest.head

/-- Removing the binder selected by a typed variable records that exact
variable as its distinguished head. -/
theorem ofVar_head (selected : Var bound headSignature) :
    (ofVar selected).2.head = selected := by
  induction selected with
  | here => rfl
  | there tail induction =>
      simp only [ofVar, head]
      rw [induction]

/-- Reconstructing a removal from its recorded head returns that exact
dependent removal receipt, including its reduced binder index. -/
theorem ofVar_head_exact
    (removal : LocalHeadRemoval headSignature bound reduced) :
    ofVar removal.head = ⟨reduced, removal⟩ := by
  induction removal with
  | here => rfl
  | there signature rest induction =>
      simp only [head, ofVar]
      rw [induction]

/-- Ordered binder signatures after deleting the selected typed position. -/
def eraseSelected : (selected : Var bound signature) → List Sig
  | @Var.here signature rest => rest
  | @Var.there rest signature head tail =>
      head :: eraseSelected tail

/-- Embed the ordered binder block left after deleting a selected typed
position back into its original context. -/
def retainSelected :
    (selected : Var bound headSignature) →
      WireRenaming (eraseSelected selected) bound
  | .here => fun value => .there value
  | .there selected => WireRenaming.lift (retainSelected selected) _

/-- `ofVar` computes exactly the ordered signature deletion. -/
theorem ofVar_reduced (selected : Var bound signature) :
    (ofVar selected).1 = eraseSelected selected := by
  induction selected with
  | here => rfl
  | there tail induction =>
      simp only [ofVar, eraseSelected]
      rw [induction]

/-- Every removal's reduced index is the signature list obtained by deleting
its recorded head. -/
theorem reduced_eq_erase_head
    (removal : LocalHeadRemoval headSignature bound reduced) :
    reduced = eraseSelected removal.head := by
  induction removal with
  | here => rfl
  | there localSignature rest induction =>
      exact congrArg (List.cons localSignature) induction

/-- Typed position immediately after a retained prefix and before a suffix. -/
def beforeSuffix
    (pre suffix : List Sig) (signature : Sig) :
    Var (pre ++ signature :: suffix) signature :=
  Var.appendRight pre (.here : Var (signature :: suffix) signature)

theorem eraseSelected_beforeSuffix
    (pre suffix : List Sig) (signature : Sig) :
    eraseSelected (beforeSuffix pre suffix signature) =
      pre ++ suffix := by
  induction pre with
  | nil => rfl
  | cons head tail induction =>
      change head :: eraseSelected (beforeSuffix tail suffix signature) =
        head :: (tail ++ suffix)
      rw [induction]

theorem ofVar_beforeSuffix_reduced
    (pre suffix : List Sig) (signature : Sig) :
    (ofVar (beforeSuffix pre suffix signature)).1 = pre ++ suffix := by
  rw [ofVar_reduced, eraseSelected_beforeSuffix]

private def keepPrefix
    (retainedPrefix : List Sig)
    (outer : WireRenaming source target) :
    WireRenaming (retainedPrefix ++ source) (retainedPrefix ++ target) :=
  match retainedPrefix with
  | [] => outer
  | signature :: rest =>
      WireRenaming.lift (keepPrefix rest outer) signature

private theorem keepPrefix_appendLeft
    (retainedPrefix : List Sig)
    (outer : WireRenaming source target)
    (value : Var retainedPrefix signature) :
    keepPrefix retainedPrefix outer
        (Var.appendLeft value source) =
      Var.appendLeft value target := by
  induction value with
  | here => rfl
  | there tail induction =>
      change Var.there
          (keepPrefix _ outer (Var.appendLeft tail source)) =
        Var.there (Var.appendLeft tail target)
      exact congrArg Var.there induction

private theorem keepPrefix_appendRight
    (retainedPrefix : List Sig)
    (outer : WireRenaming source target)
    (value : Var source signature) :
    keepPrefix retainedPrefix outer
        (Var.appendRight retainedPrefix value) =
      Var.appendRight retainedPrefix (outer value) := by
  induction retainedPrefix with
  | nil => rfl
  | cons head tail induction =>
      simp only [keepPrefix, WireRenaming.lift, Var.appendRight]
      exact congrArg Var.there induction

/-- Embed every retained local binder back into the original block. -/
def retain
    (removal : LocalHeadRemoval headSignature bound reduced) :
    WireRenaming reduced bound :=
  match removal with
  | .here => fun value => .there value
  | .there signature rest => fun value =>
      match value with
      | .here => .here
      | .there tail => .there (rest.retain tail)

/-- Intrinsically typed classification of every local variable as either the
selected head or one exact retained position. -/
inductive VariableClass
    (removal : LocalHeadRemoval headSignature bound reduced) :
    {signature : Sig} → Var bound signature → Type
  | head : VariableClass removal removal.head
  | retained (value : Var reduced signature) :
      VariableClass removal (removal.retain value)

/-- The head/retained classification is exhaustive without comparing
signatures or untyped de Bruijn indices. -/
def classify :
    (removal : LocalHeadRemoval headSignature bound reduced) →
      (value : Var bound signature) → VariableClass removal value
  | .here, .here => .head
  | .here, .there tail => .retained tail
  | .there _ _, .here => .retained .here
  | .there localSignature rest, .there tail =>
      match rest.classify tail with
      | .head => .head
      | .retained retained => .retained (.there retained)

/--
Rename a complete local-plus-outer context after moving the selected head to
an explicit slot in the new outer context.
-/
def rename
    (removal : LocalHeadRemoval headSignature bound reduced)
    (outer : WireRenaming sourceOuter targetOuter)
    (headSlot : Var targetOuter headSignature) :
    WireRenaming (bound ++ sourceOuter) (reduced ++ targetOuter) :=
  match removal with
  | .here =>
      fun value =>
        match value with
        | Var.here => Var.appendRight reduced headSlot
        | Var.there tail => keepPrefix _ outer tail
  | .there signature rest =>
      WireRenaming.lift (rest.rename outer headSlot) signature

/-- The selected local head is sent to its explicit normalized outer slot. -/
theorem rename_head
    (removal : LocalHeadRemoval headSignature bound reduced)
    (outer : WireRenaming sourceOuter targetOuter)
    (headSlot : Var targetOuter headSignature) :
    removal.rename outer headSlot
        (Var.appendLeft removal.head sourceOuter) =
      Var.appendRight reduced headSlot := by
  induction removal with
  | here => rfl
  | there signature rest induction =>
      change Var.there
          (rest.rename outer headSlot
            (Var.appendLeft rest.head sourceOuter)) =
        Var.there (Var.appendRight _ headSlot)
      exact congrArg Var.there induction

/-- Every non-head local binder keeps its exact ordered normalized position. -/
theorem rename_retain
    (removal : LocalHeadRemoval headSignature bound reduced)
    (outer : WireRenaming sourceOuter targetOuter)
    (headSlot : Var targetOuter headSignature)
    (value : Var reduced signature) :
    removal.rename outer headSlot
        (Var.appendLeft (removal.retain value) sourceOuter) =
      Var.appendLeft value targetOuter := by
  induction removal with
  | here =>
      exact keepPrefix_appendLeft _ outer value
  | there localSignature rest induction =>
      cases value with
      | here => rfl
      | there tail =>
          change Var.there
              (rest.rename outer headSlot
                (Var.appendLeft (rest.retain tail) sourceOuter)) =
            Var.there (Var.appendLeft tail targetOuter)
          exact congrArg Var.there (induction tail)

/-- Every variable from the surrounding concrete compiler context is sent
through the selected outer renaming beyond the complete reduced local block. -/
theorem rename_outer
    (removal : LocalHeadRemoval headSignature bound reduced)
    (outer : WireRenaming sourceOuter targetOuter)
    (headSlot : Var targetOuter headSignature)
    (value : Var sourceOuter signature) :
    removal.rename outer headSlot (Var.appendRight bound value) =
      Var.appendRight reduced (outer value) := by
  induction removal with
  | @here rest =>
      simp only [rename, Var.appendRight]
      exact keepPrefix_appendRight rest outer value
  | there localSignature rest induction =>
      simp only [rename, Var.appendRight]
      exact congrArg Var.there induction

/-- Split the selected semantic head from the retained local values. -/
def splitValues
    (removal : LocalHeadRemoval headSignature bound reduced) :
    ConcreteElaboration.WireValues pre bound →
      pre.Domain headSignature ×
        ConcreteElaboration.WireValues pre reduced :=
  match removal with
  | .here => fun
      | .cons head tail => ⟨head, tail⟩
  | .there _ rest => fun
      | .cons head tail =>
          let split := rest.splitValues tail
          ⟨split.1, .cons head split.2⟩

/-- Reassemble the complete local tuple from its head and retained values. -/
def assembleValues
    (removal : LocalHeadRemoval headSignature bound reduced) :
    pre.Domain headSignature →
      ConcreteElaboration.WireValues pre reduced →
        ConcreteElaboration.WireValues pre bound :=
  match removal with
  | .here => fun head tail => .cons head tail
  | .there _ rest => fun selected values =>
      match values with
      | .cons head tail =>
          .cons head (rest.assembleValues selected tail)

@[simp] theorem split_assemble
    (removal : LocalHeadRemoval headSignature bound reduced)
    (head : pre.Domain headSignature)
    (values : ConcreteElaboration.WireValues pre reduced) :
    removal.splitValues (removal.assembleValues head values) =
      ⟨head, values⟩ := by
  induction removal with
  | here => rfl
  | there signature rest induction =>
      cases values with
      | cons value tail =>
          simp only [assembleValues, splitValues]
          rw [induction]

@[simp] theorem assemble_split
    (removal : LocalHeadRemoval headSignature bound reduced)
    (values : ConcreteElaboration.WireValues pre bound) :
    removal.assembleValues
        (removal.splitValues values).1
        (removal.splitValues values).2 =
      values := by
  induction removal with
  | here =>
      cases values
      rfl
  | there signature rest induction =>
      cases values with
      | cons value tail =>
          simp only [splitValues, assembleValues]
          rw [induction]

private theorem keepPrefix_environment
    (retainedPrefix : List Sig)
    (outer : WireRenaming source target)
    (sourceEnv : Env pre source)
    (targetEnv : Env pre target)
    (exact : Env.comp targetEnv outer = sourceEnv)
    (values : ConcreteElaboration.WireValues pre retainedPrefix) :
    Env.comp
        (ContentShapeSemantics.extendValues values targetEnv)
        (keepPrefix retainedPrefix outer) =
      ContentShapeSemantics.extendValues values sourceEnv := by
  induction retainedPrefix with
  | nil =>
      cases values
      exact exact
  | cons signature rest induction =>
      cases values with
      | cons head tail =>
          simp only [ContentShapeSemantics.extendValues]
          funext selected value
          cases value with
          | here => rfl
          | there value =>
              exact congrFun (congrFun (induction tail) selected) value

/-- The normalized renaming reconstructs the original local environment. -/
theorem rename_environment
    (removal : LocalHeadRemoval headSignature bound reduced)
    (outer : WireRenaming sourceOuter targetOuter)
    (sourceOuterEnv : Env pre sourceOuter)
    (targetOuterEnv : Env pre targetOuter)
    (outerExact : Env.comp targetOuterEnv outer = sourceOuterEnv)
    (headValue : pre.Domain headSignature)
    (reducedValues : ConcreteElaboration.WireValues pre reduced)
    (headExact :
      targetOuterEnv _ headSlot = headValue) :
    Env.comp
        (ContentShapeSemantics.extendValues reducedValues targetOuterEnv)
        (removal.rename outer headSlot) =
      ContentShapeSemantics.extendValues
        (removal.assembleValues headValue reducedValues)
        sourceOuterEnv := by
  induction removal with
  | here =>
      funext selectedSig boundVar
      cases boundVar with
      | here =>
          change
            ContentShapeSemantics.extendValues reducedValues targetOuterEnv
                headSignature (Var.appendRight _ headSlot) =
              headValue
          rw [ContentShapeSemantics.extendValues_outer]
          exact headExact
      | there tail =>
          have restored :=
            keepPrefix_environment _ outer sourceOuterEnv targetOuterEnv
              outerExact reducedValues
          simpa [LocalHeadRemoval.rename,
            ContentShapeSemantics.extendValues] using
              congrFun (congrFun restored selectedSig) tail
  | there signature rest induction =>
      cases reducedValues with
      | cons value tail =>
          funext selectedSig boundVar
          cases boundVar with
          | here => rfl
          | there boundVar =>
              simpa [LocalHeadRemoval.rename,
                ContentShapeSemantics.extendValues] using congrFun
                (congrFun
                  (induction tail)
                  selectedSig)
                boundVar

end LocalHeadRemoval

end ArgumentsSemantics

end ConcreteWirePrimitive

end VisualProof
