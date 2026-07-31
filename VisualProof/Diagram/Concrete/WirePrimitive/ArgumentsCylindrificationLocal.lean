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

private def keepPrefix
    (retainedPrefix : List Sig)
    (outer : WireRenaming source target) :
    WireRenaming (retainedPrefix ++ source) (retainedPrefix ++ target) :=
  match retainedPrefix with
  | [] => outer
  | signature :: rest =>
      WireRenaming.lift (keepPrefix rest outer) signature

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
