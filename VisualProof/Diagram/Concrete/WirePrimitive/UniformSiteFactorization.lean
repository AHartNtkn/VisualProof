import VisualProof.Diagram.Concrete.IsomorphismSearch
import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval

namespace VisualProof

namespace WirePrimitive

universe u v w

/-!
## Intrinsic simultaneous-site shapes

The concrete content rules do not expose a sequence of one-site rewrites.
Instead, their semantic ledgers compile the complete acted scope and compare
two intrinsic shapes.  A shape retains every ordinary item and every ambient
cut/binder, but records the uniformly rewritten cells as typed holes.

Both bodies are first renamed into one common visible context.  Consequently
ordinary items are compared by intrinsic equality and are evaluated in one
environment; only the interpretation of the holes differs.
-/

private def Var.decEq :
    (left right : Var context signature) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private instance : DecidableEq (Var context signature) :=
  Var.decEq

private def Vars.decEq :
    (left right : Vars context arguments) → Decidable (left = right)
  | .nil, .nil => isTrue rfl
  | .cons leftHead leftTail, .cons rightHead rightTail =>
      match Var.decEq leftHead rightHead, decEq leftTail rightTail with
      | isTrue headEqual, isTrue tailEqual =>
          isTrue (by cases headEqual; cases tailEqual; rfl)
      | isFalse different, _ =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)
      | _, isFalse different =>
          isFalse (fun equality => by
            cases equality
            exact different rfl)

private instance : DecidableEq (Vars context arguments) :=
  Vars.decEq

private def DefVar.decEq :
    (left right : DefVar definitions arguments) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse (fun equality => by cases equality)
  | .there _, .here => isFalse (fun equality => by cases equality)
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse (fun equality => by
          cases equality
          exact different rfl)

private instance : DecidableEq (DefVar definitions arguments) :=
  DefVar.decEq

deriving instance DecidableEq for Region
deriving instance DecidableEq for Item
deriving instance DecidableEq for ItemSeq

/-- Ordered typed holes at one intrinsic context. -/
structure UniformIntrinsicHoles
    (arguments context : List Sig) where
  values : List (Vars context arguments)
  deriving DecidableEq

mutual

/-- One acted-scope body with its uniform cells abstracted as typed holes. -/
inductive UniformIntrinsicRegion
    (definitions : List (List Sig)) (arguments : List Sig) :
    List Sig → Type
  | mk {context : List Sig}
      (ordinary :
        UniformIntrinsicItemSeq definitions arguments context)
      (holes : UniformIntrinsicHoles arguments context) :
      UniformIntrinsicRegion definitions arguments context

/-- An ordinary intrinsic item retained by a uniform-site abstraction. -/
inductive UniformIntrinsicItem
    (definitions : List (List Sig)) (arguments : List Sig) :
    List Sig → Type
  | leaf {context}
      (item : Item definitions context) :
      UniformIntrinsicItem definitions arguments context
  | cut {context}
      (body : UniformIntrinsicRegion definitions arguments context) :
      UniformIntrinsicItem definitions arguments context
  | bind {context}
      (signature : Sig)
      (body :
        UniformIntrinsicRegion definitions arguments
          (signature :: context)) :
      UniformIntrinsicItem definitions arguments context

/-- Ordered ordinary items retained in one intrinsic shape region. -/
inductive UniformIntrinsicItemSeq
    (definitions : List (List Sig)) (arguments : List Sig) :
    List Sig → Type
  | nil {context} :
      UniformIntrinsicItemSeq definitions arguments context
  | cons {context}
      (head : UniformIntrinsicItem definitions arguments context)
      (tail : UniformIntrinsicItemSeq definitions arguments context) :
      UniformIntrinsicItemSeq definitions arguments context

end

/-- Ordered hole tuples exposed by a uniform intrinsic region. -/
def UniformIntrinsicRegion.holeValues :
    UniformIntrinsicRegion definitions arguments context →
      List (Vars context arguments)
  | .mk _ holes => holes.values

namespace UniformIntrinsicRegion

deriving instance DecidableEq for UniformIntrinsicRegion
deriving instance DecidableEq for UniformIntrinsicItem
deriving instance DecidableEq for UniformIntrinsicItemSeq

/-- Conjunction of a proposition over every member of one list. -/
private def all (values : List α) (holds : α → Prop) : Prop :=
  ∀ value, value ∈ values → holds value

private theorem all_congr
    (values : List α)
    {left right : α → Prop}
    (pointwise : ∀ value, left value ↔ right value) :
    all values left ↔ all values right := by
  constructor
  · intro holds value member
    exact (pointwise value).mp (holds value member)
  · intro holds value member
    exact (pointwise value).mpr (holds value member)

mutual

/-- Denotation of a simultaneous-site shape under one interpretation of holes. -/
def denote
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
  (env : Env pre context)
  (site : PreModel.Args pre.Domain arguments → Prop) :
    UniformIntrinsicRegion definitions arguments context → Prop
  | .mk ordinary holes =>
      UniformIntrinsicItemSeq.denote pre definitionEnv env site ordinary ∧
        all holes.values (fun values => site (Vars.denote env values))

/-- Denotation of one ordinary item retained in a simultaneous-site shape. -/
def UniformIntrinsicItem.denote
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (site : PreModel.Args pre.Domain arguments → Prop) :
    UniformIntrinsicItem definitions arguments context → Prop
  | .leaf item =>
      denoteItem pre definitionEnv env item
  | .cut body =>
      ¬ body.denote pre definitionEnv env site
  | .bind _ body =>
      ∃ value, body.denote pre definitionEnv (env.extend value) site

/-- Denotation of the retained ordinary item sequence. -/
def UniformIntrinsicItemSeq.denote
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
  (site : PreModel.Args pre.Domain arguments → Prop) :
    UniformIntrinsicItemSeq definitions arguments context → Prop
  | .nil => True
  | .cons head tail =>
      UniformIntrinsicItem.denote pre definitionEnv env site head ∧
        UniformIntrinsicItemSeq.denote pre definitionEnv env site tail


end

mutual

/-- Pointwise-equivalent hole interpretations give the same shape denotation. -/
theorem denote_site_congr
    (shape : UniformIntrinsicRegion definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (left right : PreModel.Args pre.Domain arguments → Prop)
    (pointwise : ∀ values, left values ↔ right values) :
    shape.denote pre definitionEnv env left ↔
      shape.denote pre definitionEnv env right := by
  cases shape with
  | mk ordinary holes =>
      exact
        and_congr
          (UniformIntrinsicItemSeq.denote_site_congr ordinary pre
            definitionEnv env left right pointwise)
          (all_congr holes.values fun values =>
            pointwise (Vars.denote env values))

private theorem UniformIntrinsicItem.denote_site_congr
    (item : UniformIntrinsicItem definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (left right : PreModel.Args pre.Domain arguments → Prop)
    (pointwise : ∀ values, left values ↔ right values) :
    UniformIntrinsicItem.denote pre definitionEnv env left item ↔
      UniformIntrinsicItem.denote pre definitionEnv env right item := by
  cases item with
  | leaf _ => exact Iff.rfl
  | cut body =>
      exact
        not_congr
          (denote_site_congr body pre definitionEnv env left right
            pointwise)
  | bind signature body =>
      constructor
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (denote_site_congr body pre definitionEnv (env.extend value)
              left right pointwise).mp holds⟩
      · rintro ⟨value, holds⟩
        exact
          ⟨value,
            (denote_site_congr body pre definitionEnv (env.extend value)
              left right pointwise).mpr holds⟩

private theorem UniformIntrinsicItemSeq.denote_site_congr
    (items : UniformIntrinsicItemSeq definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (left right : PreModel.Args pre.Domain arguments → Prop)
    (pointwise : ∀ values, left values ↔ right values) :
    UniformIntrinsicItemSeq.denote pre definitionEnv env left items ↔
      UniformIntrinsicItemSeq.denote pre definitionEnv env right items := by
  cases items with
  | nil => exact Iff.rfl
  | cons head tail =>
      exact
        and_congr
          (UniformIntrinsicItem.denote_site_congr head pre definitionEnv env
            left right pointwise)
          (UniformIntrinsicItemSeq.denote_site_congr tail pre definitionEnv
            env left right pointwise)

end

/-- Recognize an atom whose typed relation head is the selected uniform head. -/
def matchedHeadArguments?
    {context : List Sig}
    {arguments atomArguments : List Sig}
    (head : Var context (.rel arguments))
    (atomHead : Var context (.rel atomArguments))
    (values : Vars context atomArguments) :
    Option (Vars context arguments) :=
  if signatures : atomArguments = arguments then
    if equal : signatures ▸ atomHead = head then
      some (signatures ▸ values)
    else
      none
  else
    none

private def prependOrdinary
    (item : UniformIntrinsicItem definitions arguments context) :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicRegion definitions arguments context
  | .mk ordinary holes => .mk (.cons item ordinary) holes

private def prependHole
    (values : Vars context arguments) :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicRegion definitions arguments context
  | .mk ordinary holes => .mk ordinary ⟨values :: holes.values⟩

@[simp] private theorem holeValues_prependOrdinary
    (item : UniformIntrinsicItem definitions arguments context)
    (shape : UniformIntrinsicRegion definitions arguments context) :
    (prependOrdinary item shape).holeValues = shape.holeValues := by
  cases shape
  rfl

@[simp] private theorem holeValues_prependHole
    (values : Vars context arguments)
    (shape : UniformIntrinsicRegion definitions arguments context) :
    (prependHole values shape).holeValues = values :: shape.holeValues := by
  cases shape
  rfl

/-- Concatenate the retained ordinary portions of two uniform shapes. -/
def UniformIntrinsicItemSeq.append :
    UniformIntrinsicItemSeq definitions arguments context →
      UniformIntrinsicItemSeq definitions arguments context →
        UniformIntrinsicItemSeq definitions arguments context
  | .nil, right => right
  | .cons head tail, right =>
      .cons head (UniformIntrinsicItemSeq.append tail right)

/-- Concatenate two uniform abstractions in source item order. -/
def appendAbstracted
    (left right : UniformIntrinsicRegion definitions arguments context) :
    UniformIntrinsicRegion definitions arguments context :=
  match left, right with
  | .mk leftItems leftHoles, .mk rightItems rightHoles =>
      .mk (UniformIntrinsicItemSeq.append leftItems rightItems)
        ⟨leftHoles.values ++ rightHoles.values⟩

private theorem prependOrdinary_appendAbstracted
    (item : UniformIntrinsicItem definitions arguments context)
    (left right : UniformIntrinsicRegion definitions arguments context) :
    prependOrdinary item (appendAbstracted left right) =
      appendAbstracted (prependOrdinary item left) right := by
  cases left
  cases right
  rfl

private theorem prependHole_appendAbstracted
    (values : Vars context arguments)
    (left right : UniformIntrinsicRegion definitions arguments context) :
    prependHole values (appendAbstracted left right) =
      appendAbstracted (prependHole values left) right := by
  cases left
  cases right
  rfl

private theorem matchedHeadArguments_denote
    (pre : PreModel.{u})
    (env : Env pre context)
    (head : Var context (.rel arguments))
    (atomHead : Var context (.rel atomArguments))
    (values : Vars context atomArguments)
    (matched : matchedHeadArguments? head atomHead values = some result) :
    pre.apply (env _ atomHead) (Vars.denote env values) =
      pre.apply (env _ head) (Vars.denote env result) := by
  unfold matchedHeadArguments? at matched
  split at matched
  · rename_i signatures
    cases signatures
    split at matched
    · rename_i equal
      cases equal
      cases Option.some.inj matched
      rfl
    · contradiction
  · contradiction

mutual

/--
Abstract direct atoms headed by `head`.  All other structure, including
ordinary cuts and binders, is retained.
-/
def abstractApplied
    (head : Var context (.rel arguments)) :
    Region definitions context →
      UniformIntrinsicRegion definitions arguments context
  | .mk items => abstractAppliedItems head items

/-- Recursive item-sequence implementation of `abstractApplied`, exposed so
construction-owned receipts can characterize its exact ordinary items and
ordered holes. -/
def abstractAppliedItems
    (head : Var context (.rel arguments)) :
    ItemSeq definitions context →
      UniformIntrinsicRegion definitions arguments context
  | .nil => .mk .nil ⟨[]⟩
  | .cons item tail =>
      let rest := abstractAppliedItems head tail
      match item with
      | .atom atomHead values =>
          match matchedHeadArguments? head atomHead values with
          | some arguments => prependHole arguments rest
          | none => prependOrdinary (.leaf (.atom atomHead values)) rest
      | .named definition values =>
          prependOrdinary (.leaf (.named definition values)) rest
      | .identity signature ports atLeastTwo =>
          prependOrdinary
            (.leaf (.identity signature ports atLeastTwo)) rest
      | .cut body =>
          prependOrdinary (.cut (abstractApplied head body)) rest
      | .bind signature body =>
          prependOrdinary
            (.bind signature (abstractApplied (.there head) body)) rest

end

/-- Direct application tuples selected from one item sequence, in source
item order. Nested cuts and binders own their own local hole lists. -/
def directAppliedArguments
    (head : Var context (.rel arguments)) :
    ItemSeq definitions context → List (Vars context arguments)
  | .nil => []
  | .cons item tail =>
      let rest := directAppliedArguments head tail
      match item with
      | .atom atomHead values =>
          match matchedHeadArguments? head atomHead values with
          | some applied => applied :: rest
          | none => rest
      | .named .. => rest
      | .identity .. => rest
      | .cut .. => rest
      | .bind .. => rest

/-- Direct matching applications distribute over the concrete compiler's
ordered item-sequence append. -/
theorem directAppliedArguments_append
    (head : Var context (.rel arguments)) :
    ∀ (left right : ItemSeq definitions context),
      directAppliedArguments head (left.append right) =
        directAppliedArguments head left ++
          directAppliedArguments head right
  | .nil, right => rfl
  | .cons item tail, right => by
      have tailExact := directAppliedArguments_append head tail right
      cases item with
      | atom atomHead values =>
          simp only [ItemSeq.append, directAppliedArguments]
          split <;> simp [tailExact]
      | named definition values =>
          simp only [ItemSeq.append, directAppliedArguments]
          exact tailExact
      | identity signature ports atLeastTwo =>
          simp only [ItemSeq.append, directAppliedArguments]
          exact tailExact
      | cut body =>
          simp only [ItemSeq.append, directAppliedArguments]
          exact tailExact
      | bind signature body =>
          simp only [ItemSeq.append, directAppliedArguments]
          exact tailExact

/-- Intrinsic wire renaming distributes over ordered item append. -/
theorem ItemSeq.renameWires_append
    (rho : WireRenaming source target) :
    ∀ (left right : ItemSeq definitions source),
      (left.append right).renameWires rho =
        (left.renameWires rho).append (right.renameWires rho)
  | .nil, right => rfl
  | .cons head tail, right => by
      simp only [ItemSeq.append, ItemSeq.renameWires]
      rw [ItemSeq.renameWires_append rho tail right]

/-- A compiled child-region sequence consists only of cut items, so it
contributes no application hole at its parent region. -/
theorem directAppliedArguments_compileChildrenWith_eq_nil
    (head : Var context.sigs (.rel arguments))
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children = some items) :
    directAppliedArguments head items = [] := by
  induction children generalizing items with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at compiled
      subst items
      rfl
  | cons child tail induction =>
      simp only [ConcreteElaboration.compileChildrenWith?] at compiled
      cases childCompiled : recurse child context with
      | none => simp [childCompiled] at compiled
      | some body =>
          cases tailCompiled :
              ConcreteElaboration.compileChildrenWith? definitions diagram
                recurse context tail with
          | none => simp [childCompiled, tailCompiled] at compiled
          | some rest =>
              have itemsExact : items = .cons (.cut body) rest := by
                exact (Option.some.inj (by
                  simpa [childCompiled, tailCompiled] using compiled)).symm
              subst items
              simpa [directAppliedArguments] using induction rest tailCompiled

/-- Renaming a compiled child-region sequence still contributes no direct
application hole at its parent region. -/
theorem directAppliedArguments_rename_compileChildrenWith_eq_nil
    (rho : WireRenaming context.sigs normalizedContext)
    (head : Var normalizedContext (.rel arguments))
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children = some items) :
    directAppliedArguments head (items.renameWires rho) = [] := by
  induction children generalizing items with
  | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at compiled
      subst items
      rfl
  | cons child tail induction =>
      simp only [ConcreteElaboration.compileChildrenWith?] at compiled
      cases childCompiled : recurse child context with
      | none => simp [childCompiled] at compiled
      | some body =>
          cases tailCompiled :
              ConcreteElaboration.compileChildrenWith? definitions diagram
                recurse context tail with
          | none => simp [childCompiled, tailCompiled] at compiled
          | some rest =>
              have itemsExact : items = .cons (.cut body) rest := by
                exact (Option.some.inj (by
                  simpa [childCompiled, tailCompiled] using compiled)).symm
              subst items
              simpa [ItemSeq.renameWires, Item.renameWires,
                directAppliedArguments] using induction rest tailCompiled

/-- Compile and classify one concrete node as a direct application of the
selected intrinsic head. -/
def compiledAppliedArguments?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (head : Var context.sigs (.rel arguments))
    (node : diagram.NodeId) : Option (Vars context.sigs arguments) := do
  let item ← ConcreteElaboration.Internal.compileNode? definitions diagram
    context node
  match item with
  | .atom atomHead values => matchedHeadArguments? head atomHead values
  | .named .. => none
  | .identity .. => none
  | .cut .. => none
  | .bind .. => none

/-- The direct holes extracted from a compiled concrete node list are exactly
the ordered successful results of its per-node application classifier. -/
theorem directAppliedArguments_compileNodes
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (head : Var context.sigs (.rel arguments)) :
    ∀ (nodes : List diagram.NodeId)
      (items : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
        directAppliedArguments head items =
          nodes.filterMap
            (compiledAppliedArguments? definitions diagram context head)
  | [], items, compiled => by
      simp [ConcreteElaboration.compileNodes?] at compiled
      subst items
      rfl
  | node :: tail, items, compiled => by
      simp only [ConcreteElaboration.compileNodes?] at compiled
      cases headCompiled :
          ConcreteElaboration.Internal.compileNode? definitions diagram
            context node with
      | none => simp [headCompiled] at compiled
      | some compiledHead =>
          cases tailCompiled :
              ConcreteElaboration.compileNodes? definitions diagram context
                tail with
          | none => simp [headCompiled, tailCompiled] at compiled
          | some compiledTail =>
              have itemsExact :
                  items = .cons compiledHead compiledTail := by
                exact (Option.some.inj (by
                  simpa [headCompiled, tailCompiled] using compiled)).symm
              subst items
              have tailExact := directAppliedArguments_compileNodes
                definitions diagram context head tail compiledTail tailCompiled
              cases compiledHead with
              | atom atomHead values =>
                  simp only [directAppliedArguments, List.filterMap_cons,
                    compiledAppliedArguments?, headCompiled]
                  split <;> simp [tailExact, *]
              | named definition values =>
                  simp [directAppliedArguments, compiledAppliedArguments?,
                    headCompiled, tailExact]
              | identity signature ports atLeastTwo =>
                  simp [directAppliedArguments, compiledAppliedArguments?,
                    headCompiled, tailExact]
              | cut body =>
                  simp [directAppliedArguments, compiledAppliedArguments?,
                    headCompiled, tailExact]
              | bind signature body =>
                  simp [directAppliedArguments, compiledAppliedArguments?,
                    headCompiled, tailExact]

/-- Compile one node, rename its intrinsic variables, and classify the
renamed atom against a selected normalized head. -/
def renamedCompiledAppliedArguments?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (rho : WireRenaming context.sigs normalizedContext)
    (head : Var normalizedContext (.rel arguments))
    (node : diagram.NodeId) : Option (Vars normalizedContext arguments) := do
  let item ← ConcreteElaboration.Internal.compileNode? definitions diagram
    context node
  match item with
  | .atom atomHead values =>
      matchedHeadArguments? head (rho atomHead) (Vars.rename rho values)
  | .named .. => none
  | .identity .. => none
  | .cut .. => none
  | .bind .. => none

/-- Renaming a compiled node sequence before abstraction preserves its exact
concrete node order in the corresponding renamed per-node classifier. -/
theorem directAppliedArguments_rename_compileNodes
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (rho : WireRenaming context.sigs normalizedContext)
    (head : Var normalizedContext (.rel arguments)) :
    ∀ (nodes : List diagram.NodeId)
      (items : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
        directAppliedArguments head (items.renameWires rho) =
          nodes.filterMap
            (renamedCompiledAppliedArguments? definitions diagram context rho
              head)
  | [], items, compiled => by
      simp [ConcreteElaboration.compileNodes?] at compiled
      subst items
      rfl
  | node :: tail, items, compiled => by
      simp only [ConcreteElaboration.compileNodes?] at compiled
      cases headCompiled :
          ConcreteElaboration.Internal.compileNode? definitions diagram
            context node with
      | none => simp [headCompiled] at compiled
      | some compiledHead =>
          cases tailCompiled :
              ConcreteElaboration.compileNodes? definitions diagram context
                tail with
          | none => simp [headCompiled, tailCompiled] at compiled
          | some compiledTail =>
              have itemsExact :
                  items = .cons compiledHead compiledTail := by
                exact (Option.some.inj (by
                  simpa [headCompiled, tailCompiled] using compiled)).symm
              subst items
              have tailExact := directAppliedArguments_rename_compileNodes
                definitions diagram context rho head tail compiledTail
                  tailCompiled
              cases compiledHead with
              | atom atomHead values =>
                  simp only [ItemSeq.renameWires, Item.renameWires,
                    directAppliedArguments, List.filterMap_cons,
                    renamedCompiledAppliedArguments?, headCompiled]
                  split <;> simp [tailExact, *]
              | named definition values =>
                  simp [ItemSeq.renameWires, Item.renameWires,
                    directAppliedArguments, renamedCompiledAppliedArguments?,
                    headCompiled, tailExact]
              | identity signature ports atLeastTwo =>
                  simp [ItemSeq.renameWires, Item.renameWires,
                    directAppliedArguments, renamedCompiledAppliedArguments?,
                    headCompiled, tailExact]
              | cut body =>
                  simp [ItemSeq.renameWires, Item.renameWires,
                    directAppliedArguments, renamedCompiledAppliedArguments?,
                    headCompiled, tailExact]
              | bind signature body =>
                  simp [ItemSeq.renameWires, Item.renameWires,
                    directAppliedArguments, renamedCompiledAppliedArguments?,
                    headCompiled, tailExact]

/-- `abstractAppliedItems` exposes exactly the direct matching applications
and preserves their item-sequence order. -/
theorem abstractAppliedItems_holeValues
    (head : Var context (.rel arguments)) :
    ∀ items : ItemSeq definitions context,
    (abstractAppliedItems head items).holeValues =
      directAppliedArguments head items
  | .nil => rfl
  | .cons item tail => by
      have tailExact := abstractAppliedItems_holeValues head tail
      cases item with
      | atom atomHead values =>
          simp only [abstractAppliedItems, directAppliedArguments]
          split
          · exact (holeValues_prependHole _ _).trans
              (congrArg (List.cons _) tailExact)
          · exact (holeValues_prependOrdinary _ _).trans tailExact
      | named definition values =>
          simp only [abstractAppliedItems, directAppliedArguments]
          exact (holeValues_prependOrdinary _ _).trans tailExact
      | identity signature ports atLeastTwo =>
          simp only [abstractAppliedItems, directAppliedArguments]
          exact (holeValues_prependOrdinary _ _).trans tailExact
      | cut body =>
          simp only [abstractAppliedItems, directAppliedArguments]
          exact (holeValues_prependOrdinary _ _).trans tailExact
      | bind signature body =>
          simp only [abstractAppliedItems, directAppliedArguments]
          exact (holeValues_prependOrdinary _ _).trans tailExact

/-- `abstractApplied` has the same direct ordered hole characterization at
the region boundary. -/
theorem abstractApplied_holeValues
    (head : Var context (.rel arguments))
    (body : Region definitions context) :
    (abstractApplied head body).holeValues =
      match body with
      | .mk items => directAppliedArguments head items := by
  cases body with
  | mk items => exact abstractAppliedItems_holeValues head items

/-- The ordered holes exposed from a renamed canonical site body are exactly
the successful normalized per-node classifiers in concrete node order. -/
theorem abstractApplied_rename_siteBody_holeValues
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (rho : WireRenaming compiled.frame.visible.sigs normalizedContext)
    (head : Var normalizedContext (.rel arguments)) :
    (abstractApplied head (compiled.frame.siteBody.renameWires rho)).holeValues =
      (base.val.nodesAt site).filterMap
        (renamedCompiledAppliedArguments? definitions base.val
          compiled.frame.visible rho head) := by
  obtain ⟨fuel, nodes, children, nodesCompiled, childrenCompiled,
      bodyExact⟩ := compiled.siteBody_decomposition
  rw [bodyExact]
  simp only [Region.renameWires, abstractApplied_holeValues,
    ItemSeq.renameWires_append]
  rw [directAppliedArguments_append]
  rw [directAppliedArguments_rename_compileNodes definitions base.val
    compiled.frame.visible rho head (base.val.nodesAt site) nodes
      nodesCompiled]
  rw [directAppliedArguments_rename_compileChildrenWith_eq_nil rho head
    (base.val.childrenOf site) children childrenCompiled]
  simp

/-- Applied abstraction preserves item-sequence concatenation exactly. -/
theorem abstractAppliedItems_append
    (head : Var context (.rel arguments)) :
    ∀ (left right : ItemSeq definitions context),
      abstractAppliedItems head (left.append right) =
        appendAbstracted (abstractAppliedItems head left)
          (abstractAppliedItems head right)
  | .nil, right => by
      rw [ItemSeq.nil_append]
      cases abstractAppliedItems head right
      rfl
  | .cons item tail, right => by
      have induction := abstractAppliedItems_append head tail right
      cases item with
      | atom atomHead values =>
          simp only [ItemSeq.append, abstractAppliedItems]
          rw [induction]
          split
          · exact prependHole_appendAbstracted _ _ _
          · exact prependOrdinary_appendAbstracted _ _ _
      | named definition values =>
          simp only [ItemSeq.append, abstractAppliedItems]
          rw [induction]
          exact prependOrdinary_appendAbstracted _ _ _
      | identity signature ports atLeastTwo =>
          simp only [ItemSeq.append, abstractAppliedItems]
          rw [induction]
          exact prependOrdinary_appendAbstracted _ _ _
      | cut body =>
          simp only [ItemSeq.append, abstractAppliedItems]
          rw [induction]
          exact prependOrdinary_appendAbstracted _ _ _
      | bind signature body =>
          simp only [ItemSeq.append, abstractAppliedItems]
          rw [induction]
          exact prependOrdinary_appendAbstracted _ _ _

mutual

/-- Applied-atom abstraction preserves denotation with one shared relation. -/
theorem abstractApplied_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (head : Var context (.rel arguments))
    (body : Region definitions context) :
    denoteRegion pre definitionEnv env body ↔
      (abstractApplied head body).denote pre definitionEnv env
        (fun values => pre.apply (env _ head) values) := by
  cases body with
  | mk items =>
      exact
        abstractAppliedItems_denotes pre definitionEnv env head items

private theorem abstractAppliedItems_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (head : Var context (.rel arguments))
    (items : ItemSeq definitions context) :
    denoteItemSeq pre definitionEnv env items ↔
      (abstractAppliedItems head items).denote pre definitionEnv env
        (fun values => pre.apply (env _ head) values) := by
  cases items with
  | nil =>
      simp [abstractAppliedItems, UniformIntrinsicRegion.denote,
        UniformIntrinsicItemSeq.denote, all, denoteItemSeq]
  | cons item tail =>
      have tailLaw :=
        abstractAppliedItems_denotes pre definitionEnv env head tail
      generalize restExact :
          abstractAppliedItems head tail = rest at tailLaw ⊢
      cases rest
      rename_i ordinary holes
      cases item with
      | atom atomHead values =>
          cases matched :
              matchedHeadArguments? head atomHead values with
          | none =>
              simp [abstractAppliedItems, matched, prependOrdinary,
                restExact,
                UniformIntrinsicRegion.denote,
                UniformIntrinsicItemSeq.denote,
                UniformIntrinsicItem.denote, all, denoteItemSeq,
                denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
          | some result =>
              have atomExact :=
                matchedHeadArguments_denote pre env head atomHead values
                  matched
              simp [abstractAppliedItems, matched, prependHole,
                restExact,
                UniformIntrinsicRegion.denote,
                UniformIntrinsicItemSeq.denote, all, denoteItemSeq,
                denoteItem, tailLaw, atomExact, and_assoc, and_left_comm,
                and_comm]
      | named definition values =>
          simp [abstractAppliedItems, prependOrdinary,
            restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
      | identity signature ports atLeastTwo =>
          simp [abstractAppliedItems, prependOrdinary,
            restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
      | cut body =>
          have bodyLaw :=
            abstractApplied_denotes pre definitionEnv env head body
          simp [abstractAppliedItems, prependOrdinary,
            restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, bodyLaw, and_assoc, and_left_comm,
            and_comm]
      | bind signature body =>
          have bodyLaw :
              ∀ value : pre.Domain signature,
                denoteRegion pre definitionEnv (env.extend value) body ↔
                  (abstractApplied (.there head) body).denote pre
                    definitionEnv (env.extend value)
                    (fun values => pre.apply (env _ head) values) := by
            intro value
            simpa using
              abstractApplied_denotes pre definitionEnv
                (env.extend value) (.there head) body
          simp [abstractAppliedItems, prependOrdinary,
            restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, bodyLaw, and_assoc, and_left_comm,
            and_comm]

end

mutual

/--
Abstract an exact cut whose body is one atom headed by `head` as one hole.
Non-cell cuts remain in the shape and are traversed recursively.
-/
def abstractCutWrapped
    (head : Var context (.rel arguments)) :
    Region definitions context →
      UniformIntrinsicRegion definitions arguments context
  | .mk items => abstractCutWrappedItems head items

private def abstractCutWrappedItems
    (head : Var context (.rel arguments)) :
    ItemSeq definitions context →
      UniformIntrinsicRegion definitions arguments context
  | .nil => .mk .nil ⟨[]⟩
  | .cons item tail =>
      let rest := abstractCutWrappedItems head tail
      match item with
      | .cut (.mk (.cons (.atom atomHead values) .nil)) =>
          match matchedHeadArguments? head atomHead values with
          | some arguments => prependHole arguments rest
          | none =>
              prependOrdinary
                (.cut
                  (abstractCutWrapped head
                    (.mk (.cons (.atom atomHead values) .nil))))
                rest
      | .atom atomHead values =>
          prependOrdinary (.leaf (.atom atomHead values)) rest
      | .named definition values =>
          prependOrdinary (.leaf (.named definition values)) rest
      | .identity signature ports atLeastTwo =>
          prependOrdinary
            (.leaf (.identity signature ports atLeastTwo)) rest
      | .cut body =>
          prependOrdinary (.cut (abstractCutWrapped head body)) rest
      | .bind signature body =>
          prependOrdinary
            (.bind signature (abstractCutWrapped (.there head) body)) rest

end

mutual

/-- Exact cut-cell abstraction preserves denotation as pointwise negation. -/
theorem abstractCutWrapped_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (head : Var context (.rel arguments))
    (body : Region definitions context) :
    denoteRegion pre definitionEnv env body ↔
      (abstractCutWrapped head body).denote pre definitionEnv env
        (fun values => ¬pre.apply (env _ head) values) := by
  cases body with
  | mk items =>
      exact
        abstractCutWrappedItems_denotes pre definitionEnv env head items

private theorem abstractCutWrappedItems_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (head : Var context (.rel arguments))
    (items : ItemSeq definitions context) :
    denoteItemSeq pre definitionEnv env items ↔
      (abstractCutWrappedItems head items).denote pre definitionEnv env
        (fun values => ¬pre.apply (env _ head) values) := by
  cases items with
  | nil =>
      simp [abstractCutWrappedItems, UniformIntrinsicRegion.denote,
        UniformIntrinsicItemSeq.denote, all, denoteItemSeq]
  | cons item tail =>
      have tailLaw :=
        abstractCutWrappedItems_denotes pre definitionEnv env head tail
      generalize restExact :
          abstractCutWrappedItems head tail = rest at tailLaw ⊢
      cases rest
      rename_i ordinary holes
      cases item with
      | atom atomHead values =>
          simp [abstractCutWrappedItems, prependOrdinary, restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
      | named definition values =>
          simp [abstractCutWrappedItems, prependOrdinary, restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
      | identity signature ports atLeastTwo =>
          simp [abstractCutWrappedItems, prependOrdinary, restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, and_assoc, and_left_comm, and_comm]
      | cut body =>
          cases body with
          | mk bodyItems =>
              cases bodyItems with
              | nil =>
                  have bodyLaw :=
                    abstractCutWrapped_denotes pre definitionEnv env head
                      (.mk .nil)
                  simp [abstractCutWrappedItems, prependOrdinary, restExact,
                    UniformIntrinsicRegion.denote,
                    UniformIntrinsicItemSeq.denote,
                    UniformIntrinsicItem.denote, all, denoteItemSeq,
                    denoteItem, tailLaw, bodyLaw, and_assoc,
                    and_left_comm, and_comm]
              | cons bodyHead bodyTail =>
                  cases bodyHead with
                  | atom atomHead values =>
                      cases bodyTail with
                      | nil =>
                          cases matched :
                              matchedHeadArguments? head atomHead values with
                          | none =>
                              have bodyLaw :=
                                abstractCutWrapped_denotes pre definitionEnv
                                  env head
                                  (.mk
                                    (.cons (.atom atomHead values) .nil))
                              simp [abstractCutWrappedItems, matched,
                                prependOrdinary, restExact,
                                UniformIntrinsicRegion.denote,
                                UniformIntrinsicItemSeq.denote,
                                UniformIntrinsicItem.denote, all,
                                denoteItemSeq, denoteItem, tailLaw, bodyLaw,
                                and_assoc, and_left_comm, and_comm]
                          | some result =>
                              have atomExact :=
                                matchedHeadArguments_denote pre env head
                                  atomHead values matched
                              simp [abstractCutWrappedItems, matched,
                                prependHole, restExact,
                                UniformIntrinsicRegion.denote,
                                UniformIntrinsicItemSeq.denote, all,
                                denoteRegion, denoteItemSeq, denoteItem,
                                tailLaw, atomExact,
                                and_assoc, and_left_comm, and_comm]
                      | cons next rest =>
                          have bodyLaw :=
                            abstractCutWrapped_denotes pre definitionEnv env
                              head
                              (.mk
                                (.cons (.atom atomHead values)
                                  (.cons next rest)))
                          simp [abstractCutWrappedItems, prependOrdinary,
                            restExact, UniformIntrinsicRegion.denote,
                            UniformIntrinsicItemSeq.denote,
                            UniformIntrinsicItem.denote, all,
                            denoteItemSeq, denoteItem, tailLaw, bodyLaw,
                            and_assoc, and_left_comm, and_comm]
                  | named definition values =>
                      have bodyLaw :=
                        abstractCutWrapped_denotes pre definitionEnv env head
                          (.mk (.cons (.named definition values) bodyTail))
                      simp [abstractCutWrappedItems, prependOrdinary,
                        restExact, UniformIntrinsicRegion.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw, bodyLaw, and_assoc,
                        and_left_comm, and_comm]
                  | identity signature ports atLeastTwo =>
                      have bodyLaw :=
                        abstractCutWrapped_denotes pre definitionEnv env head
                          (.mk
                            (.cons
                              (.identity signature ports atLeastTwo)
                              bodyTail))
                      simp [abstractCutWrappedItems, prependOrdinary,
                        restExact, UniformIntrinsicRegion.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw, bodyLaw, and_assoc,
                        and_left_comm, and_comm]
                  | cut nested =>
                      have bodyLaw :=
                        abstractCutWrapped_denotes pre definitionEnv env head
                          (.mk (.cons (.cut nested) bodyTail))
                      simp [abstractCutWrappedItems, prependOrdinary,
                        restExact, UniformIntrinsicRegion.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw, bodyLaw, and_assoc,
                        and_left_comm, and_comm]
                  | bind signature nested =>
                      have bodyLaw :=
                        abstractCutWrapped_denotes pre definitionEnv env head
                          (.mk (.cons (.bind signature nested) bodyTail))
                      simp [abstractCutWrappedItems, prependOrdinary,
                        restExact, UniformIntrinsicRegion.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw, bodyLaw, and_assoc,
                        and_left_comm, and_comm]
      | bind signature body =>
          have bodyLaw :
              ∀ value : pre.Domain signature,
                denoteRegion pre definitionEnv (env.extend value) body ↔
                  (abstractCutWrapped (.there head) body).denote pre
                    definitionEnv (env.extend value)
                    (fun values => ¬pre.apply (env _ head) values) := by
            intro value
            simpa using
              abstractCutWrapped_denotes pre definitionEnv
                (env.extend value) (.there head) body
          simp [abstractCutWrappedItems, prependOrdinary, restExact,
            UniformIntrinsicRegion.denote,
            UniformIntrinsicItemSeq.denote,
            UniformIntrinsicItem.denote, all, denoteItemSeq,
            denoteItem, tailLaw, bodyLaw, and_assoc, and_left_comm,
            and_comm]

end

/-- Intermediate split abstraction before the two branches are paired. -/
private structure ParallelRaw
    (definitions : List (List Sig))
    (arguments context : List Sig) where
  ordinary : UniformIntrinsicItemSeq definitions arguments context
  first : UniformIntrinsicHoles arguments context
  second : UniformIntrinsicHoles arguments context

private def ParallelRaw.paired?
    (raw : ParallelRaw definitions arguments context) :
    Option (UniformIntrinsicRegion definitions arguments context) :=
  if paired : raw.first.values = raw.second.values then
    some (.mk raw.ordinary raw.first)
  else
    none

private def ParallelRaw.denote
    (raw : ParallelRaw definitions arguments context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (firstRelation secondRelation :
      pre.Domain (.rel arguments)) : Prop :=
  UniformIntrinsicItemSeq.denote pre definitionEnv env
      (fun values =>
        pre.apply firstRelation values ∧
          pre.apply secondRelation values)
      raw.ordinary ∧
    all raw.first.values
      (fun values =>
        pre.apply firstRelation (Vars.denote env values)) ∧
    all raw.second.values
      (fun values =>
        pre.apply secondRelation (Vars.denote env values))

private theorem all_pair
    (values : List α)
    (left right : α → Prop) :
    all values left ∧ all values right ↔
      all values (fun value => left value ∧ right value) := by
  constructor
  · rintro ⟨leftHolds, rightHolds⟩ value member
    exact ⟨leftHolds value member, rightHolds value member⟩
  · intro paired
    exact
      ⟨fun value member => (paired value member).1,
        fun value member => (paired value member).2⟩

private theorem ParallelRaw.paired_denotes
    (raw : ParallelRaw definitions arguments context)
    (shape : UniformIntrinsicRegion definitions arguments context)
    (accepted : raw.paired? = some shape)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (firstRelation secondRelation :
      pre.Domain (.rel arguments)) :
    raw.denote pre definitionEnv env firstRelation secondRelation ↔
      shape.denote pre definitionEnv env
        (fun values =>
          pre.apply firstRelation values ∧
            pre.apply secondRelation values) := by
  unfold ParallelRaw.paired? at accepted
  split at accepted
  · rename_i paired
    have shapeExact := Option.some.inj accepted
    subst shape
    unfold ParallelRaw.denote
    rw [← paired]
    simp [UniformIntrinsicRegion.denote, all_pair,
      and_assoc]
  · contradiction

mutual

private def abstractParallelRaw
    (firstHead secondHead : Var context (.rel arguments)) :
    Region definitions context → Option (ParallelRaw definitions arguments context)
  | .mk items => abstractParallelItemsRaw firstHead secondHead items

private def abstractParallelItemsRaw
    (firstHead secondHead : Var context (.rel arguments)) :
    ItemSeq definitions context →
      Option (ParallelRaw definitions arguments context)
  | .nil => some ⟨.nil, ⟨[]⟩, ⟨[]⟩⟩
  | .cons item tail => do
      let rest ← abstractParallelItemsRaw firstHead secondHead tail
      match item with
      | .atom atomHead values =>
          match matchedHeadArguments? firstHead atomHead values with
          | some arguments =>
              pure
                { rest with
                  first := ⟨arguments :: rest.first.values⟩ }
          | none =>
              match matchedHeadArguments? secondHead atomHead values with
              | some arguments =>
                  pure
                    { rest with
                      second := ⟨arguments :: rest.second.values⟩ }
              | none =>
                  pure
                    { rest with
                      ordinary :=
                        .cons (.leaf (.atom atomHead values)) rest.ordinary }
      | .named definition values =>
          pure
            { rest with
              ordinary :=
                .cons (.leaf (.named definition values)) rest.ordinary }
      | .identity signature ports atLeastTwo =>
          pure
            { rest with
              ordinary :=
                .cons
                  (.leaf (.identity signature ports atLeastTwo))
                  rest.ordinary }
      | .cut body =>
          let nested ← abstractParallelRaw firstHead secondHead body
          let paired ← nested.paired?
          pure
            { rest with
              ordinary := .cons (.cut paired) rest.ordinary }
      | .bind signature body =>
          let nested ←
            abstractParallelRaw (.there firstHead) (.there secondHead) body
          let paired ← nested.paired?
          pure
            { rest with
              ordinary := .cons (.bind signature paired) rest.ordinary }

end

mutual

private theorem abstractParallelRaw_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (firstHead secondHead : Var context (.rel arguments))
    (body : Region definitions context)
    (raw : ParallelRaw definitions arguments context)
    (accepted :
      abstractParallelRaw firstHead secondHead body = some raw) :
    denoteRegion pre definitionEnv env body ↔
      raw.denote pre definitionEnv env (env _ firstHead)
        (env _ secondHead) := by
  cases body with
  | mk items =>
      exact
        abstractParallelItemsRaw_denotes pre definitionEnv env firstHead
          secondHead items raw accepted

private theorem abstractParallelItemsRaw_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (firstHead secondHead : Var context (.rel arguments))
    (items : ItemSeq definitions context)
    (raw : ParallelRaw definitions arguments context)
    (accepted :
      abstractParallelItemsRaw firstHead secondHead items = some raw) :
    denoteItemSeq pre definitionEnv env items ↔
      raw.denote pre definitionEnv env (env _ firstHead)
        (env _ secondHead) := by
  cases items with
  | nil =>
      simp [abstractParallelItemsRaw] at accepted
      cases accepted
      simp [ParallelRaw.denote, UniformIntrinsicItemSeq.denote, all,
        denoteItemSeq]
  | cons item tail =>
      unfold abstractParallelItemsRaw at accepted
      cases tailExact :
          abstractParallelItemsRaw firstHead secondHead tail with
      | none =>
          simp [tailExact] at accepted
      | some rest =>
          have tailLaw :=
            abstractParallelItemsRaw_denotes pre definitionEnv env
              firstHead secondHead tail rest tailExact
          simp only [tailExact, Option.bind_some] at accepted
          cases item with
          | atom atomHead values =>
              cases firstMatched :
                  matchedHeadArguments? firstHead atomHead values with
              | some result =>
                  simp [firstMatched] at accepted
                  subst raw
                  have atomExact :=
                    matchedHeadArguments_denote pre env firstHead atomHead
                      values firstMatched
                  simp [ParallelRaw.denote, UniformIntrinsicItemSeq.denote,
                    all, denoteItemSeq, denoteItem, tailLaw, atomExact,
                    and_assoc, and_left_comm, and_comm]
              | none =>
                  cases secondMatched :
                      matchedHeadArguments? secondHead atomHead values with
                  | some result =>
                      simp [firstMatched, secondMatched] at accepted
                      subst raw
                      have atomExact :=
                        matchedHeadArguments_denote pre env secondHead
                          atomHead values secondMatched
                      simp [ParallelRaw.denote,
                        UniformIntrinsicItemSeq.denote, all,
                        denoteItemSeq, denoteItem, tailLaw, atomExact,
                        and_assoc, and_left_comm, and_comm]
                  | none =>
                      simp [firstMatched, secondMatched] at accepted
                      subst raw
                      simp [ParallelRaw.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw, and_assoc, and_left_comm,
                        and_comm]
          | named definition values =>
              simp at accepted
              subst raw
              simp [ParallelRaw.denote, UniformIntrinsicItemSeq.denote,
                UniformIntrinsicItem.denote, all, denoteItemSeq, denoteItem,
                tailLaw, and_assoc, and_left_comm, and_comm]
          | identity signature ports atLeastTwo =>
              simp at accepted
              subst raw
              simp [ParallelRaw.denote, UniformIntrinsicItemSeq.denote,
                UniformIntrinsicItem.denote, all, denoteItemSeq, denoteItem,
                tailLaw, and_assoc, and_left_comm, and_comm]
          | cut body =>
              cases nestedExact :
                  abstractParallelRaw firstHead secondHead body with
              | none =>
                  simp [nestedExact] at accepted
              | some nested =>
                  cases pairedExact : nested.paired? with
                  | none =>
                      simp [nestedExact, pairedExact] at accepted
                  | some paired =>
                      simp [nestedExact, pairedExact] at accepted
                      subst raw
                      have nestedLaw :=
                        abstractParallelRaw_denotes pre definitionEnv env
                          firstHead secondHead body nested nestedExact
                      have pairedLaw :=
                        nested.paired_denotes paired pairedExact pre
                          definitionEnv env (env _ firstHead)
                          (env _ secondHead)
                      simp only [denoteItemSeq, denoteItem]
                      rw [nestedLaw, pairedLaw]
                      simp [ParallelRaw.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw,
                        and_assoc, and_left_comm, and_comm]
          | bind signature body =>
              cases nestedExact :
                  abstractParallelRaw (.there firstHead)
                    (.there secondHead) body with
              | none =>
                  simp [nestedExact] at accepted
              | some nested =>
                  cases pairedExact : nested.paired? with
                  | none =>
                      simp [nestedExact, pairedExact] at accepted
                  | some paired =>
                      simp [nestedExact, pairedExact] at accepted
                      subst raw
                      have nestedLaw :
                          ∀ value : pre.Domain signature,
                            denoteRegion pre definitionEnv
                                (env.extend value) body ↔
                              nested.denote pre definitionEnv
                                (env.extend value) (env _ firstHead)
                                (env _ secondHead) := by
                        intro value
                        simpa using
                          abstractParallelRaw_denotes pre definitionEnv
                            (env.extend value) (.there firstHead)
                            (.there secondHead) body nested nestedExact
                      have pairedLaw :
                          ∀ value : pre.Domain signature,
                            nested.denote pre definitionEnv
                                (env.extend value) (env _ firstHead)
                                (env _ secondHead) ↔
                              paired.denote pre definitionEnv
                                (env.extend value)
                                (fun values =>
                                  pre.apply (env _ firstHead) values ∧
                                    pre.apply (env _ secondHead) values) := by
                        intro value
                        exact
                          nested.paired_denotes paired pairedExact pre
                            definitionEnv (env.extend value)
                            (env _ firstHead) (env _ secondHead)
                      simp only [denoteItemSeq, denoteItem]
                      simp only [nestedLaw, pairedLaw]
                      simp [ParallelRaw.denote,
                        UniformIntrinsicItemSeq.denote,
                        UniformIntrinsicItem.denote, all, denoteItemSeq,
                        denoteItem, tailLaw,
                        and_assoc, and_left_comm, and_comm]

end

/--
Abstract co-located applications of two parallel witness wires into one hole.
Acceptance requires the ordered argument tuples to pair exactly at every
ambient cut/binder position, not merely globally.
-/
def abstractParallel
    (firstHead secondHead : Var context (.rel arguments))
    (body : Region definitions context) :
    Option (UniformIntrinsicRegion definitions arguments context) := do
  let raw ← abstractParallelRaw firstHead secondHead body
  raw.paired?

/-- Accepted parallel abstraction denotes pointwise conjunction at every hole. -/
theorem abstractParallel_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (firstHead secondHead : Var context (.rel arguments))
    (body : Region definitions context)
    (shape : UniformIntrinsicRegion definitions arguments context)
    (accepted : abstractParallel firstHead secondHead body = some shape) :
    denoteRegion pre definitionEnv env body ↔
      shape.denote pre definitionEnv env
        (fun values =>
          pre.apply (env _ firstHead) values ∧
            pre.apply (env _ secondHead) values) := by
  unfold abstractParallel at accepted
  cases rawExact :
      abstractParallelRaw firstHead secondHead body with
  | none =>
      simp [rawExact] at accepted
  | some raw =>
      simp only [rawExact, Option.bind_some] at accepted
      exact
        (abstractParallelRaw_denotes pre definitionEnv env firstHead
          secondHead body raw rawExact).trans
          (raw.paired_denotes shape accepted pre definitionEnv env
            (env _ firstHead) (env _ secondHead))

/-- Check one simultaneous cut-cell shape after both bodies share a context. -/
def checkCutShape
    (sourceHead targetHead : Var context (.rel arguments))
    (sourceBody targetBody : Region definitions context) : Bool :=
  decide
    (abstractApplied sourceHead sourceBody =
      abstractCutWrapped targetHead targetBody)

/-- Check one simultaneous parallel-cell shape in a shared intrinsic context. -/
def checkParallelShape
    (sourceHead firstHead secondHead :
      Var context (.rel arguments))
    (sourceBody targetBody : Region definitions context) : Bool :=
  match abstractParallel firstHead secondHead targetBody with
  | none => false
  | some targetShape =>
      decide (abstractApplied sourceHead sourceBody = targetShape)

/--
A successful cut-shape check turns pointwise cell equivalence into complete
acted-scope body equivalence, through every retained cut and binder.
-/
theorem checkCutShape_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (sourceHead targetHead : Var context (.rel arguments))
    (sourceBody targetBody : Region definitions context)
    (accepted :
      checkCutShape sourceHead targetHead sourceBody targetBody = true)
    (pointwise :
      ∀ values,
        pre.apply (env _ sourceHead) values ↔
          ¬pre.apply (env _ targetHead) values) :
    denoteRegion pre definitionEnv env sourceBody ↔
      denoteRegion pre definitionEnv env targetBody := by
  have same :
      abstractApplied sourceHead sourceBody =
        abstractCutWrapped targetHead targetBody := by
    exact of_decide_eq_true (by
      simpa [checkCutShape] using accepted)
  let sourceShape := abstractApplied sourceHead sourceBody
  have sourceLaw :=
    abstractApplied_denotes pre definitionEnv env sourceHead sourceBody
  have targetLaw :=
    abstractCutWrapped_denotes pre definitionEnv env targetHead targetBody
  have shapeLaw :
      sourceShape.denote pre definitionEnv env
          (fun values => pre.apply (env _ sourceHead) values) ↔
        sourceShape.denote pre definitionEnv env
          (fun values => ¬pre.apply (env _ targetHead) values) :=
    sourceShape.denote_site_congr pre definitionEnv env _ _ pointwise
  have targetAtSource :
      sourceShape.denote pre definitionEnv env
          (fun values => ¬pre.apply (env _ targetHead) values) ↔
        denoteRegion pre definitionEnv env targetBody := by
    simpa [sourceShape, same] using targetLaw.symm
  exact sourceLaw.trans (shapeLaw.trans targetAtSource)

/--
A successful split-shape check turns pointwise source/pair equivalence into
complete acted-scope body equivalence.
-/
theorem checkParallelShape_denotes
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context)
    (sourceHead firstHead secondHead :
      Var context (.rel arguments))
    (sourceBody targetBody : Region definitions context)
    (accepted :
      checkParallelShape sourceHead firstHead secondHead sourceBody
        targetBody = true)
    (pointwise :
      ∀ values,
        pre.apply (env _ sourceHead) values ↔
          (pre.apply (env _ firstHead) values ∧
            pre.apply (env _ secondHead) values)) :
    denoteRegion pre definitionEnv env sourceBody ↔
      denoteRegion pre definitionEnv env targetBody := by
  unfold checkParallelShape at accepted
  cases targetExact :
      abstractParallel firstHead secondHead targetBody with
  | none =>
      simp [targetExact] at accepted
  | some targetShape =>
      have same :
          abstractApplied sourceHead sourceBody = targetShape := by
        exact of_decide_eq_true (by
          simpa [targetExact] using accepted)
      let sourceShape := abstractApplied sourceHead sourceBody
      have sourceLaw :=
        abstractApplied_denotes pre definitionEnv env sourceHead sourceBody
      have targetLaw :=
        abstractParallel_denotes pre definitionEnv env firstHead secondHead
          targetBody targetShape targetExact
      have shapeLaw :
          sourceShape.denote pre definitionEnv env
              (fun values => pre.apply (env _ sourceHead) values) ↔
            sourceShape.denote pre definitionEnv env
              (fun values =>
                pre.apply (env _ firstHead) values ∧
                  pre.apply (env _ secondHead) values) :=
        sourceShape.denote_site_congr pre definitionEnv env _ _ pointwise
      have targetAtSource :
          sourceShape.denote pre definitionEnv env
              (fun values =>
                pre.apply (env _ firstHead) values ∧
                  pre.apply (env _ secondHead) values) ↔
            denoteRegion pre definitionEnv env targetBody := by
        simpa [sourceShape, same] using targetLaw.symm
      exact sourceLaw.trans (shapeLaw.trans targetAtSource)

end UniformIntrinsicRegion

namespace ConcreteFactorization

open ConcreteWireQuantifier

/--
One checker-owned dense batch erasure. The retained target is exactly the
canonical `batchRemovalCandidate`; no caller can substitute another core.
-/
structure CheckedBatchErasure
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) where
  private mk ::
  plan :
    Internal.BatchRemovalPlan source removedRegions removedNodes removedWires
  checked : CheckedDiagram definitions
  private generated :
    checked.val = Internal.batchRemovalCandidate plan

namespace CheckedBatchErasure

/-- Execute and check one exact canonical batch erasure. -/
def check
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    Option
      (CheckedBatchErasure source removedRegions removedNodes removedWires) := do
  let plan ←
    Internal.checkBatchRemovalPlan? source removedRegions removedNodes
      removedWires
  match accepted :
      ConcreteDiagram.checkWellFormed definitions
        (Internal.batchRemovalCandidate plan) with
  | .error _ => none
  | .ok checked =>
      some
        ⟨plan, checked,
          ConcreteDiagram.checkWellFormed_preserves_input accepted⟩

/-- A structural plan with a well-formed canonical target cannot be refused. -/
theorem check_complete
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      Internal.BatchRemovalPlan source removedRegions removedNodes
        removedWires)
    (wellFormed :
      (Internal.batchRemovalCandidate plan).WellFormed definitions) :
    ∃ erasure,
      check source removedRegions removedNodes removedWires = some erasure := by
  let checked : CheckedDiagram definitions :=
    ⟨Internal.batchRemovalCandidate plan, wellFormed⟩
  let erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires :=
    ⟨plan, checked, rfl⟩
  refine ⟨erasure, ?_⟩
  simp [check, plan.checked, checked, erasure]
  split
  · rename_i error rejected
    have accepted := ConcreteDiagram.checkWellFormed_complete wellFormed
    rw [rejected] at accepted
    contradiction
  · rename_i checked' accepted
    have checkedExact : checked = checked' :=
      Except.ok.inj
        ((ConcreteDiagram.checkWellFormed_complete wellFormed).symm.trans
          accepted)
    subst checked'
    rfl

/-- The checked core is the exact canonical batch-erasure candidate. -/
theorem checked_exact
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires) :
    erasure.checked.val =
      Internal.batchRemovalCandidate erasure.plan :=
  erasure.generated

/-- Image of one retained source region in the exact checked erasure. -/
def regionImage?
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (region : source.val.RegionId) :
    Option erasure.checked.val.RegionId :=
  if retained :
      region ∈ Internal.retainedRegions source removedRegions then
    some
      (Internal.checkedRegion erasure.checked_exact
        (Internal.retainedRegionIndex source removedRegions region retained))
  else
    none

/-- Image of one retained source wire in the exact checked erasure. -/
def wireImage?
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : source.val.WireId) :
    Option erasure.checked.val.WireId :=
  if retained :
      wire ∈ Internal.retainedWires source removedWires then
    some
      (Internal.checkedWire erasure.checked_exact
        (Internal.retainedWireIndex source removedWires wire retained))
  else
    none

/-- Dense checked-erasure image of one proved-retained source wire. -/
def retainedWire
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source removedWires) :
    erasure.checked.val.WireId :=
  Internal.checkedWire erasure.checked_exact
    (Internal.retainedWireIndex source removedWires wire retained)

/-- A retained wire's dense image preserves its signature exactly. -/
theorem retainedWire_signature
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source removedWires) :
    (erasure.checked.val.wires
        (erasure.retainedWire wire retained)).sig =
      (source.val.wires wire).sig := by
  calc
    (erasure.checked.val.wires
        (erasure.retainedWire wire retained)).sig =
        ((Internal.batchRemovalCandidate erasure.plan).wires
          (Internal.retainedWireIndex source removedWires wire
            retained)).sig :=
      Internal.checkedWire_signature_transport erasure.checked_exact _
    _ = (source.val.wires wire).sig := by
      unfold Internal.batchRemovalCandidate Internal.batchWireTable
        Internal.sourceRetainedWire Internal.retainedWireIndex
      change
        (source.val.wires
          ((Internal.retainedWires source removedWires).get
            (DenseList.index
              (Internal.retainedWires source removedWires) wire
              retained))).sig =
          (source.val.wires wire).sig
      rw [DenseList.get_index]

/--
Recover the unique original wire represented by one dense checked-erasure
wire. This is the inverse direction needed to align independently erased
source and target contexts through a common core.
-/
def originalWire
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : erasure.checked.val.WireId) :
    source.val.WireId :=
  Internal.sourceRetainedWire source removedWires
    (Fin.cast
      (congrArg ConcreteDiagram.wireCount erasure.checked_exact) wire)

/-- Recovering an erasure wire preserves its signature exactly. -/
theorem originalWire_signature
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : erasure.checked.val.WireId) :
    (source.val.wires (erasure.originalWire wire)).sig =
      (erasure.checked.val.wires wire).sig := by
  let candidateWire :
      (Internal.batchRemovalCandidate erasure.plan).WireId :=
    Fin.cast
      (congrArg ConcreteDiagram.wireCount erasure.checked_exact) wire
  have checkedWireExact :
      Internal.checkedWire erasure.checked_exact candidateWire = wire := by
    apply Fin.ext
    rfl
  calc
    (source.val.wires (erasure.originalWire wire)).sig =
        ((Internal.batchRemovalCandidate erasure.plan).wires
          candidateWire).sig := by
      rfl
    _ =
        (erasure.checked.val.wires
          (Internal.checkedWire erasure.checked_exact candidateWire)).sig :=
      (Internal.checkedWire_signature_transport
        erasure.checked_exact candidateWire).symm
    _ = (erasure.checked.val.wires wire).sig := by
      rw [checkedWireExact]

/-- Every recovered original wire belongs to the retained dense table. -/
theorem originalWire_mem_retained
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : erasure.checked.val.WireId) :
    erasure.originalWire wire ∈
      Internal.retainedWires source removedWires := by
  unfold originalWire Internal.sourceRetainedWire
  exact List.get_mem _ _

/-- Recovering a proved retained wire returns that exact source wire. -/
@[simp] theorem originalWire_retainedWire
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source removedWires) :
    erasure.originalWire (erasure.retainedWire wire retained) = wire := by
  let recovered :
      Fin (Internal.retainedWires source removedWires).length :=
    Fin.cast
      (congrArg ConcreteDiagram.wireCount erasure.checked_exact)
      (erasure.retainedWire wire retained)
  have recoveredExact :
      recovered =
        Internal.retainedWireIndex source removedWires wire retained := by
    apply Fin.ext
    rfl
  unfold originalWire
  change Internal.sourceRetainedWire source removedWires recovered = wire
  rw [recoveredExact]
  unfold Internal.sourceRetainedWire Internal.retainedWireIndex
  rw [DenseList.get_index]

/-- Re-embedding a recovered wire returns the exact dense checked wire. -/
@[simp] theorem retainedWire_originalWire
    (erasure :
      CheckedBatchErasure source removedRegions removedNodes removedWires)
    (wire : erasure.checked.val.WireId) :
    erasure.retainedWire (erasure.originalWire wire)
        (erasure.originalWire_mem_retained wire) =
      wire := by
  let position :
      Fin (Internal.retainedWires source removedWires).length :=
    Fin.cast
      (congrArg ConcreteDiagram.wireCount erasure.checked_exact) wire
  have retainedNodup :
      (Internal.retainedWires source removedWires).Nodup := by
    exact
      (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have indexExact :
      Internal.retainedWireIndex source removedWires
          (erasure.originalWire wire)
          (erasure.originalWire_mem_retained wire) =
        position := by
    unfold Internal.retainedWireIndex originalWire
      Internal.sourceRetainedWire
    exact
      DenseList.index_get
        (Internal.retainedWires source removedWires) retainedNodup position
  unfold retainedWire
  rw [indexExact]
  apply Fin.ext
  rfl

end CheckedBatchErasure

/--
Independent source and target erasures meet at one checked concrete core,
modulo the repository's canonical concrete isomorphism.
-/
structure CommonCoreReceipt
    (source target : CheckedDiagram definitions) where
  private mk ::
  sourceRemovedRegions : List source.val.RegionId
  sourceRemovedNodes : List source.val.NodeId
  sourceRemovedWires : List source.val.WireId
  targetRemovedRegions : List target.val.RegionId
  targetRemovedNodes : List target.val.NodeId
  targetRemovedWires : List target.val.WireId
  sourceErasure :
    CheckedBatchErasure source sourceRemovedRegions sourceRemovedNodes
      sourceRemovedWires
  targetErasure :
    CheckedBatchErasure target targetRemovedRegions targetRemovedNodes
      targetRemovedWires
  coreIso :
    ConcreteIso sourceErasure.checked.val targetErasure.checked.val

namespace CommonCoreReceipt

/-- Assemble a common-core receipt from two checker-owned erasures and an
exact isomorphism between their checked outputs. -/
def ofErasures
    (source : CheckedDiagram definitions)
    (target : CheckedDiagram definitions)
    (sourceRemovedRegions : List source.val.RegionId)
    (sourceRemovedNodes : List source.val.NodeId)
    (sourceRemovedWires : List source.val.WireId)
    (targetRemovedRegions : List target.val.RegionId)
    (targetRemovedNodes : List target.val.NodeId)
    (targetRemovedWires : List target.val.WireId)
    (sourceErasure :
      CheckedBatchErasure source sourceRemovedRegions sourceRemovedNodes
        sourceRemovedWires)
    (targetErasure :
      CheckedBatchErasure target targetRemovedRegions targetRemovedNodes
        targetRemovedWires)
    (coreIso :
      ConcreteIso sourceErasure.checked.val targetErasure.checked.val) :
    CommonCoreReceipt source target :=
  ⟨sourceRemovedRegions, sourceRemovedNodes, sourceRemovedWires,
    targetRemovedRegions, targetRemovedNodes, targetRemovedWires,
    sourceErasure, targetErasure, coreIso⟩

/-- Transport one proved-retained source wire through the checked common core. -/
def forwardRetainedWire
    (core : CommonCoreReceipt source target)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source core.sourceRemovedWires) :
    target.val.WireId :=
  core.targetErasure.originalWire
    (core.coreIso.wires
      (core.sourceErasure.retainedWire wire retained))

/-- Common-core forward transport preserves the wire signature. -/
theorem forwardRetainedWire_signature
    (core : CommonCoreReceipt source target)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source core.sourceRemovedWires) :
    (target.val.wires (core.forwardRetainedWire wire retained)).sig =
      (source.val.wires wire).sig := by
  calc
    (target.val.wires (core.forwardRetainedWire wire retained)).sig =
        (core.targetErasure.checked.val.wires
          (core.coreIso.wires
            (core.sourceErasure.retainedWire wire retained))).sig :=
      core.targetErasure.originalWire_signature _
    _ =
        (core.sourceErasure.checked.val.wires
          (core.sourceErasure.retainedWire wire retained)).sig :=
      core.coreIso.wire_signature _
    _ = (source.val.wires wire).sig :=
      core.sourceErasure.retainedWire_signature wire retained

/-- Transport one proved-retained target wire backward through the common core. -/
def backwardRetainedWire
    (core : CommonCoreReceipt source target)
    (wire : target.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires target core.targetRemovedWires) :
    source.val.WireId :=
  core.sourceErasure.originalWire
    (core.coreIso.wires.symm
      (core.targetErasure.retainedWire wire retained))

/-- Common-core backward transport preserves the wire signature. -/
theorem backwardRetainedWire_signature
    (core : CommonCoreReceipt source target)
    (wire : target.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires target core.targetRemovedWires) :
    (source.val.wires (core.backwardRetainedWire wire retained)).sig =
      (target.val.wires wire).sig := by
  calc
    (source.val.wires (core.backwardRetainedWire wire retained)).sig =
        (core.sourceErasure.checked.val.wires
          (core.coreIso.wires.symm
            (core.targetErasure.retainedWire wire retained))).sig :=
      core.sourceErasure.originalWire_signature _
    _ =
        (core.targetErasure.checked.val.wires
          (core.targetErasure.retainedWire wire retained)).sig :=
      core.coreIso.symm.wire_signature _
    _ = (target.val.wires wire).sig :=
      core.targetErasure.retainedWire_signature wire retained

/-- Forward then backward common-core transport returns the retained source. -/
@[simp] theorem backward_forwardRetainedWire
    (core : CommonCoreReceipt source target)
    (wire : source.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires source core.sourceRemovedWires) :
    core.backwardRetainedWire
        (core.forwardRetainedWire wire retained)
        (core.targetErasure.originalWire_mem_retained
          (core.coreIso.wires
            (core.sourceErasure.retainedWire wire retained))) =
      wire := by
  unfold backwardRetainedWire forwardRetainedWire
  rw [CheckedBatchErasure.retainedWire_originalWire]
  have isoExact :
      core.coreIso.wires.symm
          (core.coreIso.wires
            (core.sourceErasure.retainedWire wire retained)) =
        core.sourceErasure.retainedWire wire retained :=
    core.coreIso.wires.left_inv _
  rw [isoExact, CheckedBatchErasure.originalWire_retainedWire]

/-- Backward then forward common-core transport returns the retained target. -/
@[simp] theorem forward_backwardRetainedWire
    (core : CommonCoreReceipt source target)
    (wire : target.val.WireId)
    (retained :
      wire ∈ Internal.retainedWires target core.targetRemovedWires) :
    core.forwardRetainedWire
        (core.backwardRetainedWire wire retained)
        (core.sourceErasure.originalWire_mem_retained
          (core.coreIso.wires.symm
            (core.targetErasure.retainedWire wire retained))) =
      wire := by
  unfold forwardRetainedWire backwardRetainedWire
  rw [CheckedBatchErasure.retainedWire_originalWire]
  have isoExact :
      core.coreIso.wires
          (core.coreIso.wires.symm
            (core.targetErasure.retainedWire wire retained)) =
        core.targetErasure.retainedWire wire retained :=
    core.coreIso.wires.right_inv _
  rw [isoExact, CheckedBatchErasure.originalWire_retainedWire]

end CommonCoreReceipt

/-- Check both canonical erasures and their exact common-core isomorphism. -/
def checkCommonCore
    (source target : CheckedDiagram definitions)
    (sourceRemovedRegions : List source.val.RegionId)
    (sourceRemovedNodes : List source.val.NodeId)
    (sourceRemovedWires : List source.val.WireId)
    (targetRemovedRegions : List target.val.RegionId)
    (targetRemovedNodes : List target.val.NodeId)
    (targetRemovedWires : List target.val.WireId) :
    Option (CommonCoreReceipt source target) := do
  let sourceErasure ←
    CheckedBatchErasure.check source sourceRemovedRegions sourceRemovedNodes
      sourceRemovedWires
  let targetErasure ←
    CheckedBatchErasure.check target targetRemovedRegions targetRemovedNodes
      targetRemovedWires
  let coreIso ←
    ConcreteIsoSearch.findConcreteIso? sourceErasure.checked.val
      targetErasure.checked.val
  pure
    ⟨sourceRemovedRegions, sourceRemovedNodes, sourceRemovedWires,
      targetRemovedRegions, targetRemovedNodes, targetRemovedWires,
      sourceErasure, targetErasure, coreIso⟩

end ConcreteFactorization

/-!
The definitions below are the pure logical core of the uniform witness law.
They deliberately do not represent concrete outer diagram contexts: ambient
binders require the typed, environment-indexed `DiagramContext` zipper used
by the rule soundness layer.
-/

/-- A propositional context with one hole per logical wire site. -/
structure UniformSiteContext (siteCount : Nat) where
  private mk ::
  fill : (Fin siteCount → Prop) → Prop
  private congruent :
    ∀ left right,
      (∀ site, left site ↔ right site) →
        (fill left ↔ fill right)

namespace UniformSiteContext

/-- One context hole. -/
def hole (site : Fin siteCount) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => values site) (by
    intro left right pointwise
    exact pointwise site)

/-- Context independent of every site. -/
def fixed (proposition : Prop) : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun _ => proposition) (by
    intro _ _ _
    exact Iff.rfl)

/-- Conjunction of two independently checked site contexts. -/
def conjoin
    (left right : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => left.fill values ∧ right.fill values) (by
      intro source target pointwise
      exact and_congr
        (left.congruent source target pointwise)
        (right.congruent source target pointwise))

/-- A local cut reverses one site's polarity without affecting uniformity. -/
def cut (inner : UniformSiteContext siteCount) :
    UniformSiteContext siteCount :=
  UniformSiteContext.mk
    (fun values => ¬ inner.fill values) (by
      intro source target pointwise
      exact not_congr (inner.congruent source target pointwise))

/-- Exhaustive conjunction of all logical site propositions. -/
def all : UniformSiteContext siteCount :=
  UniformSiteContext.mk (fun values => ∀ site, values site) (by
    intro source target pointwise
    constructor
    · intro sourceHolds site
      exact (pointwise site).mp (sourceHolds site)
    · intro targetHolds site
      exact (pointwise site).mpr (targetHolds site))

/-- Pointwise equality composes through the complete checked site context. -/
theorem fill_congr
    (context : UniformSiteContext siteCount)
    {left right : Fin siteCount → Prop}
    (pointwise : ∀ site, left site ↔ right site) :
    context.fill left ↔ context.fill right :=
  context.congruent left right pointwise

end UniformSiteContext

/-- Pure logical body factorization used to prove the shared-witness law. -/
structure UniformSiteBodyFactorization
    (siteCount : Nat)
    (SourceWitness TargetWitness : Type w) where
  private mk ::
  sourceAt : SourceWitness → Fin siteCount → Prop
  targetAt : TargetWitness → Fin siteCount → Prop
  sourceBody : SourceWitness → Prop
  targetBody : TargetWitness → Prop
  private pointwise_exact :
    ∀ source target,
      (∀ site, sourceAt source site ↔ targetAt target site) →
        (sourceBody source ↔ targetBody target)

namespace UniformSiteBodyFactorization

/-- Pointwise cell equivalence fills the complete logical body. -/
theorem congruent
    (factorization :
      UniformSiteBodyFactorization siteCount SourceWitness TargetWitness)
    (source : SourceWitness)
    (target : TargetWitness)
    (pointwise :
      ∀ site,
        factorization.sourceAt source site ↔
          factorization.targetAt target site) :
    factorization.sourceBody source ↔
      factorization.targetBody target :=
  factorization.pointwise_exact source target pointwise

/-- Definitionally exact factorization of one logical multi-hole context. -/
private def ofLogicalContext
    (context : UniformSiteContext siteCount)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    UniformSiteBodyFactorization siteCount SourceWitness TargetWitness :=
  UniformSiteBodyFactorization.mk sourceAt targetAt
    (fun witness => context.fill (sourceAt witness))
    (fun witness => context.fill (targetAt witness)) (by
      intro source target pointwise
      exact context.fill_congr pointwise)

end UniformSiteBodyFactorization

/--
One explicitly logical uniform rewrite. It proves only the shared-witness
body law; concrete scope transport is owned separately by an
environment-indexed semantic zipper.
-/
structure LogicalUniformRewrite
    (siteCount : Nat)
    (SourceWitness TargetWitness : Type w) where
  private mk ::
  siteFactorization :
    UniformSiteBodyFactorization siteCount SourceWitness TargetWitness

namespace LogicalUniformRewrite

/-- Build the pure shared-witness law from one logical site context. -/
def ofContext
    (siteContext : UniformSiteContext siteCount)
    (sourceAt : SourceWitness → Fin siteCount → Prop)
    (targetAt : TargetWitness → Fin siteCount → Prop) :
    LogicalUniformRewrite siteCount SourceWitness TargetWitness :=
  ⟨UniformSiteBodyFactorization.ofLogicalContext
    siteContext sourceAt targetAt⟩

/-- Source proposition at one logical site. -/
def sourceAt
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) :
    SourceWitness → Fin siteCount → Prop :=
  rewrite.siteFactorization.sourceAt

/-- Target proposition at the corresponding logical site. -/
def targetAt
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) :
    TargetWitness → Fin siteCount → Prop :=
  rewrite.siteFactorization.targetAt

/-- Pointwise site equivalence fills the complete logical body. -/
theorem body_congruent
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness)
    (source : SourceWitness)
    (target : TargetWitness)
    (pointwise :
      ∀ site, rewrite.sourceAt source site ↔ rewrite.targetAt target site) :
    rewrite.siteFactorization.sourceBody source ↔
      rewrite.siteFactorization.targetBody target :=
  rewrite.siteFactorization.congruent source target pointwise

/-- Existentially closed logical source body. -/
def sourceInner
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) : Prop :=
  ∃ witness, rewrite.siteFactorization.sourceBody witness

/-- Existentially closed logical target body. -/
def targetInner
    (rewrite :
      LogicalUniformRewrite siteCount SourceWitness TargetWitness) : Prop :=
  ∃ witness, rewrite.siteFactorization.targetBody witness

end LogicalUniformRewrite

end WirePrimitive

end VisualProof
