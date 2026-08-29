import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace ArgumentPermutation

/-- A typed reordering of argument tuples, with syntax and value actions kept
in lockstep. The inverse data makes non-bijective maps unrepresentable. -/
structure Permutation (source target : List Sig) where
  mapVars : ∀ {context}, Vars context source → Vars context target
  unmapVars : ∀ {context}, Vars context target → Vars context source
  mapValues : ∀ (model : Model), Values model source → Values model target
  unmapValues : ∀ (model : Model), Values model target → Values model source
  map_unmap_vars : ∀ {context} (values : Vars context target),
    mapVars (unmapVars values) = values
  unmap_map_vars : ∀ {context} (values : Vars context source),
    unmapVars (mapVars values) = values
  map_unmap_values : ∀ (model : Model) (values : Values model target),
    mapValues model (unmapValues model values) = values
  unmap_map_values : ∀ (model : Model) (values : Values model source),
    unmapValues model (mapValues model values) = values
  evaluate_map : ∀ {context} (model : Model)
    (variables : Vars context source) (env : Values model context),
    evaluateVars (mapVars variables) env =
      mapValues model (evaluateVars variables env)
  evaluate_unmap : ∀ {context} (model : Model)
    (variables : Vars context target) (env : Values model context),
    evaluateVars (unmapVars variables) env =
      unmapValues model (evaluateVars variables env)

def Permutation.refl (arguments : List Sig) :
    Permutation arguments arguments where
  mapVars := fun variables => variables
  unmapVars := fun variables => variables
  mapValues := fun _ values => values
  unmapValues := fun _ values => values
  map_unmap_vars := fun _ => rfl
  unmap_map_vars := fun _ => rfl
  map_unmap_values := fun _ _ => rfl
  unmap_map_values := fun _ _ => rfl
  evaluate_map := fun _ _ _ => rfl
  evaluate_unmap := fun _ _ _ => rfl

def Permutation.trans (first : Permutation source middle)
    (second : Permutation middle target) : Permutation source target where
  mapVars := fun variables => second.mapVars (first.mapVars variables)
  unmapVars := fun variables => first.unmapVars (second.unmapVars variables)
  mapValues := fun model values =>
    second.mapValues model (first.mapValues model values)
  unmapValues := fun model values =>
    first.unmapValues model (second.unmapValues model values)
  map_unmap_vars := by
    intro context values
    rw [first.map_unmap_vars, second.map_unmap_vars]
  unmap_map_vars := by
    intro context values
    rw [second.unmap_map_vars, first.unmap_map_vars]
  map_unmap_values := by
    intro model values
    rw [first.map_unmap_values, second.map_unmap_values]
  unmap_map_values := by
    intro model values
    rw [second.unmap_map_values, first.unmap_map_values]
  evaluate_map := by
    intro context model variables env
    rw [second.evaluate_map, first.evaluate_map]
  evaluate_unmap := by
    intro context model variables env
    rw [first.evaluate_unmap, second.evaluate_unmap]

def Permutation.cons (signature : Sig)
    (permutation : Permutation source target) :
    Permutation (signature :: source) (signature :: target) where
  mapVars := fun
    | .cons head tail => .cons head (permutation.mapVars tail)
  unmapVars := fun
    | .cons head tail => .cons head (permutation.unmapVars tail)
  mapValues := fun _ values =>
    (values.1, permutation.mapValues _ values.2)
  unmapValues := fun _ values =>
    (values.1, permutation.unmapValues _ values.2)
  map_unmap_vars := by
    intro context values
    cases values with
    | cons head tail =>
        simp only
        rw [permutation.map_unmap_vars]
  unmap_map_vars := by
    intro context values
    cases values with
    | cons head tail =>
        simp only
        rw [permutation.unmap_map_vars]
  map_unmap_values := by
    intro model values
    cases values with
    | mk head tail =>
        simp only
        rw [permutation.map_unmap_values]
  unmap_map_values := by
    intro model values
    cases values with
    | mk head tail =>
        simp only
        rw [permutation.unmap_map_values]
  evaluate_map := by
    intro context model variables env
    cases variables with
    | cons head tail =>
        simp only [evaluateVars]
        rw [permutation.evaluate_map]
  evaluate_unmap := by
    intro context model variables env
    cases variables with
    | cons head tail =>
        simp only [evaluateVars]
        rw [permutation.evaluate_unmap]

def Permutation.swapHead (left right : Sig) (rest : List Sig) :
    Permutation (left :: right :: rest) (right :: left :: rest) where
  mapVars := fun
    | .cons first (.cons second tail) => .cons second (.cons first tail)
  unmapVars := fun
    | .cons second (.cons first tail) => .cons first (.cons second tail)
  mapValues := fun _ values => (values.2.1, values.1, values.2.2)
  unmapValues := fun _ values => (values.2.1, values.1, values.2.2)
  map_unmap_vars := by
    intro context values
    cases values with
    | cons first tail => cases tail; rfl

  unmap_map_vars := by
    intro context values
    cases values with
    | cons first tail => cases tail; rfl
  map_unmap_values := by intro model values; cases values; rfl
  unmap_map_values := by intro model values; cases values; rfl
  evaluate_map := by
    intro context model variables env
    cases variables with
    | cons first tail => cases tail; rfl
  evaluate_unmap := by
    intro context model variables env
    cases variables with
    | cons first tail => cases tail; rfl

def Permutation.moveHead (signature : Sig) :
    (before after : List Sig) →
      Permutation (signature :: before ++ after)
        (before ++ signature :: after)
  | [], after => .refl (signature :: after)
  | head :: tail, after =>
      (swapHead signature head (tail ++ after)).trans
        (.cons head (moveHead signature tail after))

@[simp] theorem Permutation.moveHead_cons_extend
    (selected : Var context signature)
    (beforeValues : Vars context before)
    (afterValues : Vars context after) :
    (moveHead signature before after).mapVars
        (.cons selected (Vars.extend beforeValues afterValues)) =
      Vars.extend beforeValues (.cons selected afterValues) := by
  induction beforeValues with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.extend, moveHead, Permutation.trans, swapHead,
        Permutation.cons]
      exact congrArg (Vars.cons head) induction

@[simp] theorem Permutation.moveHead_map (signature : Sig)
    (before after : List Sig)
    (variables : Vars source (signature :: before ++ after))
    (rename : WireRenaming source target) :
    (Permutation.moveHead signature before after).mapVars
        (variables.map fun wire => rename wire) =
      ((Permutation.moveHead signature before after).mapVars variables).map
        fun wire => rename wire := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        cases rest with
        | cons second remaining =>
          exact congrArg (Vars.cons (rename second))
            (induction (Vars.cons first remaining))

theorem Permutation.countIndex_moveHead (signature : Sig)
    (before after : List Sig)
    (variables : Vars context (signature :: before ++ after))
    (wireIndex : Nat) :
    ((Permutation.moveHead signature before after).mapVars variables).countIndex
        wireIndex = variables.countIndex wireIndex := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          cases rest with
          | cons second remaining =>
              simp only [Permutation.moveHead, Permutation.trans,
                Permutation.swapHead, Permutation.cons, Vars.countIndex]
              change
                (if second.index.val = wireIndex then 1 else 0) +
                    Vars.countIndex wireIndex
                      ((Permutation.moveHead signature tail after).mapVars
                        (.cons first remaining)) = _
              rw [induction (.cons first remaining)]
              simp only [Vars.countIndex]
              omega

def Permutation.symm (permutation : Permutation source target) :
    Permutation target source where
  mapVars := permutation.unmapVars
  unmapVars := permutation.mapVars
  mapValues := permutation.unmapValues
  unmapValues := permutation.mapValues
  map_unmap_vars := permutation.unmap_map_vars
  unmap_map_vars := permutation.map_unmap_vars
  map_unmap_values := permutation.unmap_map_values
  unmap_map_values := permutation.map_unmap_values
  evaluate_map := permutation.evaluate_unmap
  evaluate_unmap := permutation.evaluate_map

def operation (sourceArguments targetArguments : List Sig)
    (permutation : Permutation sourceArguments targetArguments) :
    Transform.Operation sourceArguments where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel targetArguments)
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (permutation.mapVars
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def rootFrame (outer before after sourceArguments targetArguments : List Sig) :=
  Transform.Frame.replace outer before after [.rel targetArguments]
    sourceArguments

def targetHead (outer before after targetArguments : List Sig) :
    Var (outer ++ (before ++ .rel targetArguments :: after))
      (.rel targetArguments) :=
  Transform.Frame.insertedHead outer before after (.rel targetArguments)

structure Permutes.Description (outer : List Sig) where
  sourceArguments : List Sig
  targetArguments : List Sig
  before : List Sig
  after : List Sig
  permutation : Permutation sourceArguments targetArguments
  items : ItemSeq (outer ++ (before ++ .rel sourceArguments :: after))
  itemsEdit : Transform.ItemsEdit
    (operation sourceArguments targetArguments permutation)
    (rootFrame outer before after sourceArguments targetArguments)
    (targetHead outer before after targetArguments) items

def Permutes.Description.source (description : Permutes.Description outer) :
    Region outer :=
  .mk (description.before ++
    .rel description.sourceArguments :: description.after) description.items

def Permutes.Description.target (description : Permutes.Description outer) :
    Region outer :=
  Region.adjoinAt
    (description.before ++ .rel description.targetArguments :: description.after)
    .nil description.itemsEdit.run

inductive Permutes : Region outer → Region outer → Prop
  | mk (description : Permutes.Description outer) :
      Permutes description.source description.target

@[simp] theorem moveHeadItemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (signature :: before ++ after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ signature :: after))}
    {source : Item sourceWires}
    (edit : Transform.ItemEdit
      (operation (signature :: before ++ after)
        (before ++ signature :: after)
        (Permutation.moveHead signature before after)) frame targetHead source) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => rfl
  | .identity _ _ _ => rfl
  | .term _ _ _ _ => rfl
  | .cut _ => rfl

theorem moveHeadSelectedAtom_source_target_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (signature :: before ++ after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ signature :: after))}
    (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
      (frame.sourceKeep wire).index.val =
        (frame.targetKeep wire).index.val)
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Vars common (signature :: before ++ after))
    (siteData : PUnit) :
    Transform.ScopeTransfer .sourceToTarget
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((operation (signature :: before ++ after)
        (before ++ signature :: after)
        (Permutation.moveHead signature before after)).site frame targetHead
          ports siteData) := by
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro wireIndex _wireBound
  simp only [operation, Transform.unaryPin, Region.singleton, Region.ofItems,
    Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
    Var.index_appendLeft]
  apply (List.replicate_sublist_replicate []).mpr
  simp only [Vars.countIndex_map_appendLeft_nil]
  have mappedEq := Vars.countIndex_map_eq_of_index_eq ports
    (fun selected => frame.sourceKeep selected)
    (fun selected => frame.targetKeep selected)
    (fun selected => keepIndex selected) wireIndex
  rw [Permutation.countIndex_moveHead, mappedEq, selectedIndex]
  exact Nat.le_refl _

theorem moveHeadSelectedPin_source_target_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (signature :: before ++ after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ signature :: after))}
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Fin 1 → Var sourceWires
      (.rel (signature :: before ++ after)))
    (selected : ports 0 = frame.selected) :
    Transform.ScopeTransfer .sourceToTarget
      (Region.singleton (.identity (.rel (signature :: before ++ after)) 1
        ports))
      ((operation (signature :: before ++ after)
        (before ++ signature :: after)
        (Permutation.moveHead signature before after)).pin frame targetHead) := by
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro wireIndex _wireBound
  simp only [operation, Transform.unaryPin, Region.singleton, Region.ofItems,
    Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
    Var.index_appendLeft, List.ofFn_succ, List.ofFn_zero, List.count_cons,
    List.count_nil]
  rw [selected, selectedIndex]
  exact List.Sublist.refl _

theorem moveHead_source_target_extension
    {outer localBefore localAfter before after : List Sig}
    {signature : Sig}
    {items : ItemSeq (outer ++ (localBefore ++
      .rel (signature :: before ++ after) :: localAfter))}
    (itemsEdit : Transform.ItemsEdit
      (operation (signature :: before ++ after)
        (before ++ signature :: after)
        (Permutation.moveHead signature before after))
      (rootFrame outer localBefore localAfter
        (signature :: before ++ after) (before ++ signature :: after))
      (targetHead outer localBefore localAfter
        (before ++ signature :: after)) items)
    (sourceCanonical : (.mk (localBefore ++
      .rel (signature :: before ++ after) :: localAfter) items :
        Region outer).Canonical) :
    (Region.adjoinAt (localBefore ++
      .rel (before ++ signature :: after) :: localAfter) .nil
      itemsEdit.run).Canonical ∧
      ∀ {wireSignature} (wire : Var outer wireSignature),
        ((.mk (localBefore ++
          .rel (signature :: before ++ after) :: localAfter) items :
            Region outer).incidencePaths wire.index.val).Sublist
          ((Region.adjoinAt (localBefore ++
            .rel (before ++ signature :: after) :: localAfter) .nil
            itemsEdit.run).incidencePaths wire.index.val) := by
  let sourceLocals := localBefore ++
    .rel (signature :: before ++ after) :: localAfter
  let targetLocals := localBefore ++
    .rel (before ++ signature :: after) :: localAfter
  have sourceAdjoinedCanonical :
      (Region.adjoinAt sourceLocals .nil (Region.ofItems items)).Canonical :=
    (RegionIso.adjoinAtOfItems sourceLocals items).canonical_iff.mpr (by
      simpa only [sourceLocals] using sourceCanonical)
  have materialCanonical : (Region.ofItems items).Canonical :=
    Region.Canonical.material_of_adjoinAt sourceLocals .nil
      (Region.ofItems items) sourceAdjoinedCanonical
  have rootInvariant : Transform.IndexedHeadInvariant
      (rootFrame outer localBefore localAfter
        (signature :: before ++ after) (before ++ signature :: after))
      (targetHead outer localBefore localAfter
        (before ++ signature :: after)) := by
    refine ⟨by simp [rootFrame],
      fun wire => Transform.Frame.keep_index_eq_of_length_eq
        (by simp) wire, ?_⟩
    simp [rootFrame, targetHead, Transform.Frame.replace,
      Transform.Frame.insertedHead, Var.appendRight]
    exact rfl
  have child := Transform.ItemsEdit.scopeTransfer .sourceToTarget
    Transform.IndexedHeadInvariant
    (fun frame head locals hypothesis => hypothesis.append locals)
    rootInvariant.1 rootInvariant.2.1
    (fun selectedInvariant ports siteData =>
      moveHeadSelectedAtom_source_target_extension selectedInvariant.2.1
        selectedInvariant.2.2 ports siteData)
    (fun selectedInvariant ports selected =>
      moveHeadSelectedPin_source_target_extension selectedInvariant.2.2
        ports selected)
    moveHeadItemEdit_run_items_length rootInvariant itemsEdit
    materialCanonical
  have targetCanonical :
      (Region.adjoinAt targetLocals .nil itemsEdit.run).Canonical := by
    apply Region.Canonical.adjoinAt_of_material_roots targetLocals .nil
      itemsEdit.run True.intro child.1
    intro targetIndex
    let sourceIndex : Fin sourceLocals.length :=
      ⟨targetIndex.val, by
        simpa [sourceLocals, targetLocals] using targetIndex.isLt⟩
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
        (Region.ofItems items) sourceAdjoinedCanonical sourceIndex
    have paths := child.2 (outer.length + sourceIndex.val) (by
      simpa [sourceLocals] using
        Nat.add_lt_add_left sourceIndex.isLt outer.length)
    exact RegionPath.RootedTwo.of_sublist paths (by
      simpa [sourceIndex] using sourceRoot)
  refine ⟨by simpa only [targetLocals] using targetCanonical, ?_⟩
  intro wireSignature wire
  have sourcePaths := Region.incidencePaths_ofItems items
    (wire.appendLeft sourceLocals)
  have targetPaths := Region.incidencePaths_adjoinAt_nil itemsEdit.run
    (wire.appendLeft targetLocals)
  have targetPaths' :
      (Region.adjoinAt
        (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
        .nil itemsEdit.run).incidencePaths wire.index.val =
          itemsEdit.run.incidencePaths wire.index.val := by
    simpa [targetLocals] using targetPaths
  simp [sourceLocals] at sourcePaths
  rw [targetPaths']
  change (items.incidencePaths wire.index.val 0).Sublist
    (itemsEdit.run.incidencePaths wire.index.val)
  have paths := child.2 wire.index.val (by
    simp only [List.length_append]
    exact Nat.lt_add_right _ wire.index.isLt)
  exact sourcePaths ▸ paths

inductive Local : LocalRule
  | permute (step : Permutes before after) : Local before after

end ArgumentPermutation

def ArgumentPermutation : Rule :=
  Contextual fun before after =>
    symmetric ArgumentPermutation.Local before after

theorem ArgumentPermutation.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentPermutation source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentPermutation source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
