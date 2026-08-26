import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Scope.Rename
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Argument

namespace Duplicate

def Vars.duplicateAt (before : List Sig) :
    Vars context (before ++ signature :: after) →
      Vars context (before ++ signature :: signature :: after)
  := match before with
  | [] => fun
    | .cons selected rest => .cons selected (.cons selected rest)
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.duplicateAt restBefore tail)

@[simp] theorem Vars.duplicateAt_extend
    (beforeValues : Vars context before)
    (selected : Var context signature)
    (afterValues : Vars context after) :
    Vars.duplicateAt before
        (Vars.extend beforeValues (.cons selected afterValues)) =
      Vars.extend beforeValues (.cons selected (.cons selected afterValues)) := by
  induction beforeValues with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.extend, Vars.duplicateAt]
      exact congrArg (Vars.cons head) induction

@[simp] theorem Vars.duplicateAt_map (before : List Sig)
    (variables : Vars source (before ++ signature :: after))
    (rename : WireRenaming source target) :
    Vars.duplicateAt before (variables.map fun wire => rename wire) =
      (Vars.duplicateAt before variables).map fun wire => rename wire := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        exact congrArg (Vars.cons (rename first)) (induction rest)

theorem Vars.countIndex_le_duplicateAt (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (wireIndex : Nat) :
    variables.countIndex wireIndex ≤
      (Vars.duplicateAt before variables).countIndex wireIndex := by
  induction before with
  | nil =>
      cases variables with
      | cons head tail =>
          simp only [Vars.duplicateAt, Vars.countIndex]
          exact Nat.le_add_left _ _
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          simp only [Vars.duplicateAt, Vars.countIndex]
          exact Nat.add_le_add_left (induction rest) _

def Values.duplicateAt (before : List Sig) :
    Values model (before ++ signature :: after) →
      Values model (before ++ signature :: signature :: after)
  := match before with
  | [] => fun values => (values.1, values.1, values.2)
  | _ :: restBefore => fun values =>
      (values.1, Values.duplicateAt restBefore values.2)

def Values.contractAt (before : List Sig) :
    Values model (before ++ signature :: signature :: after) →
      Values model (before ++ signature :: after)
  := match before with
  | [] => fun values => (values.1, values.2.2)
  | _ :: restBefore => fun values =>
      (values.1, Values.contractAt restBefore values.2)

theorem Values.contract_duplicate (before : List Sig)
    (values : Values model (before ++ signature :: after)) :
    Values.contractAt before (Values.duplicateAt before values) = values := by
  induction before with
  | nil => cases values; rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [Values.duplicateAt, Values.contractAt]
        rw [induction rest]

theorem evaluate_duplicate (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (env : Values model context) :
    evaluateVars (Vars.duplicateAt before variables) env =
      Values.duplicateAt before (evaluateVars variables env) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.duplicateAt, evaluateVars, Values.duplicateAt]
        rw [induction rest]

def operation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (before ++ signature :: signature :: after))
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (Vars.duplicateAt before
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def rootFrame (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :=
  Transform.Frame.replace outer localBefore localAfter
    [.rel (before ++ signature :: signature :: after)]
    (before ++ signature :: after)

def targetHead (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :
    Var (outer ++ (localBefore ++
      .rel (before ++ signature :: signature :: after) :: localAfter))
      (.rel (before ++ signature :: signature :: after)) :=
  Transform.Frame.insertedHead outer localBefore localAfter _

structure Duplicates.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after signature) items

def Duplicates.Description.source
    (description : Duplicates.Description outer) : Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def Duplicates.Description.target
    (description : Duplicates.Description outer) : Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.signature ::
      description.signature :: description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive Duplicates : Region outer → Region outer → Prop
  | mk (description : Duplicates.Description outer) :
      Duplicates description.source description.target

@[simp] theorem duplicateItemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires
      (.rel (before ++ signature :: signature :: after))}
    {source : Item sourceWires}
    (edit : Transform.ItemEdit (operation before after signature) frame
      targetHead source) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => rfl
  | .identity _ _ _ => rfl
  | .term _ _ _ _ => rfl
  | .cut _ => rfl

theorem selectedAtom_source_target_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires
      (.rel (before ++ signature :: signature :: after))}
    (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
      (frame.sourceKeep wire).index.val =
        (frame.targetKeep wire).index.val)
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Vars common (before ++ signature :: after))
    (siteData : PUnit) :
    Transform.ScopeTransfer .sourceToTarget
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((operation before after signature).site frame targetHead ports
        siteData) := by
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
  have duplicateLe := Vars.countIndex_le_duplicateAt before
    (ports.map fun selected => frame.targetKeep selected) wireIndex
  have mappedEq := Vars.countIndex_map_eq_of_index_eq ports
    (fun selected => frame.sourceKeep selected)
    (fun selected => frame.targetKeep selected)
    (fun selected => keepIndex selected) wireIndex
  rw [mappedEq, selectedIndex]
  exact Nat.add_le_add_left duplicateLe _

theorem selectedPin_source_target_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires
      (.rel (before ++ signature :: signature :: after))}
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Fin 1 → Var sourceWires
      (.rel (before ++ signature :: after)))
    (selected : ports 0 = frame.selected) :
    Transform.ScopeTransfer .sourceToTarget
      (Region.singleton (.identity
        (.rel (before ++ signature :: after)) 1 ports))
      ((operation before after signature).pin frame targetHead) := by
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

theorem Duplicates.Description.source_target_extension
    (description : Duplicates.Description outer)
    (sourceCanonical : description.source.Canonical) :
    description.target.Canonical ∧
      ∀ {wireSignature} (wire : Var outer wireSignature),
        (description.source.incidencePaths wire.index.val).Sublist
          (description.target.incidencePaths wire.index.val) := by
  let sourceLocals := description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter
  let targetLocals := description.localBefore ++
    .rel (description.before ++ description.signature ::
      description.signature :: description.after) :: description.localAfter
  have sourceAdjoinedCanonical :
      (Region.adjoinAt sourceLocals .nil
        (Region.ofItems description.items)).Canonical := by
    exact (RegionIso.adjoinAtOfItems sourceLocals
      description.items).canonical_iff.mpr (by
        simpa only [sourceLocals, Duplicates.Description.source] using
          sourceCanonical)
  have materialCanonical : (Region.ofItems description.items).Canonical :=
    Region.Canonical.material_of_adjoinAt sourceLocals .nil
      (Region.ofItems description.items) sourceAdjoinedCanonical
  have rootInvariant : Transform.IndexedHeadInvariant
      (rootFrame outer description.localBefore description.localAfter
        description.before description.after description.signature)
      (targetHead outer description.localBefore description.localAfter
        description.before description.after description.signature) := by
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
      selectedAtom_source_target_extension selectedInvariant.2.1
        selectedInvariant.2.2 ports siteData)
    (fun selectedInvariant ports selected =>
      selectedPin_source_target_extension selectedInvariant.2.2 ports selected)
    duplicateItemEdit_run_items_length rootInvariant description.itemsEdit
    materialCanonical
  have targetCanonical : description.target.Canonical := by
    apply Region.Canonical.adjoinAt_of_material_roots targetLocals .nil
      description.itemsEdit.run True.intro child.1
    intro targetIndex
    let sourceIndex : Fin sourceLocals.length :=
      ⟨targetIndex.val, by
        simpa [sourceLocals, targetLocals] using targetIndex.isLt⟩
    have sourceRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
        (Region.ofItems description.items) sourceAdjoinedCanonical sourceIndex
    have paths := child.2 (outer.length + sourceIndex.val) (by
      simpa [sourceLocals] using
        Nat.add_lt_add_left sourceIndex.isLt outer.length)
    exact RegionPath.RootedTwo.of_sublist paths (by
      simpa [sourceIndex] using sourceRoot)
  refine ⟨by simpa only [targetLocals, Duplicates.Description.target] using
    targetCanonical, ?_⟩
  intro wireSignature wire
  have sourcePaths := Region.incidencePaths_ofItems description.items
    (wire.appendLeft sourceLocals)
  have targetPaths := Region.incidencePaths_adjoinAt_nil
    description.itemsEdit.run (wire.appendLeft targetLocals)
  have targetPaths' :
      description.target.incidencePaths wire.index.val =
        description.itemsEdit.run.incidencePaths wire.index.val := by
    simpa [targetLocals, Duplicates.Description.target] using targetPaths
  simp [sourceLocals] at sourcePaths
  simp only [Duplicates.Description.source, Duplicates.Description.target]
  rw [show (Region.adjoinAt
      (description.localBefore ++
        .rel (description.before ++ description.signature ::
          description.signature :: description.after) ::
            description.localAfter) .nil
      description.itemsEdit.run).incidencePaths wire.index.val =
        description.itemsEdit.run.incidencePaths wire.index.val from
          targetPaths']
  change (description.items.incidencePaths wire.index.val 0).Sublist
    (description.itemsEdit.run.incidencePaths wire.index.val)
  rw [← sourcePaths]
  exact child.2 wire.index.val (by
    simp only [List.length_append]
    exact Nat.lt_add_right _ wire.index.isLt)

inductive Local : LocalRule
  | duplicate (step : Duplicates before after) : Local before after

end Duplicate

namespace Projection

def Vars.dropAt (before : List Sig) :
    Vars context (before ++ signature :: after) → Vars context (before ++ after)
  := match before with
  | [] => fun
    | .cons _ rest => rest
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.dropAt restBefore tail)

theorem Vars.dropAt_extend_singleton
    (variables : Vars context before) (inserted : Var context signature) :
    HEq (Vars.dropAt before
      (Theory.Vars.extend variables (.cons inserted .nil))) variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Theory.Vars.extend, Vars.dropAt]
      congr
      exact List.append_nil _

@[simp] theorem Vars.dropAt_map (before : List Sig)
    (variables : Vars source (before ++ signature :: after))
    (rename : WireRenaming source target) :
    Vars.dropAt before (variables.map fun wire => rename wire) =
      (Vars.dropAt before variables).map fun wire => rename wire := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        exact congrArg (Vars.cons (rename first)) (induction rest)

theorem Vars.countIndex_dropAt_le (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (wireIndex : Nat) :
    (Vars.dropAt before variables).countIndex wireIndex ≤
      variables.countIndex wireIndex := by
  induction before with
  | nil =>
      cases variables with
      | cons head tail =>
          simp only [Vars.dropAt, Vars.countIndex]
          exact Nat.le_add_left _ _
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          simp only [Vars.dropAt, Vars.countIndex]
          exact Nat.add_le_add_left (induction rest) _

def Vars.insertAt (before : List Sig) (inserted : Var context signature) :
    Vars context (before ++ after) →
      Vars context (before ++ signature :: after)
  := match before with
  | [] => fun rest => .cons inserted rest
  | _ :: restBefore => fun
    | .cons head tail => .cons head (Vars.insertAt restBefore inserted tail)

@[simp] theorem Vars.insertAt_map (before : List Sig)
    (inserted : Var source signature)
    (variables : Vars source (before ++ after))
    (rename : WireRenaming source target) :
    (Vars.insertAt before inserted variables).map (fun wire => rename wire) =
      Vars.insertAt before (rename inserted)
        (variables.map fun wire => rename wire) := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        exact congrArg (Vars.cons (rename first)) (induction rest)

def Values.dropAt (before : List Sig) :
    Values model (before ++ signature :: after) →
      Values model (before ++ after)
  := match before with
  | [] => fun values => values.2
  | _ :: restBefore => fun values =>
      (values.1, Values.dropAt restBefore values.2)

def Values.insertAt (before : List Sig) (inserted : denoteSig model signature) :
    Values model (before ++ after) →
      Values model (before ++ signature :: after)
  := match before with
  | [] => fun rest => (inserted, rest)
  | _ :: restBefore => fun rest =>
      (rest.1, Values.insertAt restBefore inserted rest.2)

theorem Values.drop_insert (before : List Sig)
    (inserted : denoteSig model signature)
    (values : Values model (before ++ after)) :
    Values.dropAt before (Values.insertAt before inserted values) = values := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [Values.insertAt, Values.dropAt]
        rw [induction rest]

theorem evaluate_drop (before : List Sig)
    (variables : Vars context (before ++ signature :: after))
    (env : Values model context) :
    evaluateVars (Vars.dropAt before variables) env =
      Values.dropAt before (evaluateVars variables env) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.dropAt, evaluateVars, Values.dropAt]
        rw [induction rest]

theorem evaluate_insert (before : List Sig)
    (inserted : Var context signature)
    (variables : Vars context (before ++ after))
    (env : Values model context) :
    evaluateVars (Vars.insertAt before inserted variables) env =
      Values.insertAt before (env.lookup inserted)
        (evaluateVars variables env) := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
        simp only [Vars.insertAt, evaluateVars, Values.insertAt]
        rw [induction rest]

def operation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel (before ++ after))
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (Vars.dropAt before
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def uniformOperation (before after : List Sig) (signature : Sig) :
    Transform.Operation (before ++ signature :: after) where
  Data := fun {common _ targetWires} _ =>
    Var targetWires (.rel (before ++ after)) × Option (Var common signature)
  appendData := fun _ data locals =>
    (data.1.appendLeft locals, data.2.map fun wire => wire.appendLeft locals)
  SiteData := fun {common _sourceWires _targetWires} _frame data ports =>
    Σ attachment : Var common signature,
      { retained : Vars common (before ++ after) //
        data.2 = some attachment ∧
          ports = Vars.insertAt before attachment retained }
  site := fun frame data _ siteData =>
    Region.singleton (.atom data.1
      (siteData.2.val.map fun wire => frame.targetKeep wire))
  pin := fun _ data => Transform.unaryPin data.1

def rootFrame (outer localBefore localAfter before after : List Sig)
    (signature : Sig) :=
  Transform.Frame.replace outer localBefore localAfter
    [.rel (before ++ after)] (before ++ signature :: after)

def targetHead (outer localBefore localAfter before after : List Sig) :
    Var (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
      (.rel (before ++ after)) :=
  Transform.Frame.insertedHead outer localBefore localAfter _

structure Drops.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after) items

def Drops.Description.source (description : Drops.Description outer) :
    Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def Drops.Description.target (description : Drops.Description outer) :
    Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive Drops : Region outer → Region outer → Prop
  | mk (description : Drops.Description outer) :
      Drops description.source description.target

@[simp] theorem projectionItemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ after))}
    {source : Item sourceWires}
    (edit : Transform.ItemEdit (operation before after signature) frame
      targetHead source) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => rfl
  | .identity _ _ _ => rfl
  | .term _ _ _ _ => rfl
  | .cut _ => rfl

theorem projectionSelectedAtom_target_source_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ after))}
    (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
      (frame.sourceKeep wire).index.val =
        (frame.targetKeep wire).index.val)
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Vars common (before ++ signature :: after))
    (siteData : PUnit) :
    Transform.ScopeTransfer .targetToSource
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((operation before after signature).site frame targetHead ports
        siteData) := by
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro wireIndex _wireBound
  simp only [operation, Transform.unaryPin, Region.singleton, Region.ofItems,
    Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
    Var.index_appendLeft]
  apply (List.replicate_sublist_replicate []).mpr
  have targetAppendEq := Vars.countIndex_map_eq_of_index_eq
    (Vars.dropAt before (ports.map fun selected => frame.targetKeep selected))
    (fun selected => selected.appendLeft []) (fun selected => selected)
    (fun selected => Var.index_appendLeft selected []) wireIndex
  have sourceAppendEq := Vars.countIndex_map_eq_of_index_eq
    (ports.map fun selected => frame.sourceKeep selected)
    (fun selected => selected.appendLeft []) (fun selected => selected)
    (fun selected => Var.index_appendLeft selected []) wireIndex
  rw [targetAppendEq, sourceAppendEq]
  simp only [vars_map_id]
  have dropLe := Vars.countIndex_dropAt_le before
    (ports.map fun selected => frame.targetKeep selected) wireIndex
  have mappedEq := Vars.countIndex_map_eq_of_index_eq ports
    (fun selected => frame.targetKeep selected)
    (fun selected => frame.sourceKeep selected)
    (fun selected => (keepIndex selected).symm) wireIndex
  rw [mappedEq] at dropLe
  rw [selectedIndex]
  simpa only [vars_map_id] using Nat.add_le_add_left dropLe _

theorem projectionSelectedPin_target_source_extension
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (before ++ signature :: after) common
      sourceWires targetWires}
    {targetHead : Var targetWires (.rel (before ++ after))}
    (selectedIndex : frame.selected.index.val = targetHead.index.val)
    (ports : Fin 1 → Var sourceWires
      (.rel (before ++ signature :: after)))
    (selected : ports 0 = frame.selected) :
    Transform.ScopeTransfer .targetToSource
      (Region.singleton (.identity
        (.rel (before ++ signature :: after)) 1 ports))
      ((operation before after signature).pin frame targetHead) := by
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

theorem Drops.Description.target_source_extension
    (description : Drops.Description outer)
    (targetCanonical : description.target.Canonical) :
    description.source.Canonical ∧
      ∀ {wireSignature} (wire : Var outer wireSignature),
        (description.target.incidencePaths wire.index.val).Sublist
          (description.source.incidencePaths wire.index.val) := by
  let sourceLocals := description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter
  let targetLocals := description.localBefore ++
    .rel (description.before ++ description.after) :: description.localAfter
  have materialCanonical : description.itemsEdit.run.Canonical :=
    Region.Canonical.material_of_adjoinAt targetLocals .nil
      description.itemsEdit.run (by
        simpa only [targetLocals, Drops.Description.target] using
          targetCanonical)
  have rootInvariant : Transform.IndexedHeadInvariant
      (rootFrame outer description.localBefore description.localAfter
        description.before description.after description.signature)
      (targetHead outer description.localBefore description.localAfter
        description.before description.after) := by
    refine ⟨by simp [rootFrame],
      fun wire => Transform.Frame.keep_index_eq_of_length_eq
        (by simp) wire, ?_⟩
    simp [rootFrame, targetHead, Transform.Frame.replace,
      Transform.Frame.insertedHead, Var.appendRight]
    exact rfl
  have child := Transform.ItemsEdit.scopeTransfer .targetToSource
    Transform.IndexedHeadInvariant
    (fun frame head locals hypothesis => hypothesis.append locals)
    rootInvariant.1 rootInvariant.2.1
    (fun selectedInvariant ports siteData =>
      projectionSelectedAtom_target_source_extension selectedInvariant.2.1
        selectedInvariant.2.2 ports siteData)
    (fun selectedInvariant ports selected =>
      projectionSelectedPin_target_source_extension selectedInvariant.2.2
        ports selected)
    projectionItemEdit_run_items_length rootInvariant description.itemsEdit
    materialCanonical
  have sourceAdjoinedCanonical :
      (Region.adjoinAt sourceLocals .nil
        (Region.ofItems description.items)).Canonical := by
    apply Region.Canonical.adjoinAt_of_material_roots sourceLocals .nil
      (Region.ofItems description.items) True.intro child.1
    intro localIndex
    let targetIndex : Fin targetLocals.length :=
      ⟨localIndex.val, by
        simpa [sourceLocals, targetLocals] using localIndex.isLt⟩
    have targetRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
        description.itemsEdit.run (by
          simpa only [targetLocals, Drops.Description.target] using
            targetCanonical) targetIndex
    have paths := child.2 (outer.length + localIndex.val) (by
      simpa [sourceLocals] using
        Nat.add_lt_add_left localIndex.isLt outer.length)
    exact RegionPath.RootedTwo.of_sublist paths (by
      simpa [targetIndex] using targetRoot)
  have sourceCanonical : description.source.Canonical := by
    let presentation := RegionIso.adjoinAtOfItems sourceLocals
      description.items
    have converted := presentation.canonical_iff.mp sourceAdjoinedCanonical
    simpa only [sourceLocals, Drops.Description.source] using converted
  refine ⟨sourceCanonical, ?_⟩
  intro wireSignature wire
  have targetPaths := Region.incidencePaths_adjoinAt_nil
    description.itemsEdit.run (wire.appendLeft targetLocals)
  have targetPaths' :
      (Region.adjoinAt
        (description.localBefore ++
          Sig.rel (description.before ++ description.after) ::
            description.localAfter) .nil description.itemsEdit.run).incidencePaths
          wire.index.val =
        description.itemsEdit.run.incidencePaths wire.index.val := by
    simpa [targetLocals] using targetPaths
  simp only [Drops.Description.target, Drops.Description.source]
  rw [targetPaths']
  change (description.itemsEdit.run.incidencePaths wire.index.val).Sublist
    (description.items.incidencePaths wire.index.val 0)
  have paths := child.2 wire.index.val (by
    simp only [List.length_append]
    exact Nat.lt_add_right _ wire.index.isLt)
  have sourcePaths := Region.incidencePaths_ofItems description.items
    (wire.appendLeft sourceLocals)
  simp [sourceLocals] at sourcePaths
  rw [sourcePaths] at paths
  exact paths

structure UniformDrops.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  signature : Sig
  attachment : Option
    (Var (outer ++ (localBefore ++ localAfter)) signature)
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (uniformOperation before after signature)
    (rootFrame outer localBefore localAfter before after signature)
    (targetHead outer localBefore localAfter before after, attachment) items

def UniformDrops.Description.source
    (description : UniformDrops.Description outer) : Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++ description.signature :: description.after) ::
      description.localAfter) description.items

def UniformDrops.Description.target
    (description : UniformDrops.Description outer) : Region outer :=
  Region.adjoinAt (description.localBefore ++
    .rel (description.before ++ description.after) :: description.localAfter)
    .nil description.itemsEdit.run

inductive UniformDrops : Region outer → Region outer → Prop
  | mk (description : UniformDrops.Description outer) :
      UniformDrops description.source description.target

inductive Local.Description (outer : List Sig) : Type
  | extend (description : Drops.Description outer)
  | uniformDrop (description : UniformDrops.Description outer)
  | uniformExtend (description : UniformDrops.Description outer)

def Local.Description.source : Local.Description outer → Region outer
  | .extend description => description.target
  | .uniformDrop description => description.source
  | .uniformExtend description => description.target

def Local.Description.target : Local.Description outer → Region outer
  | .extend description => description.source
  | .uniformDrop description => description.target
  | .uniformExtend description => description.source

inductive Local : LocalRule
  | mk (description : Local.Description outer) :
      Local description.source description.target

end Projection

end Argument

def ArgumentDuplicate : Rule :=
  Contextual fun before after => symmetric Argument.Duplicate.Local before after

theorem ArgumentDuplicate.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentDuplicate source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentDuplicate source' target' :=
  Contextual.iso sourceIso step targetIso

def ArgumentProjection : Rule :=
  Contextual Argument.Projection.Local

theorem ArgumentProjection.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentProjection source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentProjection source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
