import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Argument

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace Leaf

namespace Formal

def operation (before after : List Sig) :
    Transform.Operation (before ++ .rel (before ++ after) :: after) where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun {common _sourceWires _targetWires} _frame _data ports =>
    Σ formal : Var common (.rel (before ++ after)),
      { retained : Vars common (before ++ after) //
        ports = Argument.Projection.Vars.insertAt before formal retained }
  site := fun frame _ _ siteData =>
    Region.singleton
      (.atom (frame.targetKeep siteData.1)
        (siteData.2.val.map fun wire => frame.targetKeep wire))
  pin := fun _ _ => Region.blank _

def rootFrame (outer localBefore localAfter before after : List Sig) :=
  Transform.Frame.replace outer localBefore localAfter []
    (before ++ .rel (before ++ after) :: after)

structure Applies.Description (outer : List Sig) where
  before : List Sig
  after : List Sig
  localBefore : List Sig
  localAfter : List Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ .rel (before ++ after) :: after) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation before after)
    (rootFrame outer localBefore localAfter before after) PUnit.unit items

def Applies.Description.source (description : Applies.Description outer) :
    Region outer :=
  .mk (description.localBefore ++
    .rel (description.before ++
      .rel (description.before ++ description.after) :: description.after) ::
      description.localAfter) description.items

def Applies.Description.target (description : Applies.Description outer) :
    Region outer :=
  Region.adjoinAt (description.localBefore ++ description.localAfter) .nil
    description.itemsEdit.run

inductive Applies : Region outer → Region outer → Prop
  | mk (description : Applies.Description outer) :
      Applies description.source description.target

@[simp] theorem formalItemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (.rel arguments :: arguments) common
      sourceWires targetWires} {source : Item sourceWires}
    (edit : Transform.ItemEdit (operation [] arguments) frame PUnit.unit source)
    (noPin : edit.NoSelectedPin) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => False.elim noPin
  | .identity _ _ _ => rfl
  | .cut _ => rfl

theorem formalSelectedAtom_retainedTargetToSource
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (.rel arguments :: arguments) common
      sourceWires targetWires}
    (invariant : Transform.RetainedIndexInvariant frame)
    (ports : Vars common (.rel arguments :: arguments))
    (siteData : (operation [] arguments).SiteData frame PUnit.unit ports) :
    Transform.RetainedScopeTransfer frame
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((operation [] arguments).site frame PUnit.unit ports siteData) := by
  rcases siteData with ⟨formal, retained, portsEq⟩
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro signature wire
  have selectedNe := invariant.selectedFresh wire
  subst ports
  have retainedPorts := Transform.Vars.countIndex_map_eq_of_reflection retained
    frame.sourceKeep frame.targetKeep invariant.reflects wire
  have targetAppend := Vars.countIndex_map_eq_of_index_eq retained
    (fun selected => (frame.targetKeep selected).appendLeft [])
    (fun selected => frame.targetKeep selected)
    (fun selected => Var.index_appendLeft _ _) (frame.targetKeep wire).index.val
  have sourceAppend := Vars.countIndex_map_eq_of_index_eq retained
    (fun selected => (frame.sourceKeep selected).appendLeft [])
    (fun selected => frame.sourceKeep selected)
    (fun selected => Var.index_appendLeft _ _) (frame.sourceKeep wire).index.val
  simp only [operation, Argument.Projection.Vars.insertAt,
    Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, Var.index_appendLeft, Vars.map,
    Vars.countIndex]
  have formalIff := invariant.reflects formal wire
  by_cases formalSourceEq : (frame.sourceKeep formal).index.val =
      (frame.sourceKeep wire).index.val
  · have formalTargetEq := formalIff.mp formalSourceEq
    simp only [if_pos formalTargetEq, if_pos formalSourceEq,
      if_neg selectedNe, Vars.map_map]
    rw [targetAppend, ← retainedPorts, ← sourceAppend]
    simp
  · have formalTargetNe := not_congr formalIff |>.mp formalSourceEq
    simp only [if_neg formalTargetNe, if_neg formalSourceEq,
      if_neg selectedNe, Vars.map_map]
    rw [targetAppend, ← retainedPorts, ← sourceAppend]
    simp

/-- Formal application owns validity of its raw positional source.  The
prepared direct-atom target supplies every retained-wire obligation; the sole
additional premise is rootedness of the source-only relation binder. -/
theorem target_source_validity
    {outer localBefore localAfter arguments : List Sig}
    {items : ItemSeq (outer ++ (localBefore ++
      .rel (.rel arguments :: arguments) :: localAfter))}
    (edit : Transform.ItemsEdit (operation [] arguments)
      (rootFrame outer localBefore localAfter [] arguments) PUnit.unit items)
    (noPin : edit.NoSelectedPin)
    (targetCanonical :
      (Region.adjoinAt (localBefore ++ localAfter) .nil edit.run).Canonical)
    (selectedRooted : RegionPath.RootedTwo
      (items.incidencePaths (outer.length + localBefore.length) 0)) :
    ((.mk (localBefore ++ .rel (.rel arguments :: arguments) :: localAfter)
        items : Region outer).Canonical) ∧
      ∀ {signature} (wire : Var outer signature),
        (Region.adjoinAt (localBefore ++ localAfter) .nil edit.run).incidencePaths
            wire.index.val =
          (.mk (localBefore ++ .rel (.rel arguments :: arguments) :: localAfter)
            items : Region outer).incidencePaths wire.index.val := by
  let sourceLocals := localBefore ++
    .rel (.rel arguments :: arguments) :: localAfter
  let targetLocals := localBefore ++ localAfter
  let frame := rootFrame outer localBefore localAfter [] arguments
  have rootInvariant : Transform.RetainedIndexInvariant frame := by
    constructor
    · intro leftSignature rightSignature left right
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := localBefore)
          (inserted := [.rel (.rel arguments :: arguments)])
          (after := localAfter) left right).trans
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := localBefore) (inserted := [])
          (after := localAfter) left right).symm
    · intro signature wire
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.insertedHead_ne_keep
          (outer := outer) (before := localBefore) (after := localAfter)
          (selectedSignature := .rel (.rel arguments :: arguments))
          (inserted := []) wire)
  have materialCanonical : edit.run.Canonical :=
    Region.Canonical.material_of_adjoinAt targetLocals .nil edit.run
      targetCanonical
  have child := Transform.ItemsEdit.retainedTargetToSource
    (fun invariantFrame (_ : (operation [] arguments).Data invariantFrame) =>
      Transform.RetainedIndexInvariant invariantFrame)
    (fun invariantFrame _ locals hypothesis => hypothesis.append locals)
    (fun hypothesis => hypothesis)
    (fun hypothesis ports siteData =>
      formalSelectedAtom_retainedTargetToSource hypothesis ports siteData)
    formalItemEdit_run_items_length rootInvariant edit noPin materialCanonical
  have sourceCanonical : (.mk sourceLocals items : Region outer).Canonical := by
    refine ⟨?_, (ItemSeq.ChildrenCanonical.renameWires_iff items _).mp
      child.1.2⟩
    intro localIndex
    have localBound : localIndex.val <
        localBefore.length + 1 + localAfter.length := by
      simpa [sourceLocals, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using localIndex.isLt
    by_cases beforeCase : localIndex.val < localBefore.length
    · let beforeIndex : Fin localBefore.length :=
        ⟨localIndex.val, beforeCase⟩
      let targetIndex : Fin targetLocals.length :=
        ⟨beforeIndex.val, by
          simp only [targetLocals, List.length_append]
          omega⟩
      let targetWire := Var.appendRight outer
        ((Var.ofIndex beforeIndex).appendLeft localAfter)
      have targetRoot :=
        Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil edit.run
          targetCanonical targetIndex
      have paths := child.2 targetWire
      rw [Region.incidencePaths_ofItems] at paths
      have targetKeepIndex :
          (frame.targetKeep targetWire).index.val =
            outer.length + targetIndex.val := by
        simp [targetWire, targetIndex, targetLocals, frame, rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendMap, Var.appendRight,
          Var.index]
      have sourceKeepIndex :
          (frame.sourceKeep targetWire).index.val =
            outer.length + localIndex.val := by
        simp [targetWire, beforeIndex, frame, rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendMap, Var.appendRight,
          Var.index]
      rw [targetKeepIndex, sourceKeepIndex] at paths
      exact (congrArg RegionPath.RootedTwo paths).mp targetRoot
    · by_cases selectedCase : localIndex.val = localBefore.length
      · simpa only [selectedCase] using selectedRooted
      · let afterIndex : Fin localAfter.length :=
          ⟨localIndex.val - localBefore.length - 1, by omega⟩
        let targetIndex : Fin targetLocals.length :=
          ⟨localBefore.length + afterIndex.val, by
            simp only [targetLocals, List.length_append]
            omega⟩
        let targetWire := Var.appendRight outer
          (Var.appendRight localBefore (Var.ofIndex afterIndex))
        have targetRoot :=
          Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil edit.run
            targetCanonical targetIndex
        have paths := child.2 targetWire
        rw [Region.incidencePaths_ofItems] at paths
        have targetKeepIndex :
            (frame.targetKeep targetWire).index.val =
              outer.length + targetIndex.val := by
          simp [targetWire, targetIndex, targetLocals, frame, rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendMap, Var.appendRight,
            Var.index]
        have sourceKeepIndex :
            (frame.sourceKeep targetWire).index.val =
              outer.length + localIndex.val := by
          simp [targetWire, afterIndex, frame, rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendMap, Var.appendRight,
            Var.index]
          omega
        rw [targetKeepIndex, sourceKeepIndex] at paths
        exact (congrArg RegionPath.RootedTwo paths).mp targetRoot
  refine ⟨sourceCanonical, ?_⟩
  intro signature wire
  have targetPaths := Region.incidencePaths_adjoinAt_nil edit.run
    (wire.appendLeft targetLocals)
  have paths := child.2 (wire.appendLeft targetLocals)
  rw [Region.incidencePaths_ofItems] at paths
  have paths' : edit.run.incidencePaths
      (wire.appendLeft targetLocals).index.val =
      items.incidencePaths wire.index.val 0 := by
    simpa [frame, rootFrame, Transform.Frame.replace, Transform.Frame.keep,
      Transform.Frame.localKeep, Var.appendMap_left, targetLocals,
      Var.index_appendLeft] using paths
  simpa [sourceLocals, targetLocals] using targetPaths.trans paths'

inductive Local : LocalRule
  | abstractFormal (step : Applies applied formal) : Local formal applied

end Formal

namespace Identity

def wire (signature : Sig) : {arity : Nat} →
    Fin arity → Var (List.replicate arity signature) signature
  | 0, position => Fin.elim0 position
  | _ + 1, position =>
      Fin.cases .here (fun rest => .there (wire signature rest)) position

def Vars.fromFn (ports : Fin arity → Var context signature) :
    Vars context (List.replicate arity signature) :=
  match arity with
  | 0 => .nil
  | _ + 1 => .cons (ports 0)
      (Vars.fromFn fun position => ports position.succ)

/-- Recover the positional function represented by a homogeneous variable
vector. -/
def Vars.toFn : {arity : Nat} →
    Vars context (List.replicate arity signature) →
      Fin arity → Var context signature
  | 0, .nil => Fin.elim0
  | _ + 1, .cons head tail =>
      Fin.cases head (Vars.toFn tail)

@[simp] theorem Vars.fromFn_toFn
    (ports : Vars context (List.replicate arity signature)) :
    Vars.fromFn (Vars.toFn ports) = ports := by
  induction arity with
  | zero =>
      cases ports
      rfl
  | succ arity induction =>
      cases ports with
      | cons head tail =>
          simp only [Vars.toFn, Vars.fromFn]
          exact congrArg (Vars.cons head) (induction tail)

@[simp] theorem Vars.toFn_fromFn
    (ports : Fin arity → Var context signature) :
    Vars.toFn (Vars.fromFn ports) = ports := by
  funext position
  induction arity with
  | zero => exact Fin.elim0 position
  | succ arity induction =>
      exact Fin.cases rfl (fun rest => induction
        (ports := fun index => ports index.succ) rest) position

@[simp] theorem Vars.fromFn_map
    (ports : Fin arity → Var source signature)
    (rename : WireRenaming source target) :
    (Vars.fromFn ports).map (fun wire => rename wire) =
      Vars.fromFn (fun position => rename (ports position)) := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      simp only [Vars.fromFn, Vars.map]
      exact congrArg (Vars.cons (rename (ports 0)))
        (induction (ports := fun position => ports position.succ))

@[simp] theorem Vars.toFn_map
    (ports : Vars source (List.replicate arity signature))
    (rename : WireRenaming source target) :
    Vars.toFn (ports.map fun wire => rename wire) =
      fun position => rename (Vars.toFn ports position) := by
  have mapped : ports.map (fun wire => rename wire) =
      Vars.fromFn (fun position => rename (Vars.toFn ports position)) := by
    rw [← Vars.fromFn_map, Vars.fromFn_toFn]
  rw [mapped, Vars.toFn_fromFn]

theorem Values.lookup_evaluate_fromFn
    (ports : Fin arity → Var context signature)
    (env : Values model context) (position : Fin arity) :
    (evaluateVars (Vars.fromFn ports) env).lookup (wire signature position) =
      env.lookup (ports position) := by
  induction arity with
  | zero => exact Fin.elim0 position
  | succ arity induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      exact induction (ports := fun index => ports index.succ) rest

def operation (signature : Sig) (arity : Nat) :
    Transform.Operation (List.replicate arity signature) where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun {common _sourceWires _targetWires} _frame _data ports =>
    { identityPorts : Fin arity → Var common signature //
      ports = Vars.fromFn identityPorts }
  site := fun frame _ _ siteData =>
    Region.singleton (.identity signature arity
      (fun position => frame.targetKeep (siteData.val position)))
  pin := fun _ _ => Region.blank _

def rootFrame (outer localBefore localAfter : List Sig)
    (signature : Sig) (arity : Nat) :=
  Transform.Frame.replace outer localBefore localAfter []
    (List.replicate arity signature)

@[simp] theorem identityItemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (List.replicate arity signature) common
      sourceWires targetWires} {source : Item sourceWires}
    (edit : Transform.ItemEdit (operation signature arity) frame PUnit.unit
      source)
    (noPin : edit.NoSelectedPin) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => False.elim noPin
  | .identity _ _ _ => rfl
  | .cut _ => rfl

theorem Vars.countIndex_fromFn
    (ports : Fin arity → Var wires signature) (index : Nat) :
    (Vars.fromFn ports).countIndex index =
      (List.ofFn fun position : Fin arity =>
        (ports position).index.val).count index := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      rw [List.ofFn_succ]
      simp only [Vars.fromFn, Theory.Vars.countIndex, List.count_cons]
      rw [induction (fun position => ports position.succ)]
      by_cases equal : (ports 0).index.val = index
      · simp only [equal, if_pos, beq_self_eq_true]
        omega
      · simp [equal]

theorem identitySelectedAtom_retainedTargetToSource
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (List.replicate arity signature) common
      sourceWires targetWires}
    (invariant : Transform.RetainedIndexInvariant frame)
    (ports : Vars common (List.replicate arity signature))
    (siteData : (operation signature arity).SiteData frame PUnit.unit ports) :
    Transform.RetainedScopeTransfer frame
      (Region.singleton (.atom frame.selected
        (ports.map fun wire => frame.sourceKeep wire)))
      ((operation signature arity).site frame PUnit.unit ports siteData) := by
  rcases siteData with ⟨identityPorts, portsEq⟩
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro wireSignature wire
  have selectedNe := invariant.selectedFresh wire
  subst ports
  have retainedPorts := Transform.Vars.countIndex_map_eq_of_reflection
    (Vars.fromFn identityPorts) frame.sourceKeep frame.targetKeep
    invariant.reflects wire
  have targetCount :
      (List.ofFn fun position : Fin arity =>
        (frame.targetKeep (identityPorts position)).index.val).count
          (frame.targetKeep wire).index.val =
        ((Vars.fromFn identityPorts).map fun selected =>
          frame.targetKeep selected).countIndex
            (frame.targetKeep wire).index.val := by
    calc
      _ = (Vars.fromFn (fun position =>
          frame.targetKeep (identityPorts position))).countIndex
            (frame.targetKeep wire).index.val :=
        (Vars.countIndex_fromFn _ _).symm
      _ = _ := by rw [← Vars.fromFn_map]
  have sourceAppend :
      (((Vars.fromFn identityPorts).map fun selected =>
        frame.sourceKeep selected).map fun selected =>
          selected.appendLeft []).countIndex
            (frame.sourceKeep wire).index.val =
        ((Vars.fromFn identityPorts).map fun selected =>
          frame.sourceKeep selected).countIndex
            (frame.sourceKeep wire).index.val := by
    simpa only [Diagram.vars_map_id] using
      Vars.countIndex_map_eq_of_index_eq
        ((Vars.fromFn identityPorts).map fun selected =>
          frame.sourceKeep selected)
        (fun selected => selected.appendLeft [])
        (fun selected => selected)
        (fun selected => Var.index_appendLeft _ _)
        (frame.sourceKeep wire).index.val
  simp only [operation, Region.singleton, Region.ofItems,
    Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
    Var.index_appendLeft, if_neg selectedNe]
  rw [targetCount, ← retainedPorts, ← sourceAppend]
  simp

/-- Identity leaf owns validity of its raw positional source.  The prepared
identity target supplies retained-wire validity; only the removed relation
binder's rootedness is additional. -/
theorem target_source_validity
    {outer retained : List Sig}
    {items : ItemSeq (outer ++
      (.rel (List.replicate arity signature) :: retained))}
    (edit : Transform.ItemsEdit (operation signature arity)
      (rootFrame outer [] retained signature arity) PUnit.unit items)
    (noPin : edit.NoSelectedPin)
    (targetCanonical :
      (Region.adjoinAt retained .nil edit.run).Canonical)
    (selectedRooted : RegionPath.RootedTwo
      (items.incidencePaths outer.length 0)) :
    ((.mk (.rel (List.replicate arity signature) :: retained) items :
        Region outer).Canonical) ∧
      ∀ {wireSignature} (wire : Var outer wireSignature),
        (Region.adjoinAt retained .nil edit.run).incidencePaths wire.index.val =
          (.mk (.rel (List.replicate arity signature) :: retained) items :
            Region outer).incidencePaths wire.index.val := by
  let frame := rootFrame outer [] retained signature arity
  have rootInvariant : Transform.RetainedIndexInvariant frame := by
    constructor
    · intro leftSignature rightSignature left right
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := [])
          (inserted := [.rel (List.replicate arity signature)])
          (after := retained) left right).trans
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := []) (inserted := [])
          (after := retained) left right).symm
    · intro wireSignature wire
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.insertedHead_ne_keep
          (outer := outer) (before := []) (after := retained)
          (selectedSignature := .rel (List.replicate arity signature))
          (inserted := []) wire)
  have materialCanonical : edit.run.Canonical :=
    Region.Canonical.material_of_adjoinAt retained .nil edit.run
      targetCanonical
  have child := Transform.ItemsEdit.retainedTargetToSource
    (fun invariantFrame (_ : (operation signature arity).Data invariantFrame) =>
      Transform.RetainedIndexInvariant invariantFrame)
    (fun invariantFrame _ locals hypothesis => hypothesis.append locals)
    (fun hypothesis => hypothesis)
    (fun hypothesis ports siteData =>
      identitySelectedAtom_retainedTargetToSource hypothesis ports siteData)
    identityItemEdit_run_items_length rootInvariant edit noPin
      materialCanonical
  have sourceCanonical :
      (.mk (.rel (List.replicate arity signature) :: retained) items :
        Region outer).Canonical := by
    refine ⟨?_, (ItemSeq.ChildrenCanonical.renameWires_iff items _).mp
      child.1.2⟩
    intro localIndex
    refine Fin.cases selectedRooted (fun retainedIndex => ?_) localIndex
    let retainedWire : Var (outer ++ retained) (retained.get retainedIndex) :=
      Var.appendRight outer (Var.ofIndex retainedIndex)
    have targetRoot :=
      Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil edit.run
        targetCanonical retainedIndex
    have paths := child.2 retainedWire
    rw [Region.incidencePaths_ofItems] at paths
    have targetRoot' : RegionPath.RootedTwo
        (edit.run.incidencePaths
          (frame.targetKeep retainedWire).index.val) := by
      simpa [retainedWire, frame, rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep,
        Var.appendMap_right, Var.appendMap, Var.appendRight, Var.index,
        Var.index_appendRight, List.length_nil, Nat.zero_add] using targetRoot
    have sourceRoot : RegionPath.RootedTwo
        (items.incidencePaths
          (frame.sourceKeep retainedWire).index.val 0) :=
      (congrArg RegionPath.RootedTwo paths).mp targetRoot'
    simpa [retainedWire, frame, rootFrame, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep,
      Var.appendMap_right, Var.appendMap, Var.appendRight, Var.index,
      Var.index_appendRight, List.length_nil, Nat.zero_add] using sourceRoot
  refine ⟨sourceCanonical, ?_⟩
  intro wireSignature wire
  have targetPaths := Region.incidencePaths_adjoinAt_nil edit.run
    (wire.appendLeft retained)
  have paths := child.2 (wire.appendLeft retained)
  rw [Region.incidencePaths_ofItems] at paths
  have paths' : edit.run.incidencePaths (wire.appendLeft retained).index.val =
      items.incidencePaths wire.index.val 0 := by
    simpa [frame, rootFrame, Transform.Frame.replace, Transform.Frame.keep,
      Transform.Frame.localKeep, Var.appendMap_left,
      Var.index_appendLeft] using paths
  simpa using targetPaths.trans paths'

structure Leaves.Description (outer : List Sig) where
  signature : Sig
  arity : Nat
  localBefore : List Sig
  localAfter : List Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (List.replicate arity signature) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation signature arity)
    (rootFrame outer localBefore localAfter signature arity) PUnit.unit items

def Leaves.Description.source (description : Leaves.Description outer) :
    Region outer :=
  .mk (description.localBefore ++
    .rel (List.replicate description.arity description.signature) ::
      description.localAfter) description.items

def Leaves.Description.target (description : Leaves.Description outer) :
    Region outer :=
  Region.adjoinAt (description.localBefore ++ description.localAfter) .nil
    description.itemsEdit.run

inductive Leaves : Region outer → Region outer → Prop
  | mk (description : Leaves.Description outer) :
      Leaves description.source description.target

inductive Local : LocalRule
  | abstractIdentity (step : Leaves applied identity) : Local identity applied

end Identity

end Leaf

def FormalApplication : Rule :=
  Contextual Leaf.Formal.Local

theorem FormalApplication.iso
    (sourceIso : OpenDiagramIso source source')
    (step : FormalApplication source target)
    (targetIso : OpenDiagramIso target target') :
    FormalApplication source' target' :=
  Contextual.iso sourceIso step targetIso

def IdentityLeaf : Rule :=
  Contextual Leaf.Identity.Local

theorem IdentityLeaf.iso
    (sourceIso : OpenDiagramIso source source')
    (step : IdentityLeaf source target)
    (targetIso : OpenDiagramIso target target') :
    IdentityLeaf source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
