import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Leaf

namespace VisualProof.Rule.Lambda.TermLeaf

open Diagram
open Theory
open WirePrimitive

def arguments (freeArity : Nat) : List Sig :=
  .iota :: List.replicate freeArity .iota

def Vars.fromTerm
    (output : Var context .iota)
    (ports : Fin freeArity → Var context .iota) :
    Vars context (arguments freeArity) :=
  .cons output (WirePrimitive.Leaf.Identity.Vars.fromFn ports)

def Vars.output (variables : Vars context (arguments freeArity)) :
    Var context .iota := by
  change Vars context (.iota :: List.replicate freeArity .iota) at variables
  exact match variables with
  | .cons output _ => output

def Vars.ports (variables : Vars context (arguments freeArity)) :
    Fin freeArity → Var context .iota := by
  change Vars context (.iota :: List.replicate freeArity .iota) at variables
  exact match variables with
  | .cons _ ports => WirePrimitive.Leaf.Identity.Vars.toFn ports

@[simp] theorem Vars.fromTerm_output_ports
    (variables : Vars context (arguments freeArity)) :
    Vars.fromTerm (Vars.output variables) (Vars.ports variables) = variables := by
  cases variables with
  | cons output ports =>
      change Vars.cons output
        (WirePrimitive.Leaf.Identity.Vars.fromFn
          (WirePrimitive.Leaf.Identity.Vars.toFn ports)) =
        Vars.cons output ports
      exact congrArg (Vars.cons output)
        (WirePrimitive.Leaf.Identity.Vars.fromFn_toFn ports)

@[simp] theorem Vars.output_fromTerm
    (output : Var context .iota)
    (ports : Fin freeArity → Var context .iota) :
    Vars.output (Vars.fromTerm output ports) = output := by
  rfl

@[simp] theorem Vars.ports_fromTerm
    (output : Var context .iota)
    (ports : Fin freeArity → Var context .iota) :
    Vars.ports (Vars.fromTerm output ports) = ports := by
  exact WirePrimitive.Leaf.Identity.Vars.toFn_fromFn ports

@[simp] theorem Vars.output_map
    (variables : Vars source (arguments freeArity))
    (rename : WireRenaming source target) :
    Vars.output (variables.map fun wire => rename wire) =
      rename (Vars.output variables) := by
  cases variables
  rfl

@[simp] theorem Vars.ports_map
    (variables : Vars source (arguments freeArity))
    (rename : WireRenaming source target) :
    Vars.ports (variables.map fun wire => rename wire) =
      fun slot => rename (Vars.ports variables slot) := by
  cases variables with
  | cons output ports =>
      exact WirePrimitive.Leaf.Identity.Vars.toFn_map ports rename

@[simp] theorem Vars.fromTerm_map
    (output : Var source .iota)
    (ports : Fin freeArity → Var source .iota)
    (rename : WireRenaming source target) :
    (Vars.fromTerm output ports).map (fun wire => rename wire) =
      Vars.fromTerm (rename output) (fun slot => rename (ports slot)) := by
  simp only [Vars.fromTerm, Vars.map]
  rw [WirePrimitive.Leaf.Identity.Vars.fromFn_map]

def operation (freeArity : Nat)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    Transform.Operation (arguments freeArity) where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun {common _sourceWires _targetWires} _frame _data application =>
    { termPorts : Var common .iota ×
        (Fin freeArity → Var common .iota) //
      application = Vars.fromTerm termPorts.1 termPorts.2 }
  site := fun frame _ _ siteData =>
    Region.singleton (.term (frame.targetKeep siteData.val.1) freeArity
      (fun slot => frame.targetKeep (siteData.val.2 slot)) term)
  pin := fun _ _ => Region.blank _

def rootFrame (outer localBefore localAfter : List Sig)
    (freeArity : Nat) :=
  Transform.Frame.replace outer localBefore localAfter []
    (arguments freeArity)

@[simp] theorem itemEdit_run_items_length
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (arguments freeArity) common
      sourceWires targetWires} {source : Item sourceWires}
    (edit : Transform.ItemEdit (operation freeArity term) frame PUnit.unit
      source)
    (noPin : edit.NoSelectedPin) :
    edit.run.items.length = 1 :=
  match edit with
  | .atom _ _ => rfl
  | .selectedAtom _ _ => rfl
  | .selectedPin _ _ => False.elim noPin
  | .identity _ _ _ => rfl
  | .term _ _ _ _ => rfl
  | .cut _ => rfl

theorem selectedAtom_retainedTargetToSource
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (arguments freeArity) common
      sourceWires targetWires}
    (invariant : Transform.RetainedIndexInvariant frame)
    (application : Vars common (arguments freeArity))
    (siteData : (operation freeArity term).SiteData frame PUnit.unit
      application) :
    Transform.RetainedScopeTransfer frame
      (Region.singleton (.atom frame.selected
        (application.map fun wire => frame.sourceKeep wire)))
      ((operation freeArity term).site frame PUnit.unit application
        siteData) := by
  rcases siteData with ⟨⟨output, ports⟩, applicationEq⟩
  intro _
  refine ⟨⟨fun index => Fin.elim0 index,
    ⟨True.intro, True.intro⟩⟩, ?_⟩
  intro wireSignature wire
  have selectedNe := invariant.selectedFresh wire
  subst application
  have retainedPorts := Transform.Vars.countIndex_map_eq_of_reflection
    (Vars.fromTerm output ports) frame.sourceKeep frame.targetKeep
    invariant.reflects wire
  have targetPorts :
      ((Vars.fromTerm output ports).map fun selected =>
        frame.targetKeep selected).countIndex
          (frame.targetKeep wire).index.val =
        (if (frame.targetKeep output).index.val =
              (frame.targetKeep wire).index.val then 1 else 0) +
          ((WirePrimitive.Leaf.Identity.Vars.fromFn ports).map fun selected =>
            frame.targetKeep selected).countIndex
              (frame.targetKeep wire).index.val := by
    rfl
  have targetTail :
      (List.ofFn fun slot : Fin freeArity =>
        (frame.targetKeep (ports slot)).index.val).count
          (frame.targetKeep wire).index.val =
        ((WirePrimitive.Leaf.Identity.Vars.fromFn ports).map fun selected =>
          frame.targetKeep selected).countIndex
            (frame.targetKeep wire).index.val := by
    calc
      _ = (WirePrimitive.Leaf.Identity.Vars.fromFn
          (fun slot => frame.targetKeep (ports slot))).countIndex
            (frame.targetKeep wire).index.val :=
        (WirePrimitive.Leaf.Identity.Vars.countIndex_fromFn _ _).symm
      _ = _ := by
        rw [← WirePrimitive.Leaf.Identity.Vars.fromFn_map]
  have sourceAppend :
      (((Vars.fromTerm output ports).map fun selected =>
        frame.sourceKeep selected).map fun selected =>
          selected.appendLeft []).countIndex
            (frame.sourceKeep wire).index.val =
        ((Vars.fromTerm output ports).map fun selected =>
          frame.sourceKeep selected).countIndex
            (frame.sourceKeep wire).index.val := by
    simpa only [Diagram.vars_map_id] using
      Vars.countIndex_map_eq_of_index_eq
        ((Vars.fromTerm output ports).map fun selected =>
          frame.sourceKeep selected)
        (fun selected => selected.appendLeft [])
        (fun selected => selected)
        (fun selected => Var.index_appendLeft _ _)
        (frame.sourceKeep wire).index.val
  simp only [operation, Region.singleton, Region.ofItems,
    Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
    ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
    Var.index_appendLeft, if_neg selectedNe]
  rw [targetTail, ← targetPorts, ← retainedPorts, ← sourceAppend]
  simp [Vars.fromTerm]

/-- A Lambda term leaf owns validity of its raw positional source at every
binder placement. -/
theorem target_source_validity
    {outer localBefore localAfter : List Sig}
    {items : ItemSeq (outer ++ (localBefore ++
      .rel (arguments freeArity) :: localAfter))}
    (edit : Transform.ItemsEdit (operation freeArity term)
      (rootFrame outer localBefore localAfter freeArity) PUnit.unit items)
    (noPin : edit.NoSelectedPin)
    (targetCanonical :
      (Region.adjoinAt (localBefore ++ localAfter) .nil edit.run).Canonical)
    (selectedRooted : RegionPath.RootedTwo
      (items.incidencePaths (outer.length + localBefore.length) 0)) :
    ((.mk (localBefore ++ .rel (arguments freeArity) :: localAfter)
        items : Region outer).Canonical) ∧
      ∀ {wireSignature} (wire : Var outer wireSignature),
        (Region.adjoinAt (localBefore ++ localAfter) .nil edit.run).incidencePaths
            wire.index.val =
          (.mk (localBefore ++ .rel (arguments freeArity) :: localAfter)
            items : Region outer).incidencePaths wire.index.val := by
  let sourceLocals := localBefore ++ .rel (arguments freeArity) :: localAfter
  let targetLocals := localBefore ++ localAfter
  let frame := rootFrame outer localBefore localAfter freeArity
  have rootInvariant : Transform.RetainedIndexInvariant frame := by
    constructor
    · intro leftSignature rightSignature left right
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := localBefore)
          (inserted := [.rel (arguments freeArity)])
          (after := localAfter) left right).trans
        (Transform.Frame.keep_index_eq_iff
          (outer := outer) (before := localBefore) (inserted := [])
          (after := localAfter) left right).symm
    · intro wireSignature wire
      simpa [frame, rootFrame, Transform.Frame.replace] using
        (Transform.Frame.insertedHead_ne_keep
          (outer := outer) (before := localBefore) (after := localAfter)
          (selectedSignature := .rel (arguments freeArity))
          (inserted := []) wire)
  have materialCanonical : edit.run.Canonical :=
    Region.Canonical.material_of_adjoinAt targetLocals .nil edit.run
      targetCanonical
  have child := Transform.ItemsEdit.retainedTargetToSource
    (fun invariantFrame (_ : (operation freeArity term).Data invariantFrame) =>
      Transform.RetainedIndexInvariant invariantFrame)
    (fun invariantFrame _ locals hypothesis => hypothesis.append locals)
    (fun hypothesis => hypothesis)
    (fun hypothesis application siteData =>
      selectedAtom_retainedTargetToSource hypothesis application siteData)
    itemEdit_run_items_length rootInvariant edit noPin materialCanonical
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
        ⟨beforeIndex.val, by simp only [targetLocals, List.length_append]; omega⟩
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
        simp [targetWire, targetIndex, frame, rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendRight]
      have sourceKeepIndex :
          (frame.sourceKeep targetWire).index.val =
            outer.length + localIndex.val := by
        simp [targetWire, beforeIndex, frame, rootFrame,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, Var.appendRight]
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
          simp [targetWire, targetIndex, frame, rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight]
        have sourceKeepIndex :
            (frame.sourceKeep targetWire).index.val =
              outer.length + localIndex.val := by
          simp [targetWire, afterIndex, frame, rootFrame,
            Transform.Frame.replace, Transform.Frame.keep,
            Transform.Frame.localKeep, Var.appendRight,
            Var.index]
          omega
        rw [targetKeepIndex, sourceKeepIndex] at paths
        exact (congrArg RegionPath.RootedTwo paths).mp targetRoot
  refine ⟨sourceCanonical, ?_⟩
  intro wireSignature wire
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

structure Leaves.Description (outer : List Sig) where
  freeArity : Nat
  term : VisualProof.Lambda.Term 0 (Fin freeArity)
  localBefore : List Sig
  localAfter : List Sig
  items : ItemSeq (outer ++ (localBefore ++
    .rel (arguments freeArity) :: localAfter))
  itemsEdit : Transform.ItemsEdit (operation freeArity term)
    (rootFrame outer localBefore localAfter freeArity) PUnit.unit items

def Leaves.Description.source (description : Leaves.Description outer) :
    Region outer :=
  .mk (description.localBefore ++
    .rel (arguments description.freeArity) :: description.localAfter)
    description.items

def Leaves.Description.target (description : Leaves.Description outer) :
    Region outer :=
  Region.adjoinAt (description.localBefore ++ description.localAfter) .nil
    description.itemsEdit.run

inductive Leaves : Region outer → Region outer → Prop
  | mk (description : Leaves.Description outer) :
      Leaves description.source description.target

inductive Local : LocalRule
  | abstractTerm (step : Leaves applied termRegion) : Local termRegion applied

end VisualProof.Rule.Lambda.TermLeaf

namespace VisualProof.Rule.Lambda

open Diagram

def TermLeaf : Rule := Contextual TermLeaf.Local

theorem TermLeaf.iso
    (sourceIso : OpenDiagramIso source source')
    (step : TermLeaf source target)
    (targetIso : OpenDiagramIso target target') :
    TermLeaf source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.Lambda
