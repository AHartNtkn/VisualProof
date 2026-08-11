import VisualProof.Concrete.Elaboration.Selection
import VisualProof.Concrete.Operation.Structural.Modal

/-! Source-only compiler evidence for the canonical double-cut replacement
fragment.  This module depends only on the successful replacement input and
its original extracted material compilation. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open Elaboration

namespace SelectionReplacement

/-- A replacement pattern as the exact arity-indexed compiler input used by
generic splice elaboration. -/
def patternState (replacement : SelectionReplacement input selection) :
    State replacement.pattern.val.boundary.length where
  checked := replacement.pattern
  boundary_length := rfl

end SelectionReplacement

namespace DoubleCutWrapper

/-- The rule-neutral nested-cut region introduced around the extracted
material body. -/
def wrapRegion (body : Region wires rels) : Region wires rels :=
  .mk 0 (.cons (.cut (.mk 0 (.cons (.cut body) .nil))) .nil)

private theorem castAdd_eq_iff (left right : Fin size) :
    Fin.castAdd added left = Fin.castAdd added right ↔ left = right := by
  constructor
  · intro equality
    apply Fin.ext
    exact congrArg (fun value : Fin (size + added) => value.val) equality
  · intro equality
    subst right
    rfl

private theorem natAdd_ne_castAdd (suffix : Fin added)
    (sourceIndex : Fin size) :
    Fin.natAdd size suffix ≠ Fin.castAdd added sourceIndex := by
  intro equality
  have values := congrArg
    (fun value : Fin (size + added) => value.val) equality
  simp only [Fin.val_natAdd, Fin.val_castAdd] at values
  omega

/-- Extend a source binder context to the wrapper's two new cut identities.
Neither cut binds a relation variable. -/
def liftBinders (pattern : OpenDiagram)
    (sourceSpine : BinderSpine pattern.diagram)
    (binders : BinderContext pattern.diagram rels) :
    BinderContext (diagram pattern sourceSpine) rels :=
  Fin.addCases binders (fun _ => none)

@[simp] theorem liftBinders_castAdd
    (pattern : OpenDiagram)
    (sourceSpine : BinderSpine pattern.diagram)
    (binders : BinderContext pattern.diagram rels)
    (region : Fin pattern.diagram.regionCount) :
    liftBinders pattern sourceSpine binders (Fin.castAdd 2 region) =
      binders region := by
  simp only [liftBinders, Fin.addCases_left]

@[simp] theorem liftBinders_natAdd
    (pattern : OpenDiagram)
    (sourceSpine : BinderSpine pattern.diagram)
    (binders : BinderContext pattern.diagram rels) (added : Fin 2) :
    liftBinders pattern sourceSpine binders
      (Fin.natAdd pattern.diagram.regionCount added) = none := by
  simp only [liftBinders, Fin.addCases_right]

/-- Lifting commutes with the compiler's bubble-binder push. -/
theorem liftBinders_push
    (pattern : OpenDiagram)
    (sourceSpine : BinderSpine pattern.diagram)
    (binders : BinderContext pattern.diagram rels)
    (binder : Fin pattern.diagram.regionCount) (arity : Nat) :
    liftBinders pattern sourceSpine (binders.push binder arity) =
      (liftBinders pattern sourceSpine binders).push
        (Fin.castAdd 2 binder) arity := by
  funext candidate
  refine Fin.addCases (fun sourceCandidate => ?_)
    (fun addedCandidate => ?_) candidate
  · rw [liftBinders_castAdd]
    by_cases atBinder : sourceCandidate = binder
    · subst sourceCandidate
      rw [BinderContext.push_self, BinderContext.push_self]
    · have liftedAway : Fin.castAdd 2 sourceCandidate ≠
          Fin.castAdd 2 binder := by
        intro equality
        exact atBinder ((castAdd_eq_iff _ _).1 equality)
      rw [BinderContext.push_other _ _ atBinder,
        BinderContext.push_other _ _ liftedAway, liftBinders_castAdd]
  · rw [liftBinders_natAdd]
    have addedAway : Fin.natAdd pattern.diagram.regionCount
        addedCandidate ≠ Fin.castAdd 2 binder :=
      natAdd_ne_castAdd addedCandidate binder
    rw [BinderContext.push_other _ _ addedAway, liftBinders_natAdd]
    rfl

/-- Lift an old concrete occurrence into the wrapper's unchanged node carrier
and old-region summand. -/
def liftOccurrence (pattern : OpenDiagram) :
    LocalOccurrence pattern.diagram.regionCount pattern.diagram.nodeCount →
      LocalOccurrence (pattern.diagram.regionCount + 2)
        pattern.diagram.nodeCount
  | .node node => .node node
  | .child child => .child (Fin.castAdd 2 child)

private theorem node_region_eq_lift_iff_of_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer)
    (node : Fin pattern.diagram.nodeCount) :
    ((diagram pattern spine).nodes node).region = Fin.castAdd 2 region ↔
      (pattern.diagram.nodes node).region = region := by
  simp only [diagram]
  split
  · rename_i bodyNode
    have sourceAway : (pattern.diagram.nodes node).region ≠ region := by
      simpa only [bodyNode] using Ne.symm away
    constructor
    · intro equality
      have targetRegion :
          (reparentLiftedNode 2
            (Fin.natAdd pattern.diagram.regionCount ⟨1, by decide⟩)
            (pattern.diagram.nodes node)).region =
              Fin.natAdd pattern.diagram.regionCount ⟨1, by decide⟩ := by
        cases pattern.diagram.nodes node <;> rfl
      rw [targetRegion] at equality
      exact False.elim
        ((natAdd_ne_castAdd ⟨1, by decide⟩ region) equality)
    · exact False.elim ∘ sourceAway
  · rename_i notBodyNode
    cases pattern.diagram.nodes node <;>
      simp only [liftCNode, CNode.region]
    all_goals exact castAdd_eq_iff _ _

private theorem region_parent_eq_lift_iff_of_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region child : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer) :
    ((diagram pattern spine).regions (Fin.castAdd 2 child)).parent? =
        some (Fin.castAdd 2 region) ↔
      (pattern.diagram.regions child).parent? = some region := by
  simp only [diagram, Fin.addCases_left]
  split
  · rename_i proxy
    cases pattern.diagram.regions child with
    | sheet =>
        constructor <;> intro impossible <;> cases impossible
    | cut parent =>
        simp only [liftCRegion, CRegion.parent?, Option.some.injEq]
        exact castAdd_eq_iff _ _
    | bubble parent arity =>
        simp only [liftCRegion, CRegion.parent?, Option.some.injEq]
        exact castAdd_eq_iff _ _
  · split
    · rename_i bodyParent
      have sourceNot :
          (pattern.diagram.regions child).parent? ≠ some region := by
        intro sourceParent
        have bodyEq : spine.bodyContainer = region :=
          Option.some.inj (bodyParent.symm.trans sourceParent)
        exact away bodyEq.symm
      have targetParentEq :
          (reparentLiftedRegion 2
            (Fin.natAdd pattern.diagram.regionCount ⟨1, by decide⟩)
            (pattern.diagram.regions child)).parent? =
              some (Fin.natAdd pattern.diagram.regionCount ⟨1, by decide⟩) := by
        cases childKind : pattern.diagram.regions child with
        | sheet => simp [childKind, CRegion.parent?] at bodyParent
        | cut parent => rfl
        | bubble parent arity => rfl
      constructor
      · intro targetParent
        rw [targetParentEq] at targetParent
        exact False.elim ((natAdd_ne_castAdd ⟨1, by decide⟩ region)
          (Option.some.inj targetParent))
      · exact False.elim ∘ sourceNot
    · rename_i notBodyParent
      cases pattern.diagram.regions child with
      | sheet =>
          constructor <;> intro impossible <;> cases impossible
      | cut parent =>
          simp only [liftCRegion, CRegion.parent?, Option.some.injEq]
          exact castAdd_eq_iff _ _
      | bubble parent arity =>
          simp only [liftCRegion, CRegion.parent?, Option.some.injEq]
          exact castAdd_eq_iff _ _

private theorem added_region_parent_ne_lift
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer) (added : Fin 2) :
    ((diagram pattern spine).regions
      (Fin.natAdd pattern.diagram.regionCount added)).parent? ≠
        some (Fin.castAdd 2 region) := by
  refine Fin.cases ?_ (fun tail => ?_) added
  · intro equality
    have parentEq : Fin.castAdd 2 spine.bodyContainer =
        Fin.castAdd 2 region := by
      simpa only [diagram, Fin.addCases_right, Fin.cases_zero,
        CRegion.parent?, Option.some.injEq] using equality
    exact away ((castAdd_eq_iff _ _).1 parentEq).symm
  · intro equality
    have parentEq : Fin.natAdd pattern.diagram.regionCount ⟨0, by decide⟩ =
        Fin.castAdd 2 region := by
      simpa only [diagram, Fin.addCases_right, Fin.cases_succ,
        CRegion.parent?, Option.some.injEq] using equality
    exact (natAdd_ne_castAdd ⟨0, by decide⟩ region) parentEq

private theorem allFin_add (left right : Nat) :
    allFin (left + right) =
      (allFin left).map (Fin.castAdd right) ++
        (allFin right).map (Fin.natAdd left) := by
  simp only [allFin_eq_finRange]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.length_finRange, List.length_append,
      List.length_map] at hright
    simp only [List.getElem_append, List.length_map, List.length_finRange]
    split
    · simp
    · simp
      omega

private theorem filterFin_add (predicate : Fin (left + right) → Bool) :
    filterFin predicate =
      (filterFin fun index : Fin left =>
        predicate (Fin.castAdd right index)).map (Fin.castAdd right) ++
      (filterFin fun index : Fin right =>
        predicate (Fin.natAdd left index)).map (Fin.natAdd left) := by
  unfold filterFin
  rw [allFin_add]
  simp only [List.filter_append, List.filter_map]
  rfl

/-- Every occurrence stream above the wrapped body is the old stream in the
same intrinsic order, with old child identities lifted into the wrapper. -/
theorem localOccurrences_lift_of_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer) :
    localOccurrences (diagram pattern spine) (Fin.castAdd 2 region) =
      (localOccurrences pattern.diagram region).map
        (liftOccurrence pattern) := by
  have nodeFilter :
      filterFin (fun node => decide
        (((diagram pattern spine).nodes node).region =
          Fin.castAdd 2 region)) =
        filterFin (fun node => decide
          ((pattern.diagram.nodes node).region = region)) := by
    unfold filterFin
    apply List.filter_congr
    intro node _
    exact decide_eq_decide.mpr
      (node_region_eq_lift_iff_of_ne pattern spine region away node)
  have oldChildFilter :
      filterFin (fun child : Fin pattern.diagram.regionCount => decide
        (((diagram pattern spine).regions (Fin.castAdd 2 child)).parent? =
          some (Fin.castAdd 2 region))) =
        filterFin (fun child => decide
          ((pattern.diagram.regions child).parent? = some region)) := by
    unfold filterFin
    apply List.filter_congr
    intro child _
    exact decide_eq_decide.mpr
      (region_parent_eq_lift_iff_of_ne pattern spine region child away)
  have addedChildFilter :
      filterFin (fun added : Fin 2 => decide
        (((diagram pattern spine).regions
          (Fin.natAdd pattern.diagram.regionCount added)).parent? =
            some (Fin.castAdd 2 region))) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro added member
    have accepted := of_decide_eq_true
      (List.mem_filter.mp member).2
    exact added_region_parent_ne_lift pattern spine region away added
      accepted
  have childFilter :
      filterFin (fun child => decide
        (((diagram pattern spine).regions child).parent? =
          some (Fin.castAdd 2 region))) =
        (filterFin fun child => decide
          ((pattern.diagram.regions child).parent? = some region)).map
            (Fin.castAdd 2) := by
    calc
      _ = (filterFin fun child : Fin pattern.diagram.regionCount => decide
            (((diagram pattern spine).regions
              (Fin.castAdd 2 child)).parent? =
                some (Fin.castAdd 2 region))).map (Fin.castAdd 2) ++
          (filterFin fun added : Fin 2 => decide
            (((diagram pattern spine).regions
              (Fin.natAdd pattern.diagram.regionCount added)).parent? =
                some (Fin.castAdd 2 region))).map
                  (Fin.natAdd pattern.diagram.regionCount) :=
        filterFin_add _
      _ = _ := by
        rw [oldChildFilter, addedChildFilter]
        simp only [List.map_nil, List.append_nil]
  unfold localOccurrences
  calc
    _ = (filterFin fun node => decide
          ((pattern.diagram.nodes node).region = region)).map
            (fun node => (LocalOccurrence.node node :
              LocalOccurrence (pattern.diagram.regionCount + 2)
                pattern.diagram.nodeCount)) ++
        ((filterFin fun child => decide
          ((pattern.diagram.regions child).parent? = some region)).map
            (Fin.castAdd 2)).map LocalOccurrence.child := by
      have nodesEq := congrArg
        (List.map fun node => (LocalOccurrence.node node :
          LocalOccurrence (pattern.diagram.regionCount + 2)
            pattern.diagram.nodeCount)) nodeFilter
      have childrenEq := congrArg
        (List.map fun child => (LocalOccurrence.child child :
          LocalOccurrence (pattern.diagram.regionCount + 2)
            pattern.diagram.nodeCount)) childFilter
      exact (congrArg (fun nodes => nodes ++
        (filterFin fun child => decide
          (((diagram pattern spine).regions child).parent? =
            some (Fin.castAdd 2 region))).map
              (fun child => (LocalOccurrence.child child :
                LocalOccurrence (pattern.diagram.regionCount + 2)
                  pattern.diagram.nodeCount))) nodesEq).trans
        (congrArg (List.append
          ((filterFin fun node => decide
            ((pattern.diagram.nodes node).region = region)).map
              (fun node => (LocalOccurrence.node node :
                LocalOccurrence (pattern.diagram.regionCount + 2)
                  pattern.diagram.nodeCount)))) childrenEq)
    _ = _ := by
      simp only [List.map_append, List.map_map, liftOccurrence,
        Function.comp_def]

/-- Wrapper construction changes only concrete wire scopes; endpoint order and
ownership remain literal source data. -/
theorem wire_endpoints
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (wire : Fin pattern.diagram.wireCount) :
    ((diagram pattern spine).wires wire).endpoints =
      (pattern.diagram.wires wire).endpoints := by
  simp only [diagram]
  split
  · cases pattern.diagram.wires wire
    rfl
  · split
    · rfl
    · cases pattern.diagram.wires wire
      rfl

/-- Port resolution is unchanged by the wrapper's scope-only wire update. -/
theorem resolvePort_lift
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (context : WireContext pattern.diagram)
    (node : Fin pattern.diagram.nodeCount) (port : CPort) :
    resolvePort? (diagram pattern spine) context node port =
      resolvePort? pattern.diagram context node port := by
  have owners :
      (allFin pattern.diagram.wireCount).filter (fun wire => decide
        (⟨node, port⟩ ∈ ((diagram pattern spine).wires wire).endpoints)) =
      (allFin pattern.diagram.wireCount).filter (fun wire => decide
        (⟨node, port⟩ ∈ (pattern.diagram.wires wire).endpoints)) := by
    apply List.filter_congr
    intro wire _
    rw [wire_endpoints]
    rfl
  have ownerEq :
      endpointOwner? (diagram pattern spine) ⟨node, port⟩ =
        endpointOwner? pattern.diagram ⟨node, port⟩ := by
    unfold endpointOwner?
      VisualProof.Concrete.Diagram.EndpointOccurs filterFin
    change
      ((allFin pattern.diagram.wireCount).filter (fun wire => decide
        (⟨node, port⟩ ∈ ((diagram pattern spine).wires wire).endpoints))).head? =
      ((allFin pattern.diagram.wireCount).filter (fun wire => decide
        (⟨node, port⟩ ∈ (pattern.diagram.wires wire).endpoints))).head?
    rw [owners]
    rfl
  unfold resolvePort?
  rw [ownerEq]
  rfl

/-- Simultaneous argument resolution is therefore unchanged as well. -/
theorem resolvePorts_lift
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (context : WireContext pattern.diagram)
    (node : Fin pattern.diagram.nodeCount) (arity : Nat)
    (port : Fin arity → CPort) :
    resolvePorts? (diagram pattern spine) context node arity port =
      resolvePorts? pattern.diagram context node arity port := by
  unfold resolvePorts?
  apply congrArg sequenceFin
  funext index
  exact resolvePort_lift pattern spine context node (port index)

/-- Away from the wrapped body, each old node retains its kind and lifted
concrete region/binder identities. -/
theorem node_lift_of_region_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (node : Fin pattern.diagram.nodeCount)
    (away : (pattern.diagram.nodes node).region ≠ spine.bodyContainer) :
    (diagram pattern spine).nodes node =
      liftCNode 2 (pattern.diagram.nodes node) := by
  simp only [diagram]
  rw [if_neg away]

/-- Node compilation commutes literally with the old-region embedding. -/
theorem compileNode?_lift_of_region_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (context : WireContext pattern.diagram)
    (binders : BinderContext pattern.diagram rels)
    (node : Fin pattern.diagram.nodeCount)
    (away : (pattern.diagram.nodes node).region ≠ spine.bodyContainer) :
    compileNode? (diagram pattern spine) context
        (liftBinders pattern spine binders) node =
      compileNode? pattern.diagram context binders node := by
  unfold compileNode?
  rw [node_lift_of_region_ne pattern spine node away]
  cases nodeKind : pattern.diagram.nodes node with
  | atom region binder =>
      simp only [liftCNode]
      rw [liftBinders_castAdd]
      cases lookup : binders binder with
      | none => rfl
      | some found =>
          cases found with
          | mk foundArity foundRelation =>
              change (do
                  let arguments ← resolvePorts? (diagram pattern spine)
                    context node foundArity
                  pure (Item.atom foundRelation arguments)) =
                (do
                  let arguments ← resolvePorts? pattern.diagram context
                    node foundArity
                  pure (Item.atom foundRelation arguments))
              rw [resolvePorts_lift]
              rfl
  | identity region arity =>
      simp only [liftCNode]
      rw [resolvePorts_lift]
      rfl

/-- One direct occurrence above the wrapped body compiles exactly as its
source occurrence, assuming the recursive old-region calls commute. -/
theorem compileOccurrenceWith?_lift_of_mem
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin pattern.diagram.regionCount) →
      (context : WireContext pattern.diagram) →
      BinderContext pattern.diagram rels →
      Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin (diagram pattern spine).regionCount) →
      (context : WireContext (diagram pattern spine)) →
      BinderContext (diagram pattern spine) rels →
      Option (Region context.length rels))
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer)
    (recursive : ∀ {rels : RelCtx}
      (child : Fin pattern.diagram.regionCount)
      (context : WireContext pattern.diagram)
      (binders : BinderContext pattern.diagram rels),
      (pattern.diagram.regions child).parent? = some region →
      targetRecurse (Fin.castAdd 2 child) context
          (liftBinders pattern spine binders) =
        sourceRecurse child context binders)
    (context : WireContext pattern.diagram)
    (binders : BinderContext pattern.diagram rels)
    (occurrence : LocalOccurrence pattern.diagram.regionCount
      pattern.diagram.nodeCount)
    (member : occurrence ∈ localOccurrences pattern.diagram region) :
    compileOccurrenceWith? (diagram pattern spine) targetRecurse context
        (liftBinders pattern spine binders) (liftOccurrence pattern occurrence) =
      compileOccurrenceWith? pattern.diagram sourceRecurse context binders
        occurrence := by
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (mem_localOccurrences_node pattern.diagram region node).1 member
      have nodeAway : (pattern.diagram.nodes node).region ≠
          spine.bodyContainer := by
        intro atBody
        exact away (nodeRegion.symm.trans atBody)
      simp only [liftOccurrence, compileOccurrenceWith?]
      exact compileNode?_lift_of_region_ne pattern spine context binders node
        nodeAway
  | child child =>
      have parent :=
        (mem_localOccurrences_child pattern.diagram region child).1 member
      have notBodyParent :
          (pattern.diagram.regions child).parent? ≠
            some spine.bodyContainer := by
        intro bodyParent
        exact away (Option.some.inj (parent.symm.trans bodyParent))
      simp only [liftOccurrence, compileOccurrenceWith?]
      simp only [diagram, Fin.addCases_left]
      by_cases proxy : ∃ index, child = spine.proxy index
      · rw [if_pos proxy]
        cases childKind : pattern.diagram.regions child with
        | sheet => rfl
        | cut sourceParent =>
            simp only [liftCRegion]
            rw [recursive child context binders parent]
        | bubble sourceParent arity =>
            simp only [liftCRegion]
            have targetRecursive : targetRecurse (Fin.castAdd 2 child)
                context ((liftBinders pattern spine binders).push
                  (Fin.castAdd 2 child) arity) =
                sourceRecurse child context (binders.push child arity) := by
              calc
                _ = targetRecurse (Fin.castAdd 2 child) context
                    (liftBinders pattern spine
                      (binders.push child arity)) :=
                  congrArg (targetRecurse (Fin.castAdd 2 child) context)
                    (liftBinders_push pattern spine binders child arity).symm
                _ = _ := recursive child context (binders.push child arity)
                  parent
            exact congrArg
              (fun recursiveResult => recursiveResult.bind fun childBody =>
                some (Item.bubble arity childBody))
              targetRecursive
      · rw [if_neg proxy, if_neg notBodyParent]
        cases childKind : pattern.diagram.regions child with
        | sheet => rfl
        | cut sourceParent =>
            simp only [liftCRegion]
            rw [recursive child context binders parent]
        | bubble sourceParent arity =>
            simp only [liftCRegion]
            have targetRecursive : targetRecurse (Fin.castAdd 2 child)
                context ((liftBinders pattern spine binders).push
                  (Fin.castAdd 2 child) arity) =
                sourceRecurse child context (binders.push child arity) := by
              calc
                _ = targetRecurse (Fin.castAdd 2 child) context
                    (liftBinders pattern spine
                      (binders.push child arity)) :=
                  congrArg (targetRecurse (Fin.castAdd 2 child) context)
                    (liftBinders_push pattern spine binders child arity).symm
                _ = _ := recursive child context (binders.push child arity)
                  parent
            exact congrArg
              (fun recursiveResult => recursiveResult.bind fun childBody =>
                some (Item.bubble arity childBody))
              targetRecursive

/-- Compiling every direct occurrence at an unchanged lifted region is the
source compilation, provided recursive calls commute at its exact children. -/
theorem compileOccurrencesWith?_lift_of_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin pattern.diagram.regionCount) →
      (context : WireContext pattern.diagram) →
      BinderContext pattern.diagram rels →
      Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin (diagram pattern spine).regionCount) →
      (context : WireContext (diagram pattern spine)) →
      BinderContext (diagram pattern spine) rels →
      Option (Region context.length rels))
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer)
    (recursive : ∀ {rels : RelCtx}
      (child : Fin pattern.diagram.regionCount)
      (context : WireContext pattern.diagram)
      (binders : BinderContext pattern.diagram rels),
      (pattern.diagram.regions child).parent? = some region →
      targetRecurse (Fin.castAdd 2 child) context
          (liftBinders pattern spine binders) =
        sourceRecurse child context binders)
    (context : WireContext pattern.diagram)
    (binders : BinderContext pattern.diagram rels) :
    compileOccurrencesWith? (diagram pattern spine) targetRecurse context
        (liftBinders pattern spine binders)
        (localOccurrences (diagram pattern spine) (Fin.castAdd 2 region)) =
      compileOccurrencesWith? pattern.diagram sourceRecurse context binders
        (localOccurrences pattern.diagram region) := by
  rw [localOccurrences_lift_of_ne pattern spine region away]
  have mapped := compileOccurrencesWith?_map sourceRecurse targetRecurse
    context context binders (liftBinders pattern spine binders)
    (liftOccurrence pattern) id (localOccurrences pattern.diagram region)
    (by
      intro occurrence member
      have compiled := compileOccurrenceWith?_lift_of_mem pattern spine
        sourceRecurse targetRecurse region away recursive context binders
        occurrence member
      rw [compiled]
      cases sourceResult : compileOccurrenceWith? pattern.diagram
          sourceRecurse context binders occurrence with
      | none => rfl
      | some item =>
          exact congrArg some (Item.renameWires_id item).symm)
  cases sourceResult : compileOccurrencesWith? pattern.diagram sourceRecurse
      context binders (localOccurrences pattern.diagram region) with
  | none =>
      rw [sourceResult] at mapped
      simpa only [Option.map_none] using mapped
  | some items =>
      rw [sourceResult] at mapped
      change compileOccurrencesWith? (diagram pattern spine) targetRecurse
          context (liftBinders pattern spine binders)
          ((localOccurrences pattern.diagram region).map
            (liftOccurrence pattern)) =
        some (ItemSeq.renameWires id items) at mapped
      rw [ItemSeq.renameWires_id items] at mapped
      exact mapped

@[simp] theorem openDiagram_boundary
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram) :
    (openDiagram pattern spine).boundary = pattern.boundary := rfl

@[simp] theorem spine_proxyCount
    (pattern : OpenDiagram) (source : BinderSpine pattern.diagram) :
    (spine pattern source).proxyCount = source.proxyCount := rfl

@[simp] theorem spine_proxy
    (pattern : OpenDiagram) (source : BinderSpine pattern.diagram)
    (index : Fin source.proxyCount) :
    (spine pattern source).proxy index = Fin.castAdd 2 (source.proxy index) :=
  rfl

@[simp] theorem spine_arity
    (pattern : OpenDiagram) (source : BinderSpine pattern.diagram)
    (index : Fin source.proxyCount) :
    (spine pattern source).arity index = source.arity index := rfl

@[simp] theorem spine_bodyContainer
    (pattern : OpenDiagram) (source : BinderSpine pattern.diagram) :
    (spine pattern source).bodyContainer =
      Fin.castAdd 2 source.bodyContainer := rfl

/-- Exact local-wire order is unchanged at every lifted region other than the
wrapped body container. -/
theorem exactScopeWires_lift_of_ne
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer) :
    exactScopeWires (diagram pattern spine) (Fin.castAdd 2 region) =
      exactScopeWires pattern.diagram region := by
  unfold exactScopeWires filterFin
  apply List.filter_congr
  intro wire _
  simp only [diagram]
  split
  · rename_i boundary
    exact decide_eq_decide.mpr (castAdd_eq_iff _ _)
  · split
    · rename_i bodyScope
      have sourceAway : (pattern.diagram.wires wire).scope ≠ region := by
        simpa only [bodyScope] using Ne.symm away
      simp only [sourceAway, decide_false]
      apply decide_eq_false
      intro equality
      have values := congrArg Fin.val equality
      simp only [Fin.val_natAdd, Fin.val_castAdd] at values
      omega
    · rename_i bodyScope
      exact decide_eq_decide.mpr (castAdd_eq_iff _ _)

private theorem compileOccurrencesWith?_castContext_eq
    {sourceDiagram : Concrete.Diagram}
    {sourceContext targetContext : WireContext sourceDiagram}
    (contextEq : sourceContext = targetContext)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) →
      BinderContext sourceDiagram rels → Option (Region context.length rels))
    (binders : BinderContext sourceDiagram rels)
    (occurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount)) :
    compileOccurrencesWith? sourceDiagram recurse targetContext binders
        occurrences =
      (compileOccurrencesWith? sourceDiagram recurse sourceContext binders
        occurrences).map fun items =>
          items.castWiresEq (congrArg List.length contextEq) := by
  subst targetContext
  cases compileOccurrencesWith? sourceDiagram recurse sourceContext binders
      occurrences <;> rfl

private theorem ItemSeq.castWiresEq_proof_irrel
    (first second : source = target) (items : ItemSeq source rels) :
    items.castWiresEq first = items.castWiresEq second := by
  rw [show first = second from Subsingleton.elim _ _]

private theorem finishRegion_castContext_eq_mk
    {sourceDiagram : Concrete.Diagram}
    (context : WireContext sourceDiagram)
    (region : Fin sourceDiagram.regionCount)
    (targetContext targetLocals : WireContext sourceDiagram)
    (targetLocalCount : Nat)
    (contextEq : context.extend region = targetContext)
    (localsEq : exactScopeWires sourceDiagram region = targetLocals)
    (localsLengthEq : targetLocals.length = targetLocalCount)
    (targetSplit : targetContext.length =
      context.length + targetLocalCount)
    (items : ItemSeq targetContext.length rels) :
    finishRegion sourceDiagram context region
        (items.castWiresEq (congrArg List.length contextEq.symm)) =
      .mk targetLocalCount (items.castWiresEq targetSplit) := by
  subst targetContext
  subst targetLocals
  subst targetLocalCount
  simp only [finishRegion, ItemSeq.castWiresEq_trans]

private theorem finishRegion_lift
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (region : Fin pattern.diagram.regionCount)
    (away : region ≠ spine.bodyContainer)
    (context : WireContext pattern.diagram)
    (items : ItemSeq (context.extend region).length rels) :
    let extendedEq : context.extend region =
        WireContext.extend (d := diagram pattern spine) context
          (Fin.castAdd 2 region) := by
      unfold WireContext.extend
      exact congrArg (context ++ ·)
        (exactScopeWires_lift_of_ne pattern spine region away).symm
    finishRegion (diagram pattern spine) context (Fin.castAdd 2 region)
        (items.castWiresEq (congrArg List.length extendedEq)) =
      finishRegion pattern.diagram context region items := by
  dsimp only
  let sourceLocals := exactScopeWires pattern.diagram region
  let sourceExtended : WireContext pattern.diagram := context ++ sourceLocals
  have targetContextEq :
      WireContext.extend (d := diagram pattern spine) context
          (Fin.castAdd 2 region) = sourceExtended := by
    unfold WireContext.extend sourceExtended sourceLocals
    exact congrArg (context ++ ·)
      (exactScopeWires_lift_of_ne pattern spine region away)
  have targetCanonical := finishRegion_castContext_eq_mk
    (sourceDiagram := diagram pattern spine) context
    (Fin.castAdd 2 region) sourceExtended sourceLocals sourceLocals.length
    targetContextEq
    (exactScopeWires_lift_of_ne pattern spine region away) rfl
    (by exact List.length_append) items
  have sourceCanonical := finishRegion_castContext_eq_mk
    (sourceDiagram := pattern.diagram) context region sourceExtended
    sourceLocals sourceLocals.length rfl rfl rfl
    (by exact List.length_append) items
  calc
    _ = .mk sourceLocals.length
        (items.castWiresEq (WireContext.length_extend context region)) := by
      simpa only [ItemSeq.castWiresEq_proof_irrel] using targetCanonical
    _ = _ := by
      symm
      simpa only [ItemSeq.castWiresEq_proof_irrel] using sourceCanonical

/-- A source subtree which does not enclose the wrapped body compiles
literally after lifting.  Non-enclosure is inherited by every recursive
child, so this theorem never crosses the replacement route. -/
theorem compileRegion?_lift_of_not_encloses
    (pattern : OpenDiagram) (spine : BinderSpine pattern.diagram)
    (wellFormed : pattern.diagram.WellFormed)
    (fuel : Nat) (region : Fin pattern.diagram.regionCount)
    (siteOutside : ¬pattern.diagram.Encloses region spine.bodyContainer)
    (context : WireContext pattern.diagram)
    (binders : BinderContext pattern.diagram rels) :
    compileRegion? (diagram pattern spine) fuel (Fin.castAdd 2 region)
        context (liftBinders pattern spine binders) =
      compileRegion? pattern.diagram fuel region context binders := by
  induction fuel generalizing region rels context binders with
  | zero => rfl
  | succ fuel ih =>
      have away : region ≠ spine.bodyContainer := by
        intro atSite
        subst region
        exact siteOutside
          (Diagram.Encloses.refl pattern.diagram spine.bodyContainer)
      let sourceExtended := context.extend region
      let targetExtended := WireContext.extend
        (d := diagram pattern spine) context (Fin.castAdd 2 region)
      have extendedEq : sourceExtended = targetExtended := by
        unfold sourceExtended targetExtended WireContext.extend
        exact congrArg (context ++ ·)
          (exactScopeWires_lift_of_ne pattern spine region away).symm
      have occurrences := compileOccurrencesWith?_lift_of_ne pattern spine
        (compileRegion? pattern.diagram fuel)
        (compileRegion? (diagram pattern spine) fuel) region away
        (by
          intro _ child childContext childBinders parent
          have regionChild : pattern.diagram.Encloses region child := by
            refine ⟨⟨1, by
              have := child.isLt
              omega⟩, ?_⟩
            simp only [Diagram.climb, parent]
          have childOutside :
              ¬pattern.diagram.Encloses child spine.bodyContainer := by
            intro childSite
            exact siteOutside (checked_encloses_trans wellFormed
              regionChild childSite)
          exact ih child childOutside childContext childBinders)
        sourceExtended binders
      have targetContextCast := compileOccurrencesWith?_castContext_eq
        (sourceDiagram := diagram pattern spine) extendedEq
        (compileRegion? (diagram pattern spine) fuel)
        (liftBinders pattern spine binders)
        (localOccurrences (diagram pattern spine) (Fin.castAdd 2 region))
      rw [occurrences] at targetContextCast
      simp only [compileRegion?]
      cases sourceResult : compileOccurrencesWith? pattern.diagram
          (compileRegion? pattern.diagram fuel) sourceExtended binders
          (localOccurrences pattern.diagram region) with
      | none =>
          rw [sourceResult] at targetContextCast
          change compileOccurrencesWith? (diagram pattern spine)
              (compileRegion? (diagram pattern spine) fuel) targetExtended
              (liftBinders pattern spine binders)
              (localOccurrences (diagram pattern spine)
                (Fin.castAdd 2 region)) = none at targetContextCast
          rw [targetContextCast]
          rfl
      | some items =>
          rw [sourceResult] at targetContextCast
          change compileOccurrencesWith? (diagram pattern spine)
              (compileRegion? (diagram pattern spine) fuel) targetExtended
              (liftBinders pattern spine binders)
              (localOccurrences (diagram pattern spine)
                (Fin.castAdd 2 region)) =
            some (items.castWiresEq
              (congrArg List.length extendedEq)) at targetContextCast
          rw [targetContextCast]
          simp only [Option.pure_def]
          apply congrArg some
          simpa only [ItemSeq.castWiresEq_proof_irrel] using
            finishRegion_lift pattern spine region away context items

end DoubleCutWrapper

/-- A successful double-cut replacement retains exactly the canonical wrapped
extraction as its open pattern. -/
theorem doubleCutWrappedReplacement_pattern
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (success : doubleCutWrappedReplacement source.diagram selection =
      .ok replacement) :
    replacement.pattern.val = DoubleCutWrapper.openDiagram
      (extractedSelectionOpen source selection).val
  (extractedSelectionSpine source selection) := by
  unfold doubleCutWrappedReplacement at success
  dsimp only at success
  split at success <;> try contradiction
  cases success
  rfl

/-- A successful double-cut replacement retains exactly the lifted canonical
binder spine. -/
theorem doubleCutWrappedReplacement_binderSpine
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (success : doubleCutWrappedReplacement source.diagram selection =
      .ok replacement) :
    HEq replacement.binderSpine (DoubleCutWrapper.spine
      (extractedSelectionOpen source selection).val
      (extractedSelectionSpine source selection)) := by
  unfold doubleCutWrappedReplacement at success
  dsimp only at success
  split at success <;> try contradiction
  cases success
  rfl

end VisualProof.Concrete
