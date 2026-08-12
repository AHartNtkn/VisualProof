import VisualProof.Concrete.Elaboration.Compile.Kernel
import VisualProof.Concrete.Open

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private def descendantRegions (d : Diagram)
    (region : Fin d.regionCount) : List (Fin d.regionCount) :=
  filterFin fun candidate => decide (d.Encloses region candidate)

private theorem filter_sublist_filter {values : List α} {p q : α → Bool}
    (implication : ∀ value, p value = true → q value = true) :
    (values.filter p).Sublist (values.filter q) := by
  induction values with
  | nil => exact .slnil
  | cons head tail ih =>
      cases hp : p head with
      | false =>
          cases hq : q head with
          | false => simpa [hp, hq] using ih
          | true => simpa [hp, hq] using ih.cons head
      | true =>
          have hq := implication head hp
          simpa [hp, hq] using ih.cons_cons head

private theorem descendantRegions_length_lt_of_parent
    {d : Diagram} (hwf : d.WellFormed)
    {child parent : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    (descendantRegions d child).length <
      (descendantRegions d parent).length := by
  have sublist : (descendantRegions d child).Sublist
      (descendantRegions d parent) := by
    have parentChild : d.Encloses parent child := by
      refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
      simp [Diagram.climb, hparent]
    apply filter_sublist_filter
    intro candidate candidateMember
    simp only [decide_eq_true_eq] at candidateMember ⊢
    exact checked_encloses_trans hwf parentChild candidateMember
  have distinct : descendantRegions d child ≠
      descendantRegions d parent := by
    intro equal
    have parentMember : parent ∈ descendantRegions d parent := by
      simp [descendantRegions, Diagram.Encloses.refl]
    have childMember : parent ∈ descendantRegions d child := by
      rw [equal]
      exact parentMember
    simp only [descendantRegions, mem_filterFin, decide_eq_true_eq]
      at childMember
    exact checked_direct_child_not_encloses_parent hwf hparent childMember
  have lengthLe := sublist.length_le
  have lengthNe : (descendantRegions d child).length ≠
      (descendantRegions d parent).length := by
    intro equal
    exact distinct (sublist.eq_of_length equal)
  omega

private structure ValidItemsResult (d : Diagram)
    (parent : Fin d.regionCount)
    (origins : List (LocalOccurrence d.regionCount d.nodeCount)) where
  items : CompiledItems d
  origins_eq : items.origins = origins
  valid : items.ValidAt parent

private noncomputable def compileNodeList (d : Diagram) (hwf : d.WellFormed)
    (parent : Fin d.regionCount) :
    (nodes : List (Fin d.nodeCount)) →
    (∀ node, node ∈ nodes → (d.nodes node).region = parent) →
    ValidItemsResult d parent (nodes.map LocalOccurrence.node)
  | [], _ => ⟨.nil, rfl, trivial⟩
  | node :: tail, hlocal =>
      let rest := compileNodeList d hwf parent tail
        (fun candidate member => hlocal candidate (by simp [member]))
      ⟨.cons (compileNode d hwf node) rest.items, by
        simp [rest.origins_eq], ⟨by
          simpa [hlocal node (by simp)] using compileNode_valid d hwf node,
        rest.valid⟩⟩

private noncomputable def compileNodeItems (d : Diagram) (hwf : d.WellFormed)
    (origin : Fin d.regionCount) :
    ValidItemsResult d origin (localNodeOccurrences d origin) := by
  unfold localNodeOccurrences
  apply compileNodeList d hwf origin
  intro node member
  simpa using member

/-- Canonical symbolic compilation of one region. -/
noncomputable def compileRegion (d : Diagram) (hwf : d.WellFormed)
    : (origin : Fin d.regionCount) → CompiledRegion d
  | origin =>
      let nodes := (compileNodeItems d hwf origin).items
      let children := (filterFin fun child =>
          decide ((d.regions child).parent? = some origin)).foldr
        (fun child tail =>
          if _parentEq : (d.regions child).parent? = some origin then
            match d.regions child with
            | .sheet => tail
            | .cut _ => .cons (.cut (compileRegion d hwf child)) tail
            | .bubble _ arity =>
                .cons (.bubble arity (compileRegion d hwf child)) tail
          else tail) .nil
      .mk origin nodes children
termination_by origin => (descendantRegions d origin).length
decreasing_by
  all_goals exact descendantRegions_length_lt_of_parent hwf _parentEq

@[simp] theorem compileRegion_origin (d : Diagram) (hwf : d.WellFormed)
    (origin : Fin d.regionCount) :
    (compileRegion d hwf origin).origin = origin := by
  rw [compileRegion]
  rfl

private theorem compileChildFold_valid (d : Diagram) (hwf : d.WellFormed)
    (origin : Fin d.regionCount) (children : List (Fin d.regionCount))
    (direct : ∀ child, child ∈ children →
      (d.regions child).parent? = some origin)
    (childrenValid : ∀ child, child ∈ children →
      (compileRegion d hwf child).Valid) :
    let compiled : CompiledItems d := children.foldr
      (fun child tail =>
        if _parentEq : (d.regions child).parent? = some origin then
          match d.regions child with
          | .sheet => tail
          | .cut _ => CompiledItems.cons
              (CompiledItem.cut (compileRegion d hwf child)) tail
          | .bubble _ arity => CompiledItems.cons
              (CompiledItem.bubble arity (compileRegion d hwf child)) tail
        else tail) CompiledItems.nil
    compiled.origins = children.map LocalOccurrence.child ∧
      compiled.ValidAt origin := by
  induction children with
  | nil => exact ⟨rfl, trivial⟩
  | cons child tail ih =>
      have parentEq := direct child (by simp)
      have tailDirect : ∀ candidate, candidate ∈ tail →
          (d.regions candidate).parent? = some origin := by
        intro candidate member
        exact direct candidate (by simp [member])
      have tailValid : ∀ candidate, candidate ∈ tail →
          (compileRegion d hwf candidate).Valid := by
        intro candidate member
        exact childrenValid candidate (by simp [member])
      have tailResult := ih tailDirect tailValid
      let tailItems : CompiledItems d := tail.foldr
        (fun candidate rest =>
          if _parentEq : (d.regions candidate).parent? = some origin then
            match d.regions candidate with
            | .sheet => rest
            | .cut _ => CompiledItems.cons
                (CompiledItem.cut (compileRegion d hwf candidate)) rest
            | .bubble _ arity => CompiledItems.cons
                (CompiledItem.bubble arity (compileRegion d hwf candidate))
                rest
          else rest) CompiledItems.nil
      cases shape : d.regions child with
      | sheet => rw [shape] at parentEq; cases parentEq
      | cut childParent =>
          have parentSame : childParent = origin := by
            rw [shape] at parentEq
            exact Option.some.inj parentEq
          subst childParent
          have foldedEq :
              (child :: tail).foldr
                (fun candidate rest =>
                  if _parentEq :
                      (d.regions candidate).parent? = some origin then
                    match d.regions candidate with
                    | .sheet => rest
                    | .cut _ => CompiledItems.cons
                        (CompiledItem.cut (compileRegion d hwf candidate)) rest
                    | .bubble _ arity => CompiledItems.cons
                        (CompiledItem.bubble arity
                          (compileRegion d hwf candidate)) rest
                  else rest) CompiledItems.nil =
                CompiledItems.cons
                  (CompiledItem.cut (compileRegion d hwf child)) tailItems := by
            rw [List.foldr_cons, dif_pos parentEq, shape]
          rw [foldedEq]
          refine ⟨?_, ?_⟩
          · change LocalOccurrence.child
                (compileRegion d hwf child).origin :: _ = _
            rw [compileRegion_origin]
            exact congrArg (List.cons _) tailResult.1
          · change (CompiledItem.cut
                (compileRegion d hwf child)).ValidAt origin ∧
              tailItems.ValidAt origin
            exact ⟨⟨by rw [compileRegion_origin]; exact shape,
              childrenValid child (by simp)⟩, tailResult.2⟩
      | bubble childParent arity =>
          have parentSame : childParent = origin := by
            rw [shape] at parentEq
            exact Option.some.inj parentEq
          subst childParent
          have foldedEq :
              (child :: tail).foldr
                (fun candidate rest =>
                  if _parentEq :
                      (d.regions candidate).parent? = some origin then
                    match d.regions candidate with
                    | .sheet => rest
                    | .cut _ => CompiledItems.cons
                        (CompiledItem.cut (compileRegion d hwf candidate)) rest
                    | .bubble _ arity => CompiledItems.cons
                        (CompiledItem.bubble arity
                          (compileRegion d hwf candidate)) rest
                  else rest) CompiledItems.nil =
                CompiledItems.cons
                  (CompiledItem.bubble arity (compileRegion d hwf child))
                  tailItems := by
            rw [List.foldr_cons, dif_pos parentEq, shape]
          rw [foldedEq]
          refine ⟨?_, ?_⟩
          · change LocalOccurrence.child
                (compileRegion d hwf child).origin :: _ = _
            rw [compileRegion_origin]
            exact congrArg (List.cons _) tailResult.1
          · change (CompiledItem.bubble arity
                (compileRegion d hwf child)).ValidAt origin ∧
              tailItems.ValidAt origin
            exact ⟨⟨by rw [compileRegion_origin]; exact shape,
              childrenValid child (by simp)⟩, tailResult.2⟩

theorem compileRegion_valid (d : Diagram) (hwf : d.WellFormed) :
    (origin : Fin d.regionCount) → (compileRegion d hwf origin).Valid
  | origin => by
      rw [compileRegion]
      let nodes := compileNodeItems d hwf origin
      let childFins := filterFin fun child =>
        decide ((d.regions child).parent? = some origin)
      have childDirect : ∀ child, child ∈ childFins →
          (d.regions child).parent? = some origin := by
        intro child member
        simpa [childFins] using member
      have childrenResult := compileChildFold_valid d hwf origin childFins
        childDirect (fun child member => compileRegion_valid d hwf child)
      change _ ∧ _ ∧ _ ∧ _
      exact ⟨nodes.origins_eq, childrenResult.1, nodes.valid,
        childrenResult.2⟩
termination_by origin => (descendantRegions d origin).length
decreasing_by
  all_goals exact descendantRegions_length_lt_of_parent hwf (childDirect child member)

theorem openRootWires_exact
    {d : OpenDiagram} (hwf : d.WellFormed) :
    WireContext.Exact d.rootWires d.diagram.root := by
  constructor
  · exact d.rootWires_nodup
  · intro wire
    rw [OpenDiagram.mem_rootWires_iff d hwf]
    constructor
    · intro hscope
      rw [hscope]
      exact Diagram.Encloses.refl d.diagram d.diagram.root
    · exact encloses_sheet_eq hwf.diagram_well_formed.root_is_sheet

theorem closedRootWires_exact (hwf : d.WellFormed) :
    WireContext.Exact
      (([] : WireContext d) ++ exactScopeWires d d.root) d.root := by
  simpa [WireContext.extend] using WireContext.root_exact hwf

end VisualProof.Concrete.Elaboration
