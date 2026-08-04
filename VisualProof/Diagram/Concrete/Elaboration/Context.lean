import VisualProof.Diagram.Concrete.Elaboration.Traversal
import VisualProof.Diagram.Core

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

/-! Proof-independent wire contexts.  List order is the intrinsic wire order. -/

abbrev WireContext (d : ConcreteDiagram) := List (Fin d.wireCount)

namespace WireContext

def lookup? (context : WireContext d) (wire : Fin d.wireCount) :
    Option (Fin context.length) :=
  indexOf? context wire

def extend (context : WireContext d) (region : Fin d.regionCount) :
    WireContext d :=
  context ++ exactScopeWires d region

def Covers (context : WireContext d) (region : Fin d.regionCount) : Prop :=
  forall wire : Fin d.wireCount,
    d.Encloses (d.wires wire).scope region -> wire ∈ context

structure Exact (context : WireContext d) (region : Fin d.regionCount) : Prop where
  nodup : context.Nodup
  mem_iff : forall wire : Fin d.wireCount,
    wire ∈ context ↔ d.Encloses (d.wires wire).scope region

theorem Exact.covers (hexact : Exact context region) : context.Covers region :=
  fun wire hencloses => (hexact.mem_iff wire).mpr hencloses

@[simp] theorem length_extend (context : WireContext d)
    (region : Fin d.regionCount) :
    (context.extend region).length =
      context.length + (exactScopeWires d region).length := by
  simp [extend]

theorem lookup?_sound {context : WireContext d} {wire : Fin d.wireCount}
    {index : Fin context.length} (h : context.lookup? wire = some index) :
    context[index] = wire :=
  indexOf?_sound h

theorem lookup?_complete {context : WireContext d} {wire : Fin d.wireCount}
    (h : wire ∈ context) : exists index, context.lookup? wire = some index :=
  indexOf?_complete h

theorem lookup?_unique {context : WireContext d} (hnodup : context.Nodup)
    {wire : Fin d.wireCount} {index : Fin context.length}
    (hindex : context.lookup? wire = some index)
    {other : Fin context.length} (hother : context[other] = wire) :
    other = index :=
  indexOf?_unique_of_nodup hnodup hindex hother

def outerIndex (context : WireContext d) (region : Fin d.regionCount)
    (index : Fin context.length) : Fin (context.extend region).length :=
  ⟨index.val, by rw [length_extend]; omega⟩

theorem extend_outer (context : WireContext d)
    (region : Fin d.regionCount) (index : Fin context.length) :
    (context.extend region)[context.outerIndex region index] = context[index] := by
  exact List.getElem_append_left index.isLt

theorem extend_local (context : WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (exactScopeWires d region).length) :
    (context.extend region)[Fin.natAdd context.length index] =
      (exactScopeWires d region)[index] := by
  simp [extend]

theorem exactScopeWires_disjoint {d : ConcreteDiagram}
    {first second : Fin d.regionCount} (hne : first ≠ second) :
    List.Pairwise (fun left right => left ≠ right)
      (exactScopeWires d first ++ exactScopeWires d second) := by
  rw [List.pairwise_append]
  refine ⟨exactScopeWires_nodup d first,
    exactScopeWires_nodup d second, ?_⟩
  intro left hleft right hright heq
  subst right
  have hfirst := (mem_exactScopeWires d first left).mp hleft
  have hsecond := (mem_exactScopeWires d second left).mp hright
  exact hne (hfirst.symm.trans hsecond)

theorem extend_nodup (context : WireContext d) (region : Fin d.regionCount)
    (hnodup : context.Nodup)
    (hfresh : forall wire, wire ∈ context -> (d.wires wire).scope ≠ region) :
    (context.extend region).Nodup := by
  rw [extend, List.nodup_append]
  refine ⟨hnodup, exactScopeWires_nodup d region, ?_⟩
  intro left hleft right hright heq
  subst right
  exact hfresh left hleft ((mem_exactScopeWires d region left).mp hright)

end WireContext

/-! Parent-step decomposition used by both lexical contexts. -/

theorem climb_add {d : ConcreteDiagram}
    {start middle finish : Fin d.regionCount} {first second : Nat}
    (hfirst : d.climb first start = some middle)
    (hsecond : d.climb second middle = some finish) :
    d.climb (first + second) start = some finish := by
  induction first generalizing start with
  | zero =>
      have heq : start = middle := Option.some.inj hfirst
      subst start
      simpa using hsecond
  | succ first ih =>
      cases hparent : (d.regions start).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hfirst
      | some parent =>
          have htail : d.climb first parent = some middle := by
            simpa [ConcreteDiagram.climb, hparent] using hfirst
          simpa [Nat.succ_add, ConcreteDiagram.climb, hparent] using
            ih htail

theorem checked_encloses_trans {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {ancestor middle descendant : Fin d.regionCount}
    (hfirst : d.Encloses ancestor middle)
    (hsecond : d.Encloses middle descendant) :
    d.Encloses ancestor descendant := by
  obtain ⟨first, hfirst⟩ := hfirst
  obtain ⟨second, hsecond⟩ := hsecond
  obtain ⟨rootSteps, hroot⟩ := hwf.all_regions_reach_root ancestor
  have hcomposed :
      d.climb (second.val + first.val) descendant = some ancestor :=
    climb_add hsecond hfirst
  have htoRoot :
      d.climb ((second.val + first.val) + rootSteps.val) descendant =
        some d.root :=
    climb_add hcomposed hroot
  have hbound := ParentTraversal.climb_to_root_steps_le_regionCount d
    hwf.root_is_sheet hwf.all_regions_reach_root htoRoot
  exact ⟨⟨second.val + first.val, by omega⟩, hcomposed⟩

/-- Every proper descendant lies below a unique-level direct child of the
chosen ancestor.  This is the parent-tree decomposition used when a partial
occurrence is reconstructed as a checked selection. -/
theorem exists_direct_child_enclosing {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {ancestor descendant : Fin d.regionCount}
    (hne : descendant ≠ ancestor)
    (hencloses : d.Encloses ancestor descendant) :
    ∃ child,
      (d.regions child).parent? = some ancestor ∧
        d.Encloses child descendant := by
  obtain ⟨steps, hclimb⟩ := hencloses
  rcases steps with ⟨steps, hbound⟩
  induction steps generalizing descendant with
  | zero =>
      have : descendant = ancestor := Option.some.inj hclimb
      exact False.elim (hne this)
  | succ steps ih =>
      cases hparent : (d.regions descendant).parent? with
      | none => simp [ConcreteDiagram.climb, hparent] at hclimb
      | some parent =>
          have htail : d.climb steps parent = some ancestor := by
            simpa [ConcreteDiagram.climb, hparent] using hclimb
          by_cases heq : parent = ancestor
          · subst parent
            exact ⟨descendant, hparent,
              ConcreteDiagram.Encloses.refl d descendant⟩
          · obtain ⟨child, hchild, hchildParent⟩ :=
              ih (descendant := parent) heq (by omega) htail
            have hparentDescendant : d.Encloses parent descendant := by
              refine ⟨⟨1, by have := descendant.isLt; omega⟩, ?_⟩
              simp [ConcreteDiagram.climb, hparent]
            exact ⟨child, hchild,
              checked_encloses_trans hwf hchildParent hparentDescendant⟩

/-- Enclosure in a checked parent tree is antisymmetric. -/
theorem checked_encloses_antisymm {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {first second : Fin d.regionCount}
    (hfirst : d.Encloses first second)
    (hsecond : d.Encloses second first) : first = second := by
  obtain ⟨firstSteps, hfirst⟩ := hfirst
  obtain ⟨secondSteps, hsecond⟩ := hsecond
  obtain ⟨rootSteps, hroot⟩ := hwf.all_regions_reach_root second
  have hcycle :
      d.climb (firstSteps.val + secondSteps.val + rootSteps.val) second =
        some d.root :=
    climb_add (climb_add hfirst hsecond) hroot
  have heq := ParentTraversal.climb_to_root_steps_unique d hwf.root_is_sheet
    hcycle hroot
  have hzero : firstSteps.val = 0 := by omega
  have : second = first := by
    simpa [hzero, ConcreteDiagram.climb] using hfirst
  exact this.symm

theorem checked_direct_child_not_encloses_parent
    {d : ConcreteDiagram} (hwf : d.WellFormed signature)
    {child parent : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    ¬ d.Encloses child parent := by
  intro hencloses
  obtain ⟨parentSteps, hparentRoot⟩ := hwf.all_regions_reach_root parent
  obtain ⟨cycleSteps, hcycle⟩ := hencloses
  have hchildParent : d.climb 1 child = some parent := by
    simp [ConcreteDiagram.climb, hparent]
  have hchildRoot : d.climb (1 + parentSteps.val) child = some d.root :=
    climb_add hchildParent hparentRoot
  have hcycleRoot :
      d.climb (cycleSteps.val + (1 + parentSteps.val)) parent = some d.root :=
    climb_add hcycle hchildRoot
  have heq := ParentTraversal.climb_to_root_steps_unique d hwf.root_is_sheet
    hcycleRoot hparentRoot
  omega

theorem encloses_direct_child {d : ConcreteDiagram}
    {ancestor child parent : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent)
    (hencloses : d.Encloses ancestor child) :
    ancestor = child ∨ d.Encloses ancestor parent := by
  obtain ⟨steps, hsteps⟩ := hencloses
  rcases steps with ⟨steps, hbound⟩
  cases steps with
  | zero =>
      left
      simpa [ConcreteDiagram.climb] using hsteps.symm
  | succ steps =>
      right
      refine ⟨⟨steps, by omega⟩, ?_⟩
      simpa [ConcreteDiagram.climb, hparent] using hsteps

theorem encloses_sheet_eq {d : ConcreteDiagram}
    {ancestor sheet : Fin d.regionCount}
    (hsheet : d.regions sheet = .sheet)
    (hencloses : d.Encloses ancestor sheet) : ancestor = sheet := by
  obtain ⟨steps, hsteps⟩ := hencloses
  rcases steps with ⟨steps, hbound⟩
  cases steps with
  | zero => simpa [ConcreteDiagram.climb] using hsteps.symm
  | succ steps => simp [ConcreteDiagram.climb, hsheet, CRegion.parent?] at hsteps

namespace WireContext

theorem root_exact {d : ConcreteDiagram} (hwf : d.WellFormed signature) :
    Exact (WireContext.extend ([] : WireContext d) d.root) d.root := by
  constructor
  · simpa [extend] using exactScopeWires_nodup d d.root
  · intro wire
    rw [show wire ∈ WireContext.extend ([] : WireContext d) d.root ↔
        (d.wires wire).scope = d.root by simp [extend]]
    constructor
    · intro hscope
      rw [hscope]
      exact ConcreteDiagram.Encloses.refl d d.root
    · exact encloses_sheet_eq hwf.root_is_sheet

theorem Exact.extend_child {d : ConcreteDiagram}
    {context : WireContext d} {parent : Fin d.regionCount}
    (hexact : Exact context parent)
    (hwf : d.WellFormed signature)
    {child : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    Exact (context.extend child) child := by
  have hparentEncloses : d.Encloses parent child := by
    have hpositive : 0 < d.regionCount :=
      Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
    refine ⟨⟨1, by omega⟩, ?_⟩
    change (match (d.regions child).parent? with
      | none => none
      | some directParent => d.climb 0 directParent) = some parent
    rw [hparent]
    rfl
  constructor
  · apply extend_nodup context child hexact.nodup
    intro wire hwire hscope
    have hscopeParent : d.Encloses (d.wires wire).scope parent :=
      (hexact.mem_iff wire).mp hwire
    rw [hscope] at hscopeParent
    exact checked_direct_child_not_encloses_parent hwf hparent hscopeParent
  · intro wire
    constructor
    · intro hwire
      rcases List.mem_append.mp hwire with houter | hlocal
      · exact checked_encloses_trans hwf
          ((hexact.mem_iff wire).mp houter) hparentEncloses
      · have hscope := (mem_exactScopeWires d child wire).mp hlocal
        rw [hscope]
        exact ConcreteDiagram.Encloses.refl d child
    · intro hencloses
      rcases encloses_direct_child hparent hencloses with hscope | houter
      · apply List.mem_append_right context
        exact (mem_exactScopeWires d child wire).mpr hscope
      · apply List.mem_append_left (exactScopeWires d child)
        exact (hexact.mem_iff wire).mpr houter

end WireContext

/-! Proof-independent binder contexts keyed by exact concrete bubble identity. -/

abbrev BinderContext (d : ConcreteDiagram) (rels : RelCtx) :=
  Fin d.regionCount -> Option (Sigma fun arity => RelVar rels arity)

namespace BinderContext

def empty : BinderContext d [] := fun _ => none

def liftVar (head : Nat) (relation : RelVar rels arity) :
    RelVar (head :: rels) arity where
  index := relation.index.succ
  hasArity := by simpa using relation.hasArity

def head (arity : Nat) : RelVar (arity :: rels) arity where
  index := 0
  hasArity := rfl

def push (context : BinderContext d rels)
    (binder : Fin d.regionCount) (arity : Nat) :
    BinderContext d (arity :: rels) :=
  fun candidate =>
    if candidate = binder then
      some ⟨arity, head arity⟩
    else
      (context candidate).map fun relation =>
        ⟨relation.1, liftVar arity relation.2⟩

def Covers (context : BinderContext d rels)
    (region : Fin d.regionCount) : Prop :=
  forall binder parent arity,
    d.regions binder = .bubble parent arity ->
    d.Encloses binder region ->
    exists relation : RelVar rels arity,
      context binder = some ⟨arity, relation⟩

@[simp] theorem push_self (context : BinderContext d rels)
    (binder : Fin d.regionCount) (arity : Nat) :
    context.push binder arity binder = some ⟨arity, head arity⟩ := by
  simp [push]

theorem push_other (context : BinderContext d rels)
    {binder candidate : Fin d.regionCount} (arity : Nat)
    (hne : candidate ≠ binder) :
    context.push binder arity candidate =
      (context candidate).map (fun relation =>
        ⟨relation.1, liftVar arity relation.2⟩) := by
  simp [push, hne]

theorem empty_covers_root {d : ConcreteDiagram} (hwf : d.WellFormed signature) :
    (empty : BinderContext d []).Covers d.root := by
  intro binder parent arity hbinder hencloses
  have heq : binder = d.root :=
    encloses_sheet_eq hwf.root_is_sheet hencloses
  subst binder
  rw [hwf.root_is_sheet] at hbinder
  contradiction

theorem covers_cut_child {context : BinderContext d rels}
    {child parent : Fin d.regionCount}
    (hcovers : context.Covers parent)
    (hchild : d.regions child = .cut parent) :
    context.Covers child := by
  intro binder binderParent arity hbinder hencloses
  have hparent : (d.regions child).parent? = some parent := by
    simp [hchild, CRegion.parent?]
  rcases encloses_direct_child hparent hencloses with heq | hancestor
  · subst binder
    rw [hchild] at hbinder
    contradiction
  · exact hcovers binder binderParent arity hbinder hancestor

theorem push_covers_bubble_child {context : BinderContext d rels}
    {child parent : Fin d.regionCount} {childArity : Nat}
    (hcovers : context.Covers parent)
    (hchild : d.regions child = .bubble parent childArity) :
    (context.push child childArity).Covers child := by
  intro binder binderParent arity hbinder hencloses
  have hparent : (d.regions child).parent? = some parent := by
    simp [hchild, CRegion.parent?]
  by_cases heq : binder = child
  · subst binder
    rw [hchild] at hbinder
    have harity : arity = childArity :=
      (CRegion.bubble.inj hbinder).2.symm
    subst arity
    exact ⟨head childArity, push_self context child childArity⟩
  · have hancestor : d.Encloses binder parent :=
      (encloses_direct_child hparent hencloses).resolve_left heq
    obtain ⟨relation, hrelation⟩ :=
      hcovers binder binderParent arity hbinder hancestor
    exact ⟨liftVar childArity relation, by
      rw [push_other context childArity heq, hrelation]
      rfl⟩

theorem checked_atom_binder_is_bubble {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {node : Fin d.nodeCount} {region binder : Fin d.regionCount}
    (hnode : d.nodes node = .atom region binder) :
    exists parent arity, d.regions binder = .bubble parent arity := by
  simpa [ConcreteDiagram.AtomBindersAreBubbles, hnode]
    using hwf.atom_binders_are_bubbles node

theorem checked_atom_binder_available {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {context : BinderContext d rels} {node : Fin d.nodeCount}
    {region binder parent : Fin d.regionCount} {arity : Nat}
    (hcovers : context.Covers region)
    (hnode : d.nodes node = .atom region binder)
    (hbinder : d.regions binder = .bubble parent arity) :
    exists relation : RelVar rels arity,
      context binder = some ⟨arity, relation⟩ := by
  apply hcovers binder parent arity hbinder
  simpa [ConcreteDiagram.AtomBindersEnclose, hnode]
    using hwf.atom_binders_enclose node

/-- Exact enumeration of the concrete bubbles represented by an intrinsic
relation context. It supplements coverage with the inverse direction needed
to transport a pattern's relation variables into a host lexical context. -/
structure Enumeration
    (diagram : ConcreteDiagram)
    (context : BinderContext diagram rels)
    (region : Fin diagram.regionCount) where
  binder : Fin rels.length → Fin diagram.regionCount
  binder_injective : Function.Injective binder
  bubble : ∀ index, ∃ parent,
    diagram.regions (binder index) =
      .bubble parent (rels.get index)
  encloses : ∀ index, diagram.Encloses (binder index) region
  lookup : ∀ index,
    context (binder index) = some ⟨rels.get index, {
      index := index
      hasArity := rfl
    }⟩
  lookup_owner : ∀ {candidate arity} (relation : RelVar rels arity),
    context candidate = some ⟨arity, relation⟩ →
      binder relation.index = candidate

def Enumeration.empty
    (diagram : ConcreteDiagram) :
    Enumeration diagram BinderContext.empty diagram.root where
  binder := nofun
  binder_injective := nofun
  bubble := nofun
  encloses := nofun
  lookup := nofun
  lookup_owner := by
    intro candidate arity relation hlookup
    simp [BinderContext.empty] at hlookup

def Enumeration.cutChild
    (enumeration : Enumeration diagram context parent)
    (hwf : diagram.WellFormed signature)
    (hchild : diagram.regions child = .cut parent) :
    Enumeration diagram context child where
  binder := enumeration.binder
  binder_injective := enumeration.binder_injective
  bubble := enumeration.bubble
  encloses := by
    intro index
    have parentChild : diagram.Encloses parent child := by
      refine ⟨⟨1, by
        have := child.isLt
        omega⟩, ?_⟩
      simp [ConcreteDiagram.climb, hchild, CRegion.parent?]
    exact checked_encloses_trans hwf
      (enumeration.encloses index) parentChild
  lookup := enumeration.lookup
  lookup_owner := enumeration.lookup_owner

def Enumeration.bubbleChild
    (enumeration : Enumeration diagram context parent)
    (hwf : diagram.WellFormed signature)
    (hchild : diagram.regions child = .bubble parent arity) :
    Enumeration diagram (context.push child arity) child where
  binder := Fin.cases child enumeration.binder
  binder_injective := by
    intro left right heq
    rcases Fin.eq_zero_or_eq_succ left with rfl | ⟨leftTail, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ right with rfl | ⟨rightTail, rfl⟩
      · rfl
      · simp only [Fin.cases_zero, Fin.cases_succ] at heq
        have hencloses := enumeration.encloses rightTail
        have parentEq : (diagram.regions child).parent? = some parent := by
          simp [hchild, CRegion.parent?]
        exact False.elim
          (checked_direct_child_not_encloses_parent
            hwf parentEq (by simpa [heq] using hencloses))
    · rcases Fin.eq_zero_or_eq_succ right with rfl | ⟨rightTail, rfl⟩
      · simp only [Fin.cases_zero, Fin.cases_succ] at heq
        have hencloses := enumeration.encloses leftTail
        have parentEq : (diagram.regions child).parent? = some parent := by
          simp [hchild, CRegion.parent?]
        exact False.elim
          (checked_direct_child_not_encloses_parent
            hwf parentEq (by simpa [← heq] using hencloses))
      · simp only [Fin.cases_succ] at heq
        exact congrArg Fin.succ (enumeration.binder_injective heq)
  bubble := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact ⟨parent, by simpa using hchild⟩
    · simpa using enumeration.bubble tail
  encloses := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact ConcreteDiagram.Encloses.refl diagram child
    · have parentChild : diagram.Encloses parent child := by
        refine ⟨⟨1, by
          have := child.isLt
          omega⟩, ?_⟩
        simp [ConcreteDiagram.climb, hchild, CRegion.parent?]
      exact checked_encloses_trans hwf
        (enumeration.encloses tail) parentChild
  lookup := by
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact BinderContext.push_self context child arity
    · have childNe : enumeration.binder tail ≠ child := by
        intro heq
        have hencloses := enumeration.encloses tail
        have parentEq : (diagram.regions child).parent? = some parent := by
          simp [hchild, CRegion.parent?]
        exact checked_direct_child_not_encloses_parent
          hwf parentEq (by simpa [heq] using hencloses)
      change context.push child arity (enumeration.binder tail) = _
      rw [BinderContext.push_other context arity childNe, enumeration.lookup]
      rfl
  lookup_owner := by
    intro candidate relationArity relation hlookup
    rcases relation with ⟨index, hasArity⟩
    revert hasArity
    refine Fin.cases ?_ (fun tail => ?_) index
    · intro hasArity hlookup
      have harity : relationArity = arity := by simpa using hasArity.symm
      subst relationArity
      by_cases heq : candidate = child
      · subst candidate
        rfl
      · rw [BinderContext.push_other context arity heq] at hlookup
        cases hcandidate : context candidate with
        | none => simp [hcandidate] at hlookup
        | some previous =>
            have hindexValue := congrArg
              (fun value => value.map fun relation => relation.2.index.val)
              hlookup
            simp [hcandidate, BinderContext.liftVar] at hindexValue
    · intro hasArity hlookup
      have hcandidateNe : candidate ≠ child := by
        intro heq
        subst candidate
        rw [BinderContext.push_self] at hlookup
        have hindexValue := congrArg
          (fun value => value.map fun relation => relation.2.index.val)
          hlookup
        simp [BinderContext.head] at hindexValue
      rw [BinderContext.push_other context arity hcandidateNe] at hlookup
      cases hcandidate : context candidate with
      | none => simp [hcandidate] at hlookup
      | some previous =>
          cases previous with
          | mk previousArity previousRelation =>
              have hprevious : context candidate =
                  some ⟨previousArity, previousRelation⟩ := hcandidate
              have hindex : previousRelation.index = tail := by
                have hindexValue := congrArg
                  (fun value => value.map fun relation => relation.2.index.val)
                  hlookup
                simp [hcandidate, BinderContext.liftVar] at hindexValue
                apply Fin.ext
                omega
              have howner := enumeration.lookup_owner previousRelation hprevious
              simpa only [Fin.cases_succ, hindex] using howner

/-- The concrete binder represented by each lexical relation position is
independent of the retained proof of enumeration. -/
theorem Enumeration.binder_unique
    {diagram : ConcreteDiagram} {rels : RelCtx}
    {context : BinderContext diagram rels}
    {region : Fin diagram.regionCount}
    (first second : Enumeration diagram context region) :
    first.binder = second.binder := by
  funext index
  let relation : RelVar rels (rels.get index) := ⟨index, rfl⟩
  exact (second.lookup_owner relation (first.lookup index)).symm

end BinderContext

/-! The unique concrete wire owning an endpoint, before lexical resolution. -/

def endpointOwner? (d : ConcreteDiagram)
    (endpoint : CEndpoint d.nodeCount) : Option (Fin d.wireCount) :=
  (filterFin fun wire => decide (d.EndpointOccurs wire endpoint)).head?

theorem endpointOwner?_sound {d : ConcreteDiagram}
    {endpoint : CEndpoint d.nodeCount} {wire : Fin d.wireCount}
    (h : endpointOwner? d endpoint = some wire) :
    d.EndpointOccurs wire endpoint := by
  unfold endpointOwner? at h
  generalize hs : filterFin
      (fun candidate => decide (d.EndpointOccurs candidate endpoint)) = owners at h
  cases owners with
  | nil => simp at h
  | cons head tail =>
      simp at h
      subst wire
      have hmem : head ∈ filterFin
          (fun candidate => decide (d.EndpointOccurs candidate endpoint)) := by
        rw [hs]
        simp
      simpa using hmem

theorem endpointOwner?_complete {d : ConcreteDiagram}
    {endpoint : CEndpoint d.nodeCount} {wire : Fin d.wireCount}
    (h : d.EndpointOccurs wire endpoint) :
    exists owner, endpointOwner? d endpoint = some owner := by
  have hmem : wire ∈ filterFin
      (fun candidate => decide (d.EndpointOccurs candidate endpoint)) := by
    simpa using h
  unfold endpointOwner?
  generalize hs : filterFin
      (fun candidate => decide (d.EndpointOccurs candidate endpoint)) = owners at hmem
  cases owners with
  | nil => simp at hmem
  | cons head tail => exact ⟨head, rfl⟩

theorem endpoint_wire_unique {d : ConcreteDiagram}
    (hdisjoint : d.WireEndpointsAreDisjoint)
    {endpoint : CEndpoint d.nodeCount} {first second : Fin d.wireCount}
    (hfirst : d.EndpointOccurs first endpoint)
    (hsecond : d.EndpointOccurs second endpoint) : first = second := by
  by_cases heq : first = second
  · exact heq
  · have hnotBool :=
      hdisjoint first second (bne_iff_ne.mpr heq) endpoint hfirst
    have hfalse : decide (d.EndpointOccurs second endpoint) = false := by
      cases hdecision : decide (d.EndpointOccurs second endpoint) <;>
        simp [hdecision] at hnotBool ⊢
    exact False.elim ((decide_eq_false_iff_not.mp hfalse) hsecond)

theorem endpointOwner?_unique {d : ConcreteDiagram}
    (hdisjoint : d.WireEndpointsAreDisjoint)
    {endpoint : CEndpoint d.nodeCount} {owner wire : Fin d.wireCount}
    (howner : endpointOwner? d endpoint = some owner)
    (hwire : d.EndpointOccurs wire endpoint) : wire = owner :=
  endpoint_wire_unique hdisjoint hwire (endpointOwner?_sound howner)

/-! Port resolution first finds its concrete owner and then its lexical index. -/

def resolvePort? (d : ConcreteDiagram) (context : WireContext d)
    (node : Fin d.nodeCount) (port : CPort) :
    Option (Fin context.length) := do
  let wire <- endpointOwner? d ⟨node, port⟩
  context.lookup? wire

def resolvePorts? (d : ConcreteDiagram) (context : WireContext d)
    (node : Fin d.nodeCount) (arity : Nat)
    (port : Fin arity -> CPort := fun index => .arg index) :
    Option (Fin arity -> Fin context.length) :=
  sequenceFin fun index => resolvePort? d context node (port index)

theorem resolvePort?_sound {context : WireContext d}
    {node : Fin d.nodeCount} {port : CPort}
    {index : Fin context.length}
    (h : resolvePort? d context node port = some index) :
    exists wire : Fin d.wireCount,
      d.EndpointOccurs wire ⟨node, port⟩ /\ context[index] = wire := by
  unfold resolvePort? at h
  cases howner : endpointOwner? d ⟨node, port⟩ with
  | none => simp [howner] at h
  | some wire =>
      simp [howner] at h
      exact ⟨wire, endpointOwner?_sound howner, WireContext.lookup?_sound h⟩

theorem resolvePort?_complete {context : WireContext d}
    (hcovers : context.Covers region)
    (hscopes : d.WireScopesEnclose)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region)
    {port : CPort} (hcovered : exists wire, d.EndpointOccurs wire ⟨node, port⟩) :
    exists index, resolvePort? d context node port = some index := by
  obtain ⟨wire, hwire⟩ := hcovered
  obtain ⟨owner, howner⟩ := endpointOwner?_complete hwire
  have hownerOccurs := endpointOwner?_sound howner
  have hencloses := hscopes owner ⟨node, port⟩ hownerOccurs
  rw [hregion] at hencloses
  obtain ⟨index, hindex⟩ := context.lookup?_complete (hcovers owner hencloses)
  exact ⟨index, by simp [resolvePort?, howner, hindex]⟩

theorem required_port_is_covered {d : ConcreteDiagram}
    (hcovered : d.RequiredPortsAreCovered)
    {node : Fin d.nodeCount} {port : CPort}
    (hrequired : d.RequiresPort node port) :
    exists wire, d.EndpointOccurs wire ⟨node, port⟩ := by
  specialize hcovered node
  cases hnode : d.nodes node with
  | term region freePorts term =>
      simp only [hnode] at hcovered
      rw [ConcreteDiagram.requiresPort_term_iff d node port region freePorts term hnode]
        at hrequired
      rcases hrequired with rfl | ⟨index, rfl⟩
      · exact hcovered.1
      · exact hcovered.2 index
  | atom region binder =>
      cases hbinder : d.regions binder with
      | sheet => simp [ConcreteDiagram.RequiresPort, hnode, hbinder] at hrequired
      | cut parent => simp [ConcreteDiagram.RequiresPort, hnode, hbinder] at hrequired
      | bubble parent arity =>
          simp only [hnode, hbinder] at hcovered
          rw [ConcreteDiagram.requiresPort_atom_bubble_iff d node port region binder
            parent arity hnode hbinder] at hrequired
          obtain ⟨index, rfl⟩ := hrequired
          exact hcovered index
  | named region definition arity =>
      simp only [hnode] at hcovered
      rw [ConcreteDiagram.requiresPort_named_iff d node port region definition arity hnode]
        at hrequired
      obtain ⟨index, rfl⟩ := hrequired
      exact hcovered index

theorem checked_resolvePort?_complete (hwf : d.WellFormed signature)
    {context : WireContext d} {region : Fin d.regionCount}
    (hcovers : context.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region)
    {port : CPort} (hrequired : d.RequiresPort node port) :
    exists index, resolvePort? d context node port = some index :=
  resolvePort?_complete hcovers hwf.wire_scopes_enclose hregion
    (required_port_is_covered hwf.required_ports_are_covered hrequired)

theorem checked_resolvePorts?_complete (hwf : d.WellFormed signature)
    {context : WireContext d} {region : Fin d.regionCount}
    (hcovers : context.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region)
    (arity : Nat) (port : Fin arity -> CPort)
    (hrequired : forall index, d.RequiresPort node (port index)) :
    exists result, resolvePorts? d context node arity port = some result := by
  apply Option.isSome_iff_exists.mp
  unfold resolvePorts?
  rw [sequenceFin_isSome_iff]
  intro index
  exact checked_resolvePort?_complete hwf hcovers hregion (hrequired index)

/-! Exact signature-index resolution. -/

def namedRel? (signature : List Nat) (definition arity : Nat) :
    Option (NamedRel signature arity) :=
  if hdefinition : definition < signature.length then
    if harity : signature.get ⟨definition, hdefinition⟩ = arity then
      some ⟨⟨definition, hdefinition⟩, harity⟩
    else none
  else none

theorem namedRel?_sound {signature : List Nat} {definition arity : Nat}
    {relation : NamedRel signature arity}
    (h : namedRel? signature definition arity = some relation) :
    relation.index.val = definition /\ signature[definition]? = some arity := by
  unfold namedRel? at h
  split at h
  · rename_i hdefinition
    split at h
    · rename_i harity
      cases h
      constructor
      · rfl
      · apply List.getElem?_eq_some_iff.mpr
        exact ⟨hdefinition, by simpa [List.get_eq_getElem] using harity⟩
    · simp at h
  · simp at h

theorem namedRel?_complete {signature : List Nat} {definition arity : Nat}
    (h : signature[definition]? = some arity) :
    exists relation, namedRel? signature definition arity = some relation := by
  obtain ⟨hdefinition, hvalue⟩ := List.getElem?_eq_some_iff.mp h
  have harity : signature.get ⟨definition, hdefinition⟩ = arity := by
    simpa [List.get_eq_getElem] using hvalue
  unfold namedRel?
  rw [dif_pos hdefinition, dif_pos harity]
  exact ⟨_, rfl⟩

theorem checked_namedRel?_complete {d : ConcreteDiagram}
    (hwf : d.WellFormed signature)
    {node : Fin d.nodeCount} {region : Fin d.regionCount}
    {definition arity : Nat}
    (hnode : d.nodes node = .named region definition arity) :
    exists relation, namedRel? signature definition arity = some relation := by
  apply namedRel?_complete
  simpa [ConcreteDiagram.NamedReferencesResolve, hnode]
    using hwf.named_references_resolve node

end VisualProof.Diagram.ConcreteElaboration
