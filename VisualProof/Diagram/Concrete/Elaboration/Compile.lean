import VisualProof.Diagram.Concrete.Elaboration.Context
import VisualProof.Diagram.Concrete.Examples

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

private def compileNode? (signature : List Nat) (d : ConcreteDiagram)
    (context : WireContext d) (binders : BinderContext d rels)
    (node : Fin d.nodeCount) : Option (Item signature context.length rels) :=
  match d.nodes node with
  | .term _ freePorts term => do
      let output <- resolvePort? d context node .output
      let free <- resolvePorts? d context node freePorts (fun index => .free index)
      pure (.equation output (term.mapFree free))
  | .atom _ binder => do
      let relation <- binders binder
      let arguments <- resolvePorts? d context node relation.1
      pure (.atom relation.2 arguments)
  | .named _ definition arity => do
      let relation <- namedRel? signature definition arity
      let arguments <- resolvePorts? d context node arity
      pure (.named relation arguments)

private def compileOccurrenceWith?
    (signature : List Nat) (d : ConcreteDiagram)
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount) :
    Option (Item signature context.length rels) :=
  match occurrence with
  | .node node => compileNode? signature d context binders node
  | .child child =>
      match d.regions child with
      | .sheet => none
      | .cut _ => return .cut (← recurse child context binders)
      | .bubble _ arity =>
          return .bubble arity
            (← recurse child context (binders.push child arity))

private def compileOccurrencesWith?
    (signature : List Nat) (d : ConcreteDiagram)
    (recurse : forall {rels : RelCtx},
      (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels))
    (context : WireContext d) (binders : BinderContext d rels) :
    List (LocalOccurrence d.regionCount d.nodeCount) ->
      Option (ItemSeq signature context.length rels)
  | [] => some .nil
  | occurrence :: tail => do
      let item <- compileOccurrenceWith? signature d recurse context binders occurrence
      let rest <- compileOccurrencesWith? signature d recurse context binders tail
      pure (.cons item rest)

private def finishRegion (d : ConcreteDiagram)
    (context : WireContext d) (region : Fin d.regionCount)
    (items : ItemSeq signature (context.extend region).length rels) :
    Region signature context.length rels := by
  rw [WireContext.length_extend] at items
  exact .mk (exactScopeWires d region).length items

private def compileRegion? (signature : List Nat) (d : ConcreteDiagram) :
    Nat -> (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels)
  | 0, _, _, _ => none
  | fuel + 1, region, context, binders => do
      let extended := context.extend region
      let items <- compileOccurrencesWith? signature d
        (compileRegion? signature d fuel) extended binders
        (localOccurrences d region)
      pure (finishRegion d context region items)

private theorem compileNode?_complete
    (hwf : d.WellFormed signature)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (hwires : context.Covers region) (hbinders : binders.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region) :
    exists item, compileNode? signature d context binders node = some item := by
  cases hnode : d.nodes node with
  | term nodeRegion freePorts term =>
      obtain ⟨output, houtput⟩ := checked_resolvePort?_complete hwf hwires
        (node := node) hregion (port := .output) (by
          simp [ConcreteDiagram.RequiresPort, hnode])
      obtain ⟨free, hfree⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion freePorts (fun index => .free index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.equation output (term.mapFree free), by
        simp [compileNode?, hnode, houtput, hfree]⟩
  | atom nodeRegion binder =>
      have hnodeRegion : nodeRegion = region := by simpa [hnode] using hregion
      subst nodeRegion
      obtain ⟨parent, arity, hbubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf hnode
      obtain ⟨relation, hrelation⟩ :=
        BinderContext.checked_atom_binder_available hwf hbinders hnode hbubble
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode, hbubble]
          exact ⟨index, rfl⟩)
      exact ⟨Item.atom relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩
  | named nodeRegion definition arity =>
      obtain ⟨relation, hrelation⟩ := checked_namedRel?_complete hwf hnode
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.named relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩

private theorem child_depth
    {d : ConcreteDiagram} {child parent : Fin d.regionCount} {depth : Nat}
    (hparent : (d.regions child).parent? = some parent)
    (hdepth : d.climb depth parent = some d.root) :
    d.climb (depth + 1) child = some d.root := by
  change d.climb (Nat.succ depth) child = some d.root
  simpa [ConcreteDiagram.climb, hparent] using hdepth

private theorem compileRegion?_complete
    (hwf : d.WellFormed signature)
    {fuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + fuel = d.regionCount + 1)
    (hwires : (context.extend region).Exact region)
    (hbinders : binders.Covers region) :
    exists body, compileRegion? signature d fuel region context binders = some body := by
  induction fuel generalizing depth region context rels with
  | zero =>
      have hpositive : 0 < d.regionCount + 1 - depth := by
        have hle := ParentTraversal.climb_to_root_steps_le_regionCount d
          hwf.root_is_sheet hwf.all_regions_reach_root hdepth
        omega
      exfalso
      omega
  | succ fuel ih =>
      let extended := context.extend region
      have hextended : extended.Exact region := by simpa [extended] using hwires
      have hoccurrence : forall occurrence,
          occurrence ∈ localOccurrences d region ->
          exists item,
            compileOccurrenceWith? signature d
              (compileRegion? signature d fuel) extended binders occurrence =
                some item := by
        intro occurrence hmem
        cases occurrence with
        | node node =>
            have hnodeRegion :=
              (mem_localOccurrences_node d region node).mp hmem
            simpa [compileOccurrenceWith?] using
              compileNode?_complete hwf hextended.covers hbinders hnodeRegion
        | child child =>
            have hparent :=
              (mem_localOccurrences_child d region child).mp hmem
            cases hchild : d.regions child with
            | sheet =>
                have hchildRoot : child = d.root :=
                  hwf.only_root_is_sheet child hchild
                subst child
                rw [hwf.root_is_sheet] at hparent
                simp [CRegion.parent?] at hparent
            | cut parent =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.covers_cut_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.cut body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
            | bubble parent arity =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.push_covers_bubble_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.bubble arity body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
      have hoccurrences : exists items,
          compileOccurrencesWith? signature d (compileRegion? signature d fuel)
            extended binders (localOccurrences d region) = some items := by
        have go : forall occurrences :
            List (LocalOccurrence d.regionCount d.nodeCount),
            (forall occurrence, occurrence ∈ occurrences ->
              exists item,
                compileOccurrenceWith? signature d
                    (compileRegion? signature d fuel) extended binders occurrence =
                  some item) ->
            exists items,
              compileOccurrencesWith? signature d (compileRegion? signature d fuel)
                extended binders occurrences = some items := by
          intro occurrences
          induction occurrences with
          | nil => intro _; exact ⟨.nil, rfl⟩
          | cons occurrence tail ihTail =>
              intro hsuccess
              obtain ⟨item, hitem⟩ := hsuccess occurrence (by simp)
              obtain ⟨rest, hrest⟩ := ihTail (by
                intro candidate hcandidate
                exact hsuccess candidate (by simp [hcandidate]))
              exact ⟨.cons item rest, by
                simp [compileOccurrencesWith?, hitem, hrest]⟩
        exact go _ hoccurrence
      obtain ⟨items, hitems⟩ := hoccurrences
      refine ⟨finishRegion d context region items, ?_⟩
      simp only [compileRegion?]
      change (compileOccurrencesWith? signature d (compileRegion? signature d fuel)
        extended binders (localOccurrences d region)).bind
          (fun result => some (finishRegion d context region result)) =
        some (finishRegion d context region items)
      rw [hitems]
      rfl

private theorem compileRoot?_complete (checked : CheckedDiagram signature) :
    exists body,
      compileRegion? signature checked.val (checked.val.regionCount + 1)
        checked.val.root ([] : WireContext checked.val)
        BinderContext.empty = some body := by
  apply compileRegion?_complete checked.property
    (depth := 0) (region := checked.val.root)
  · exact checked.val.climb_zero checked.val.root
  · omega
  · exact WireContext.root_exact checked.property
  · exact BinderContext.empty_covers_root checked.property

end VisualProof.Diagram.ConcreteElaboration

namespace VisualProof.Diagram

open ConcreteElaboration
open VisualProof.Theory

namespace CheckedDiagram

def elaborate (checked : CheckedDiagram signature) : Region signature 0 [] :=
  (compileRegion? signature checked.val (checked.val.regionCount + 1)
    checked.val.root ([] : WireContext checked.val) BinderContext.empty).get
      (Option.isSome_iff_exists.mpr (compileRoot?_complete checked))

private theorem elaborate_computation (checked : CheckedDiagram signature) :
    exists body,
      compileRegion? signature checked.val (checked.val.regionCount + 1)
          checked.val.root ([] : WireContext checked.val) BinderContext.empty =
        some body /\ checked.elaborate = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete checked
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end CheckedDiagram

namespace ConcreteDiagram

def elaborate (d : ConcreteDiagram) (hwf : d.WellFormed signature) :
    Region signature 0 [] :=
  CheckedDiagram.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : ConcreteDiagram)
    (first second : d.WellFormed signature) :
    d.elaborate first = d.elaborate second := by
  rfl

private theorem elaborate_computation (d : ConcreteDiagram)
    (hwf : d.WellFormed signature) :
    exists body,
      compileRegion? signature d (d.regionCount + 1) d.root
          ([] : WireContext d) BinderContext.empty = some body /\
        d.elaborate hwf = body :=
  CheckedDiagram.elaborate_computation ⟨d, hwf⟩

end ConcreteDiagram

namespace ConcreteExamples

def validNestedChecked : CheckedDiagram [] :=
  ⟨validNested, checkWellFormed_iff.mp validNested_check⟩

def bareWireChecked : CheckedDiagram [] :=
  ⟨bareWire, checkWellFormed_iff.mp bareWire_check⟩

def unaryHead : RelVar [1] 1 where
  index := 0
  hasArity := rfl

def validNestedIntrinsic : Region [] 0 [] :=
  .mk 0 (.cons
    (.bubble 1 (.mk 1 (.cons
      (.cut (.mk 0 (.cons
        (.equation 0 (.lam (.bvar 0)))
        (.cons (.atom unaryHead (Fin.cases 0 Fin.elim0)) .nil))))
      .nil)))
    .nil)

theorem validNested_elaborate :
    validNestedChecked.elaborate = validNestedIntrinsic := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedDiagram.elaborate_computation validNestedChecked
  have hbody : body = validNestedIntrinsic := by
    have hkernel' := hkernel
    simp only [validNestedChecked] at hkernel'
    change some validNestedIntrinsic = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact helaborate.trans hbody

theorem bareWire_elaborate :
    bareWireChecked.elaborate = bareLocalWireExample := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedDiagram.elaborate_computation bareWireChecked
  have hbody : body = bareLocalWireExample := by
    have hkernel' := hkernel
    simp only [bareWireChecked] at hkernel'
    change some bareLocalWireExample = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact helaborate.trans hbody

end ConcreteExamples

end VisualProof.Diagram
