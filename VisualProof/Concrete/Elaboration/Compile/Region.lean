import VisualProof.Concrete.Elaboration.Compile.Kernel

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

private def compileOccurrenceZero? (d : Diagram)
    (context : WireContext d) (binders : BinderContext d rels) :
    LocalOccurrence d.regionCount d.nodeCount →
      Option (CompiledItem d 0 context rels binders)
  | .node node => compileNode? d 0 context binders node
  | .child _ => none

private def compileItemsZero? (d : Diagram)
    (context : WireContext d) (binders : BinderContext d rels) :
    List (LocalOccurrence d.regionCount d.nodeCount) →
      Option (CompiledItems d 0 context rels binders)
  | [] => some .nil
  | occurrence :: tail => do
      let head ← compileOccurrenceZero? d context binders occurrence
      let rest ← compileItemsZero? d context binders tail
      pure (.cons head rest)

private def compileOccurrenceSuccWith? (d : Diagram)
    (childFuel : Nat)
    (recurse : ∀ {nestedRels : RelCtx},
      (origin : Fin d.regionCount) → (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d
        (.nested childFuel origin context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels) :
    LocalOccurrence d.regionCount d.nodeCount →
      Option (CompiledItem d (childFuel + 1) context rels binders)
  | .node node => compileNode? d (childFuel + 1) context binders node
  | .child child =>
      match d.regions child with
      | .sheet => none
      | .cut _ => do
          let body ← recurse child context binders
          pure (.cut body)
      | .bubble _ arity => do
          let body ← recurse child context (binders.push child arity)
          pure (.bubble arity body)

private def compileItemsSuccWith? (d : Diagram)
    (childFuel : Nat)
    (recurse : ∀ {nestedRels : RelCtx},
      (origin : Fin d.regionCount) → (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d
        (.nested childFuel origin context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels) :
    List (LocalOccurrence d.regionCount d.nodeCount) →
      Option (CompiledItems d (childFuel + 1) context rels binders)
  | [] => some .nil
  | occurrence :: tail => do
      let head ← compileOccurrenceSuccWith? d childFuel recurse
        context binders occurrence
      let rest ← compileItemsSuccWith? d childFuel recurse
        context binders tail
      pure (.cons head rest)

/-- Compile the body of an actual successor-fuel nested call. The argument is
the predecessor fuel stored in the call signature. -/
def compileRegion? (d : Diagram) :
    (childFuel : Nat) → (origin : Fin d.regionCount) →
      (context : WireContext d) → (binders : BinderContext d rels) →
      Option (CompiledRegion d
        (.nested childFuel origin context rels binders))
  | 0, origin, context, binders => do
      let items ← compileItemsZero? d (context.extend origin) binders
        (localOccurrences d origin)
      pure (.mk items)
  | childFuel + 1, origin, context, binders => do
      let items ← compileItemsSuccWith? d childFuel
        (compileRegion? d childFuel) (context.extend origin) binders
        (localOccurrences d origin)
      pure (.mk items)

/-- Compile one occurrence with the fixed fuel-recursive region compiler. -/
def compileOccurrence? (d : Diagram) :
    (fuel : Nat) → (context : WireContext d) →
      (binders : BinderContext d rels) →
      LocalOccurrence d.regionCount d.nodeCount →
      Option (CompiledItem d fuel context rels binders)
  | 0, context, binders, occurrence =>
      compileOccurrenceZero? d context binders occurrence
  | childFuel + 1, context, binders, occurrence =>
      compileOccurrenceSuccWith? d childFuel (compileRegion? d childFuel)
        context binders occurrence

/-- Compile an ordinary ordered occurrence list. Recursive region compilation
is fixed internally and cannot be supplied by callers. -/
def compileItems? (d : Diagram) :
    (fuel : Nat) → (context : WireContext d) →
      (binders : BinderContext d rels) →
      List (LocalOccurrence d.regionCount d.nodeCount) →
      Option (CompiledItems d fuel context rels binders)
  | 0, context, binders, occurrences =>
      compileItemsZero? d context binders occurrences
  | childFuel + 1, context, binders, occurrences =>
      compileItemsSuccWith? d childFuel (compileRegion? d childFuel)
        context binders occurrences

/-- Compile the actual root call directly into the sole root-indexed result. -/
def compileRoot? (d : Diagram) (ambient locals : WireContext d) :
    Option (CompiledRegion d (.root ambient locals)) := do
  let items ← compileItems? d d.regionCount (ambient ++ locals)
    BinderContext.empty (localOccurrences d d.root)
  pure (.mk items)

/-- Run the sole compiler at the exact root or nested call described by its
signature. -/
def CompilerCall.compile? : (call : CompilerCall d) →
    Option (CompiledRegion d call)
  | .root ambient locals => compileRoot? d ambient locals
  | .nested childFuel origin context _ binders =>
      compileRegion? d childFuel origin context binders

@[simp] theorem CompilerCall.compile?_root
    (ambient locals : WireContext d) :
    (CompilerCall.root ambient locals).compile? =
      compileRoot? d ambient locals := rfl

@[simp] theorem CompilerCall.compile?_nested
    {rels : RelCtx}
    (childFuel : Nat) (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels) :
    (CompilerCall.nested childFuel origin context rels binders).compile? =
      compileRegion? d childFuel origin context binders := rfl

@[simp] theorem compileOccurrence?_node
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (node : Fin d.nodeCount) :
    compileOccurrence? d fuel context binders (.node node) =
      compileNode? d fuel context binders node := by
  cases fuel <;> rfl

@[simp] theorem compileOccurrence?_child_zero
    (d : Diagram) (context : WireContext d)
    (binders : BinderContext d rels) (child : Fin d.regionCount) :
    compileOccurrence? d 0 context binders (.child child) = none := by
  rfl

theorem compileOccurrence?_child_succ_sheet
    (d : Diagram) (childFuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child : Fin d.regionCount)
    (hchild : d.regions child = .sheet) :
    compileOccurrence? d (childFuel + 1) context binders (.child child) =
      none := by
  simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild]

theorem compileOccurrence?_child_succ_cut
    (d : Diagram) (childFuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child parent : Fin d.regionCount)
    (hchild : d.regions child = .cut parent) :
    compileOccurrence? d (childFuel + 1) context binders (.child child) =
      (do
        let body ← compileRegion? d childFuel child context binders
        pure (.cut body)) := by
  simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild]

theorem compileOccurrence?_child_succ_bubble
    (d : Diagram) (childFuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child parent : Fin d.regionCount)
    (arity : Nat) (hchild : d.regions child = .bubble parent arity) :
    compileOccurrence? d (childFuel + 1) context binders (.child child) =
      (do
        let body ← compileRegion? d childFuel child context
          (binders.push child arity)
        pure (.bubble arity body)) := by
  simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild]

noncomputable def compileOccurrence?_child_cut_inv
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child parent : Fin d.regionCount)
    (hchild : d.regions child = .cut parent)
    {item : CompiledItem d fuel context rels binders}
    (compiled : compileOccurrence? d fuel context binders (.child child) =
      some item) :
    PSigma fun childFuel => PSigma fun body =>
      fuel = childFuel + 1 ∧
        compileRegion? d childFuel child context binders = some body ∧
        item.erase = Item.cut body.erase := by
  cases fuel with
  | zero => simp at compiled
  | succ childFuel =>
      rw [compileOccurrence?_child_succ_cut _ _ _ _ _ _ hchild] at compiled
      cases hbody : compileRegion? d childFuel child context binders with
      | none => simp [hbody] at compiled
      | some body =>
          simp [hbody] at compiled
          subst item
          exact ⟨childFuel, body, rfl, hbody, rfl⟩

/-- An exact cut result exposes the recursive compiler equation for its body. -/
theorem compileOccurrence?_child_cut_body
    {childFuel : Nat} {child : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    {body : CompiledRegion d
      (.nested childFuel child context rels binders)}
    (compiled : compileOccurrence? d (childFuel + 1) context binders
      (.child child) = some (.cut body)) :
    compileRegion? d childFuel child context binders = some body := by
  cases hregion : d.regions child with
  | sheet =>
      rw [compileOccurrence?_child_succ_sheet _ _ _ _ _ hregion] at compiled
      contradiction
  | cut parent =>
      rw [compileOccurrence?_child_succ_cut _ _ _ _ _ _ hregion] at compiled
      cases hbody : compileRegion? d childFuel child context binders with
      | none => simp [hbody] at compiled
      | some result =>
          simp [hbody] at compiled
          subst result
          rfl
  | bubble parent arity =>
      rw [compileOccurrence?_child_succ_bubble _ _ _ _ _ _ _ hregion]
        at compiled
      cases hbody : compileRegion? d childFuel child context
          (binders.push child arity) with
      | none => simp [hbody] at compiled
      | some result => simp [hbody] at compiled

theorem compileOccurrence?_child_sheet_false
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child : Fin d.regionCount)
    (hchild : d.regions child = .sheet)
    {item : CompiledItem d fuel context rels binders}
    (compiled : compileOccurrence? d fuel context binders (.child child) =
      some item) : False := by
  cases fuel with
  | zero => simp at compiled
  | succ childFuel =>
      rw [compileOccurrence?_child_succ_sheet _ _ _ _ _ hchild] at compiled
      contradiction

noncomputable def compileOccurrence?_child_bubble_inv
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) (child parent : Fin d.regionCount)
    (arity : Nat) (hchild : d.regions child = .bubble parent arity)
    {item : CompiledItem d fuel context rels binders}
    (compiled : compileOccurrence? d fuel context binders (.child child) =
      some item) :
    PSigma fun childFuel => PSigma fun body =>
      fuel = childFuel + 1 ∧
        compileRegion? d childFuel child context (binders.push child arity) =
          some body ∧
        item.erase = Item.bubble arity body.erase := by
  cases fuel with
  | zero => simp at compiled
  | succ childFuel =>
      rw [compileOccurrence?_child_succ_bubble _ _ _ _ _ _ _ hchild]
        at compiled
      cases hbody : compileRegion? d childFuel child context
          (binders.push child arity) with
      | none => simp [hbody] at compiled
      | some body =>
          simp [hbody] at compiled
          subst item
          exact ⟨childFuel, body, rfl, hbody, rfl⟩

/-- An exact bubble result exposes the recursive compiler equation for its
body. -/
theorem compileOccurrence?_child_bubble_body
    {childFuel arity : Nat} {child : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    {body : CompiledRegion d
      (.nested childFuel child context (arity :: rels)
        (binders.push child arity))}
    (compiled : compileOccurrence? d (childFuel + 1) context binders
      (.child child) = some (.bubble arity body)) :
    compileRegion? d childFuel child context (binders.push child arity) =
      some body := by
  cases hregion : d.regions child with
  | sheet =>
      rw [compileOccurrence?_child_succ_sheet _ _ _ _ _ hregion] at compiled
      contradiction
  | cut parent =>
      rw [compileOccurrence?_child_succ_cut _ _ _ _ _ _ hregion] at compiled
      cases hbody : compileRegion? d childFuel child context binders with
      | none => simp [hbody] at compiled
      | some result => simp [hbody] at compiled
  | bubble parent actualArity =>
      rw [compileOccurrence?_child_succ_bubble _ _ _ _ _ _ _ hregion]
        at compiled
      cases hbody : compileRegion? d childFuel child context
          (binders.push child actualArity) with
      | none => simp [hbody] at compiled
      | some result =>
          simp [hbody] at compiled
          obtain ⟨rfl, bodyEq⟩ := compiled
          cases bodyEq
          exact hbody

@[simp] theorem compileItems?_nil
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels) :
    compileItems? d fuel context binders [] = some .nil := by
  cases fuel <;> rfl

theorem compileItems?_cons
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (tail : List (LocalOccurrence d.regionCount d.nodeCount)) :
    compileItems? d fuel context binders (occurrence :: tail) = (do
      let head ← compileOccurrence? d fuel context binders occurrence
      let rest ← compileItems? d fuel context binders tail
      pure (.cons head rest)) := by
  cases fuel <;> rfl

theorem compileRegion?_eq_compileItems?
    (d : Diagram) (childFuel : Nat) (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels) :
    compileRegion? d childFuel origin context binders = (do
      let items ← compileItems? d childFuel (context.extend origin) binders
        (localOccurrences d origin)
      pure (.mk items)) := by
  cases childFuel <;> rfl

/-- The root compiler is the fixed item compiler at the exact root call. -/
theorem compileRoot?_eq_compileItems?
    (d : Diagram) (ambient locals : WireContext d) :
    compileRoot? d ambient locals = (do
      let items ← compileItems? d d.regionCount (ambient ++ locals)
        BinderContext.empty (localOccurrences d d.root)
      pure (.mk items)) := rfl

/-- Every exact compiler call is packaged from the ordinary compilation of
its direct occurrence list. -/
theorem CompilerCall.compile?_eq_compileItems? (call : CompilerCall d) :
    call.compile? = (do
      let items ← compileItems? d call.childFuel call.fullContext
        call.binders (localOccurrences d call.origin)
      pure (.mk items)) := by
  cases call with
  | root ambient locals => rfl
  | nested childFuel origin context rels binders =>
      simpa [CompilerCall.fullContext, CompilerCall.localContext,
        WireContext.extend] using
          compileRegion?_eq_compileItems? d childFuel origin context binders

/-- Successful root-item compilation packages the exact root result. -/
theorem compileRoot?_of_items
    {items : CompiledItems d d.regionCount (ambient ++ locals) []
      BinderContext.empty}
    (compiled : compileItems? d d.regionCount (ambient ++ locals)
      BinderContext.empty (localOccurrences d d.root) = some items) :
    compileRoot? d ambient locals = some (.mk items) := by
  rw [compileRoot?_eq_compileItems?]
  simp [compiled]

/-- Item compilation distributes constructively over ordinary list append. -/
theorem compileItems?_append
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels)
    (initial suffix : List (LocalOccurrence d.regionCount d.nodeCount))
    {initialResult suffixResult : CompiledItems d fuel context rels binders}
    (initialCompiled :
      compileItems? d fuel context binders initial = some initialResult)
    (suffixCompiled :
      compileItems? d fuel context binders suffix = some suffixResult) :
    compileItems? d fuel context binders (initial ++ suffix) =
      some (initialResult.append suffixResult) := by
  induction initial generalizing initialResult with
  | nil =>
      simp only [compileItems?_nil] at initialCompiled
      cases initialCompiled
      simpa using suffixCompiled
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at initialCompiled
      cases hhead : compileOccurrence? d fuel context binders occurrence with
      | none => simp [hhead] at initialCompiled
      | some head =>
          cases htail : compileItems? d fuel context binders tail with
          | none => simp [hhead, htail] at initialCompiled
          | some tailResult =>
              simp [hhead, htail] at initialCompiled
              subst initialResult
              rw [List.cons_append, compileItems?_cons, hhead,
                ih htail]
              rfl

theorem compileRoot?_localCount
    {body : CompiledRegion d (.root ambient locals)}
    (_compiled : compileRoot? d ambient locals = some body) :
    body.localCount = locals.length := rfl

theorem compileOccurrence?_origin
    {item : CompiledItem d fuel context rels binders}
    (compiled : compileOccurrence? d fuel context binders occurrence =
      some item) :
    item.origin = occurrence := by
  cases fuel with
  | zero =>
      cases occurrence with
      | node node => exact compileNode?_origin compiled
      | child child => simp [compileOccurrence?, compileOccurrenceZero?] at compiled
  | succ childFuel =>
      cases occurrence with
      | node node => exact compileNode?_origin compiled
      | child child =>
          cases hregion : d.regions child with
          | sheet =>
              simp [compileOccurrence?, compileOccurrenceSuccWith?, hregion]
                at compiled
          | cut parent =>
              cases hbody : compileRegion? d childFuel child context binders with
              | none =>
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hregion,
                    hbody] at compiled
              | some body =>
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hregion,
                    hbody] at compiled
                  subst item
                  rfl
          | bubble parent arity =>
              cases hbody : compileRegion? d childFuel child context
                  (binders.push child arity) with
              | none =>
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hregion,
                    hbody] at compiled
              | some body =>
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hregion,
                    hbody] at compiled
                  subst item
                  rfl

theorem compileItems?_origins
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d fuel context rels binders}
    (compiled : compileItems? d fuel context binders occurrences = some items) :
    items.origins = occurrences := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      rfl
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d fuel context binders occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d fuel context binders tail with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              cases compiled
              rw [CompiledItems.origins_cons,
                compileOccurrence?_origin hitem, ih htail]

theorem compileItems?_length
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d fuel context rels binders}
    (compiled : compileItems? d fuel context binders occurrences = some items) :
    items.length = occurrences.length := by
  rw [CompiledItems.length_eq_origins_length,
    compileItems?_origins compiled]

theorem compileItems?_get
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d fuel context rels binders}
    (compiled : compileItems? d fuel context binders occurrences = some items)
    (index : Fin occurrences.length) :
    compileOccurrence? d fuel context binders (occurrences.get index) =
      some (items.get (Fin.cast (compileItems?_length compiled).symm index)) := by
  induction occurrences generalizing items with
  | nil => exact Fin.elim0 index
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d fuel context binders occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d fuel context binders tail with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              cases compiled
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · simpa only [List.get, CompiledItems.get] using hitem
              · have ihResult := ih htail tailIndex
                simpa only [List.get, CompiledItems.get] using ihResult

theorem compileItems?_complete
    (d : Diagram) (fuel : Nat) (context : WireContext d)
    (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (hsuccess : ∀ occurrence, occurrence ∈ occurrences →
      ∃ item, compileOccurrence? d fuel context binders occurrence =
        some item) :
    ∃ items, compileItems? d fuel context binders occurrences = some items := by
  induction occurrences with
  | nil => exact ⟨.nil, compileItems?_nil d fuel context binders⟩
  | cons occurrence tail ih =>
      obtain ⟨item, hitem⟩ := hsuccess occurrence (by simp)
      obtain ⟨rest, hrest⟩ := ih (by
        intro candidate hcandidate
        exact hsuccess candidate (by simp [hcandidate]))
      exact ⟨.cons item rest, by
        rw [compileItems?_cons, hitem, hrest]
        rfl⟩

/-- Every well-formed node compiles in covering wire and binder contexts. -/
theorem compileNode?_complete
    (hwf : d.WellFormed)
    (fuel : Nat)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (hwires : context.Covers region) (hbinders : binders.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region) :
    ∃ item, compileNode? d fuel context binders node = some item := by
  cases hnode : d.nodes node with
  | atom nodeRegion binder =>
      have hnodeRegion : nodeRegion = region := by simpa [hnode] using hregion
      subst nodeRegion
      obtain ⟨parent, arity, hbubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf hnode
      obtain ⟨relation, hrelation⟩ :=
        BinderContext.checked_atom_binder_available hwf hbinders hnode hbubble
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf
        hwires (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, hnode, hbubble]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.atom relation arguments), by
        simp [compileNode?, hnode, hrelation, harguments]⟩
  | identity nodeRegion arity =>
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf
        hwires (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.identity arity arguments), by
        simp [compileNode?, hnode, harguments]⟩

private theorem child_depth
    {d : Diagram} {child parent : Fin d.regionCount} {depth : Nat}
    (hparent : (d.regions child).parent? = some parent)
    (hdepth : d.climb depth parent = some d.root) :
    d.climb (depth + 1) child = some d.root := by
  change d.climb (Nat.succ depth) child = some d.root
  simpa [Diagram.climb, hparent] using hdepth

/-- A covered region whose predecessor fuel reaches the root compiles. -/
theorem compileRegion?_complete
    (hwf : d.WellFormed)
    {childFuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + childFuel = d.regionCount)
    (hwires : (context.extend region).Exact region)
    (hbinders : binders.Covers region) :
    ∃ body, compileRegion? d childFuel region context binders = some body := by
  induction childFuel generalizing depth region context rels with
  | zero =>
      let extended := context.extend region
      have hextended : extended.Exact region := by simpa [extended] using hwires
      have hoccurrence : ∀ occurrence,
          occurrence ∈ localOccurrences d region →
          ∃ item, compileOccurrence? d 0 extended binders occurrence =
            some item := by
        intro occurrence hmem
        cases occurrence with
        | node node =>
            have hnodeRegion := (mem_localOccurrences_node d region node).mp hmem
            simpa using compileNode?_complete hwf 0 hextended.covers hbinders
              hnodeRegion
        | child child =>
            have hparent :=
              (mem_localOccurrences_child d region child).mp hmem
            have hchildDepth := child_depth hparent hdepth
            have hle := ParentTraversal.climb_to_root_steps_le_regionCount d
              hwf.root_is_sheet hwf.all_regions_reach_root hchildDepth
            omega
      obtain ⟨items, hitems⟩ := compileItems?_complete d 0 extended binders
        (localOccurrences d region) hoccurrence
      refine ⟨.mk items, ?_⟩
      rw [compileRegion?_eq_compileItems?, hitems]
      rfl

  | succ childFuel ih =>
      let extended := context.extend region
      have hextended : extended.Exact region := by simpa [extended] using hwires
      have hoccurrence : ∀ occurrence,
          occurrence ∈ localOccurrences d region →
          ∃ item, compileOccurrence? d (childFuel + 1) extended binders
            occurrence = some item := by
        intro occurrence hmem
        cases occurrence with
        | node node =>
            have hnodeRegion := (mem_localOccurrences_node d region node).mp hmem
            simpa using compileNode?_complete hwf (childFuel + 1)
              hextended.covers hbinders hnodeRegion
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
                have hchildFuel : depth + 1 + childFuel = d.regionCount := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.covers_cut_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨CompiledItem.cut body, by
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild,
                    hbody]⟩
            | bubble parent arity =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + childFuel = d.regionCount := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.push_covers_bubble_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨CompiledItem.bubble arity body, by
                  simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild,
                    hbody]⟩
      obtain ⟨items, hitems⟩ := compileItems?_complete d (childFuel + 1)
        extended binders (localOccurrences d region) hoccurrence
      refine ⟨.mk items, ?_⟩
      rw [compileRegion?_eq_compileItems?, hitems]
      rfl

/-- Compile any chosen direct-occurrence list at an exact lexical context.
The fixed occurrence compiler owns all recursive region calls. -/
theorem compileDirectItems?_complete
    (hwf : d.WellFormed)
    {fuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + fuel = d.regionCount)
    (hwires : context.Exact region)
    (hbinders : binders.Covers region)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d region) :
    ∃ items, compileItems? d fuel context binders occurrences = some items := by
  induction fuel generalizing depth region context rels with
  | zero =>
      apply compileItems?_complete
      intro occurrence occurrenceMember
      have direct := hlocal occurrence occurrenceMember
      cases occurrence with
      | node node =>
          have hnodeRegion :=
            (mem_localOccurrences_node d region node).mp direct
          simpa using compileNode?_complete hwf 0 hwires.covers hbinders
            hnodeRegion
      | child child =>
          have hparent :=
            (mem_localOccurrences_child d region child).mp direct
          have hchildDepth := child_depth hparent hdepth
          have hle := ParentTraversal.climb_to_root_steps_le_regionCount d
            hwf.root_is_sheet hwf.all_regions_reach_root hchildDepth
          omega
  | succ childFuel ih =>
      apply compileItems?_complete
      intro occurrence occurrenceMember
      have direct := hlocal occurrence occurrenceMember
      cases occurrence with
      | node node =>
          have hnodeRegion :=
            (mem_localOccurrences_node d region node).mp direct
          simpa using compileNode?_complete hwf (childFuel + 1)
            hwires.covers hbinders hnodeRegion
      | child child =>
          have hparent :=
            (mem_localOccurrences_child d region child).mp direct
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
              have hchildFuel : depth + 1 + childFuel = d.regionCount := by
                omega
              have hchildWires := hwires.extend_child hwf hparent
              have hchildBinders :=
                BinderContext.covers_cut_child hbinders hchild
              obtain ⟨body, hbody⟩ := compileRegion?_complete hwf
                hchildDepth hchildFuel hchildWires hchildBinders
              exact ⟨CompiledItem.cut body, by
                simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild,
                  hbody]⟩
          | bubble parent arity =>
              have hparentEq : parent = region := by
                simpa [hchild, CRegion.parent?] using hparent
              subst parent
              have hchildDepth := child_depth hparent hdepth
              have hchildFuel : depth + 1 + childFuel = d.regionCount := by
                omega
              have hchildWires := hwires.extend_child hwf hparent
              have hchildBinders :=
                BinderContext.push_covers_bubble_child hbinders hchild
              obtain ⟨body, hbody⟩ := compileRegion?_complete hwf
                hchildDepth hchildFuel hchildWires hchildBinders
              exact ⟨CompiledItem.bubble arity body, by
                simp [compileOccurrence?, compileOccurrenceSuccWith?, hchild,
                  hbody]⟩

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

theorem compileRoot?_complete
    (hwf : d.WellFormed)
    (ambient locals : WireContext d)
    (hwires : WireContext.Exact (ambient ++ locals) d.root) :
    ∃ body, compileRoot? d ambient locals = some body := by
  have hbinders : (BinderContext.empty : BinderContext d []).Covers d.root :=
    BinderContext.empty_covers_root hwf
  obtain ⟨items, hitems⟩ := compileDirectItems?_complete hwf
    (fuel := d.regionCount) (depth := 0) (region := d.root)
    (context := ambient ++ locals) (binders := BinderContext.empty)
    (by rfl) (by omega) hwires hbinders (localOccurrences d d.root)
    (fun _ member => member)
  exact ⟨.mk items, by
    simp [compileRoot?, hitems]⟩

end VisualProof.Concrete.Elaboration
