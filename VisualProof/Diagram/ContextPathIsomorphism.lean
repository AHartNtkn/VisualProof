import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

open VisualProof
open Theory

/-- Proof-relevant transport of a focused region path through a region
isomorphism.  Besides locating the corresponding target focus, the record
retains the isomorphisms of both the enclosing one-hole context and the
focused body. -/
structure RegionIso.ContextPathAlignment
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target)
    {sourcePath : List Nat}
    (sourceWitness : Region.ContextPath source sourcePath) where
  targetPath : List Nat
  targetWitness : Region.ContextPath target targetPath
  holeRelsEq : targetWitness.toFocus.holeRels =
    sourceWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  context : DiagramContextIso signature wire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq ▸ targetWitness.toFocus.context)
  body : RegionIso signature holeWire sourceWitness.toFocus.holeRels
    sourceWitness.toFocus.body
    (holeRelsEq ▸ targetWitness.toFocus.body)

/-- Simultaneously transporting a context and its filling body across the
same relation-context equality does not change the reconstructed region. -/
theorem DiagramContext.fill_castHoleRels
    {targetHoleRels sourceHoleRels : RelCtx}
    (equality : targetHoleRels = sourceHoleRels)
    (context : DiagramContext signature outerWires holeWires outerRels
      targetHoleRels)
    (body : Region signature holeWires targetHoleRels) :
    (equality ▸ context).fill (equality ▸ body) = context.fill body := by
  cases equality
  rfl

/-- Casting a region to an equal relation context and immediately back is
definitionally inert, packaged so later dependent alignment proofs need not
eliminate a proof field from the alignment record. -/
theorem Region.castRels_symm_cast
    {sourceRels targetRels : RelCtx}
    (equality : targetRels = sourceRels)
    (region : Region signature wires sourceRels) :
    equality ▸ (equality.symm ▸ region) = region := by
  cases equality
  rfl

/-- Replace the aligned holes by isomorphic bodies and rebuild the complete
source and target regions. -/
theorem RegionIso.ContextPathAlignment.fill
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    {iso : RegionIso signature wire rels source target}
    {sourcePath : List Nat}
    {sourceWitness : Region.ContextPath source sourcePath}
    (alignment : RegionIso.ContextPathAlignment iso sourceWitness)
    (sourceReplacement : Region signature
      sourceWitness.toFocus.holeWires sourceWitness.toFocus.holeRels)
    (targetReplacement : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels)
    (replacement : RegionIso signature alignment.holeWire
      sourceWitness.toFocus.holeRels sourceReplacement
      (alignment.holeRelsEq ▸ targetReplacement)) :
    RegionIso signature wire rels
      (sourceWitness.toFocus.context.fill sourceReplacement)
      (alignment.targetWitness.toFocus.context.fill targetReplacement) := by
  have lifted := alignment.context.fill replacement
  have targetFill := DiagramContext.fill_castHoleRels
    alignment.holeRelsEq alignment.targetWitness.toFocus.context
      targetReplacement
  exact targetFill ▸ lifted

theorem ItemSeq.focusAt?_item
    (items : ItemSeq signature wires rels) (index : Nat)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index = some focus) :
    focus.item = items.get ⟨index,
      ItemSeq.focusAt?_index_lt items index focus hfocus⟩ := by
  let finiteIndex : Fin items.length :=
    ⟨index, ItemSeq.focusAt?_index_lt items index focus hfocus⟩
  obtain ⟨other, hother, hitem⟩ :=
    ItemSeq.focusAt?_complete items finiteIndex
  have : other = focus := Option.some.inj (hother.symm.trans hfocus)
  subst other
  exact hitem

private theorem ItemIso.target_of_cut
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBody : Region signature sourceWires rels}
    {targetItem : Item signature targetWires rels}
    (iso : ItemIso signature wire rels (.cut sourceBody) targetItem) :
    ∃ targetBody, targetItem = .cut targetBody ∧
      RegionIso signature wire rels sourceBody targetBody := by
  cases iso with
  | cut body => exact ⟨_, rfl, body⟩

private theorem ItemIso.target_of_bubble
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {targetItem : Item signature targetWires rels}
    (iso : ItemIso signature wire rels
      (.bubble arity sourceBody) targetItem) :
    ∃ targetBody, targetItem = .bubble arity targetBody ∧
      RegionIso signature wire (arity :: rels) sourceBody targetBody := by
  cases iso with
  | bubble body => exact ⟨_, rfl, body⟩

theorem DiagramContext.castHoleRels_cut
    (equality : targetHoleRels = sourceHoleRels)
    (before after : ItemSeq signature (outerWires + localWires) outerRels)
    (child : DiagramContext signature (outerWires + localWires) holeWires
      outerRels targetHoleRels) :
    equality ▸ (DiagramContext.cut localWires before after child) =
      DiagramContext.cut localWires before after (equality ▸ child) := by
  cases equality
  rfl

theorem DiagramContext.castHoleRels_bubble
    (equality : targetHoleRels = sourceHoleRels)
    (before after : ItemSeq signature (outerWires + localWires) outerRels)
    (child : DiagramContext signature (outerWires + localWires) holeWires
      (arity :: outerRels) targetHoleRels) :
    equality ▸ (DiagramContext.bubble localWires before after arity child) =
      DiagramContext.bubble localWires before after arity
        (equality ▸ child) := by
  cases equality
  rfl

/-- Extend the sibling suffix of a successful focus without changing the
focused position or item. -/
def ItemSeq.Focus.appendAfter
    {items : ItemSeq signature wires rels}
    (focus : ItemSeq.Focus items)
    (suffix : ItemSeq signature wires rels) :
    ItemSeq.Focus (items.append suffix) where
  before := focus.before
  item := focus.item
  after := focus.after.append suffix
  rebuild := by
    change focus.before.append
        ((ItemSeq.cons focus.item focus.after).append suffix) =
      items.append suffix
    rw [← ItemSeq.append_assoc, focus.rebuild]

theorem ItemSeq.focusAt?_append_left
    (items suffix : ItemSeq signature wires rels) (index : Nat)
    (focus : ItemSeq.Focus items)
    (hfocus : items.focusAt? index = some focus) :
    (items.append suffix).focusAt? index =
      some (focus.appendAfter suffix) := by
  cases items with
  | nil => simp [ItemSeq.focusAt?] at hfocus
  | cons head tail =>
      cases index with
      | zero =>
          simp [ItemSeq.focusAt?] at hfocus
          subst focus
          rfl
      | succ index =>
          cases htail : tail.focusAt? index with
          | none => simp [ItemSeq.focusAt?, htail] at hfocus
          | some tailFocus =>
              simp [ItemSeq.focusAt?, htail] at hfocus
              subst focus
              have appended := ItemSeq.focusAt?_append_left tail suffix index
                tailFocus htail
              simp only [ItemSeq.append, ItemSeq.focusAt?]
              rw [appended]
              rfl
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

/-- A non-root context path in an item block survives appending arbitrary
root siblings on the right. -/
def Region.ContextPath.appendRootItemsRight
    {items : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat} :
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest)) →
    (suffix : ItemSeq signature wires rels) →
    Region.ContextPath (Region.mk 0 (items.append suffix)) (index :: rest)
  | .cut focus atIndex isCut nested, suffix =>
      .cut (focus.appendAfter suffix)
        (ItemSeq.focusAt?_append_left items suffix index focus atIndex)
        isCut nested
  | .bubble focus atIndex isBubble nested, suffix =>
      .bubble (focus.appendAfter suffix)
        (ItemSeq.focusAt?_append_left items suffix index focus atIndex)
        isBubble nested

/-- Reindex a replacement along the definitionally unchanged terminal type
of `appendRootItemsRight`. -/
def Region.ContextPath.appendRootItemsRightReplacement
    {items suffix : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat} :
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest)) →
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) →
    Region signature
      (witness.appendRootItemsRight suffix).toFocus.holeWires
      (witness.appendRootItemsRight suffix).toFocus.holeRels
  | .cut _ _ _ _, replacement => replacement
  | .bubble _ _ _ _, replacement => replacement

/-- Appending root siblings preserves the terminal relation context. -/
def Region.ContextPath.appendRootItemsRightHoleRelsEq
    {items suffix : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat} :
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest)) →
    (witness.appendRootItemsRight suffix).toFocus.holeRels =
      witness.toFocus.holeRels
  | .cut _ _ _ _ => rfl
  | .bubble _ _ _ _ => rfl

/-- Appending root siblings preserves the terminal wire carrier. -/
def Region.ContextPath.appendRootItemsRightHoleWire
    {items suffix : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat} :
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest)) →
    FiniteEquiv
      (Fin (witness.appendRootItemsRight suffix).toFocus.holeWires)
      (Fin witness.toFocus.holeWires)
  | .cut _ _ _ _ => FiniteEquiv.refl _
  | .bubble _ _ _ _ => FiniteEquiv.refl _

/-- The root item block obtained by filling a proper path in a zero-local
region.  Nonemptiness excludes the `here` case and keeps the original root
wire carrier unchanged. -/
noncomputable def Region.ContextPath.filledRootItems
    {items : ItemSeq signature wires rels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (proper : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) : ItemSeq signature wires rels := by
  cases witness with
  | here => exact False.elim (proper rfl)
  | cut focus atIndex isCut nested =>
      exact focus.before.append
        (.cons (.cut (nested.toFocus.context.fill replacement)) focus.after)
  | bubble focus atIndex isBubble nested =>
      exact focus.before.append
        (.cons (.bubble _ (nested.toFocus.context.fill replacement))
          focus.after)

/-- Filling a proper path in a zero-local region changes only its root item
block. -/
theorem Region.ContextPath.fill_eq_mk_filledRootItems
    {items : ItemSeq signature wires rels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (proper : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels) :
    witness.toFocus.context.fill replacement =
      Region.mk 0 (witness.filledRootItems proper replacement) := by
  cases witness with
  | here => exact False.elim (proper rfl)
  | cut => rfl
  | bubble => rfl

/-- Semantic form of `fill_eq_mk_filledRootItems`. -/
theorem Region.ContextPath.denote_fill_iff_filledRootItems
    {items : ItemSeq signature wires rels} {path : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) path)
    (proper : path ≠ [])
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement) ↔
      denoteItemSeq model named environment relEnv
        (witness.filledRootItems proper replacement) := by
  rw [witness.fill_eq_mk_filledRootItems proper replacement]
  simp only [denoteRegion_mk, extendWireEnv_zero]
  constructor
  · rintro ⟨_, denotation⟩
    exact denotation
  · intro denotation
    exact ⟨Fin.elim0, denotation⟩

/-- Appending root siblings on the right represents conjunction with those
siblings.  This semantic form is insensitive to the compiler's chosen sibling
order and retains all local witnesses of the focused replacement. -/
theorem Region.ContextPath.appendRootItemsRight_fill_equiv
    {items suffix : ItemSeq signature wires rels}
    {index : Nat} {rest : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest))
    (replacement : Region signature witness.toFocus.holeWires
      witness.toFocus.holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named env relEnv
        ((Region.mk 0 suffix).conjoin
          (witness.toFocus.context.fill replacement)) ↔
      denoteRegion model named env relEnv
        ((witness.appendRootItemsRight suffix).toFocus.context.fill
          (witness.appendRootItemsRightReplacement replacement)) := by
  cases witness with
  | cut focus atIndex isCut nested =>
      have leftEnv : env ∘ Region.conjoinLeftWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinLeftWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinLeftWire, Fin.addCases_left]
      have rightEnv : env ∘ Region.conjoinRightWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinRightWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinRightWire, Fin.addCases_left]
      simp [Region.denote_conjoin, Region.ContextPath.toFocus,
        Region.ContextPath.appendRootItemsRight, DiagramContext.fill,
        Region.ContextPath.appendRootItemsRightReplacement,
        denoteRegion_mk, extendWireEnv_zero, ItemSeq.Focus.appendAfter,
        denoteItemSeq_append, denoteItemSeq_renameWires, leftEnv, rightEnv,
        and_assoc, and_left_comm, and_comm]
  | bubble focus atIndex isBubble nested =>
      have leftEnv : env ∘ Region.conjoinLeftWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinLeftWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinLeftWire, Fin.addCases_left]
      have rightEnv : env ∘ Region.conjoinRightWire wires 0 0 = env := by
        funext wire
        refine Fin.addCases (fun inherited => ?_)
          (fun localIndex => Fin.elim0 localIndex) wire
        apply congrArg env
        change Region.conjoinRightWire wires 0 0
            (Fin.castAdd 0 inherited) = Fin.castAdd 0 inherited
        simp only [Region.conjoinRightWire, Fin.addCases_left]
      simp [Region.denote_conjoin, Region.ContextPath.toFocus,
        Region.ContextPath.appendRootItemsRight, DiagramContext.fill,
        Region.ContextPath.appendRootItemsRightReplacement,
        denoteRegion_mk, extendWireEnv_zero, ItemSeq.Focus.appendAfter,
        denoteItemSeq_append, denoteItemSeq_renameWires, leftEnv, rightEnv,
        and_assoc, and_left_comm, and_comm]

/-- Every intrinsic context path has a corresponding path through an
isomorphic presentation.  Occurrence permutations are followed exactly;
the distinguished child is transported recursively while all siblings are
carried by the surrounding permutation frame. -/
theorem RegionIso.alignContextPath
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target)
    {sourcePath : List Nat}
    (sourceWitness : Region.ContextPath source sourcePath) :
    Nonempty (RegionIso.ContextPathAlignment iso sourceWitness) := by
  induction sourceWitness generalizing targetWires with
  | here source =>
      exact ⟨{
        targetPath := []
        targetWitness := .here target
        holeRelsEq := rfl
        holeWire := wire
        context := .hole wire
        body := iso
      }⟩
  | cut sourceFocus sourceAt sourceIsCut sourceNested induction =>
      cases iso with
      | mk localWire itemSeqIso =>
          cases itemSeqIso with
          | permute positions itemIsos =>
              let sourceIndex : Fin _ := ⟨_,
                ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩
              let targetIndex := positions sourceIndex
              obtain ⟨targetFocus, targetAt, targetItem⟩ :=
                ItemSeq.focusAt?_complete _ targetIndex
              have sourceItem := ItemSeq.focusAt?_item _ _ sourceFocus sourceAt
              have distinguished := itemIsos sourceIndex
              rw [← sourceItem, sourceIsCut, ← targetItem] at distinguished
              obtain ⟨targetBody, targetIsCut, childIso⟩ :=
                ItemIso.target_of_cut distinguished
              let frame : ItemSeqIso.Frame
                  (extendWireEquiv wire localWire) sourceIndex targetIndex := {
                positions := positions
                mapped := rfl
                siblings := fun index _ => itemIsos index
              }
              obtain ⟨child⟩ := induction childIso
              let targetWitness : Region.ContextPath _
                  (targetIndex.val :: child.targetPath) :=
                .cut targetFocus targetAt targetIsCut child.targetWitness
              exact ⟨{
                targetPath := targetIndex.val :: child.targetPath
                targetWitness := targetWitness
                holeRelsEq := by
                  simpa [targetWitness, Region.ContextPath.toFocus] using
                    child.holeRelsEq
                holeWire := child.holeWire
                context := by
                  simp only [targetWitness, Region.ContextPath.toFocus]
                  rw [DiagramContext.castHoleRels_cut]
                  exact
                    DiagramContextIso.cutFrame localWire sourceFocus
                      targetFocus sourceAt targetAt frame
                      sourceNested.toFocus.context
                      (child.holeRelsEq ▸
                        child.targetWitness.toFocus.context) child.context
                body := by
                  simpa [targetWitness, Region.ContextPath.toFocus] using
                    child.body
              }⟩
  | bubble sourceFocus sourceAt sourceIsBubble sourceNested induction =>
      cases iso with
      | mk localWire itemSeqIso =>
          cases itemSeqIso with
          | permute positions itemIsos =>
              let sourceIndex : Fin _ := ⟨_,
                ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩
              let targetIndex := positions sourceIndex
              obtain ⟨targetFocus, targetAt, targetItem⟩ :=
                ItemSeq.focusAt?_complete _ targetIndex
              have sourceItem := ItemSeq.focusAt?_item _ _ sourceFocus sourceAt
              have distinguished := itemIsos sourceIndex
              rw [← sourceItem, sourceIsBubble, ← targetItem] at distinguished
              obtain ⟨targetBody, targetIsBubble, childIso⟩ :=
                ItemIso.target_of_bubble distinguished
              let frame : ItemSeqIso.Frame
                  (extendWireEquiv wire localWire) sourceIndex targetIndex := {
                positions := positions
                mapped := rfl
                siblings := fun index _ => itemIsos index
              }
              obtain ⟨child⟩ := induction childIso
              let targetWitness : Region.ContextPath _
                  (targetIndex.val :: child.targetPath) :=
                .bubble targetFocus targetAt targetIsBubble child.targetWitness
              exact ⟨{
                targetPath := targetIndex.val :: child.targetPath
                targetWitness := targetWitness
                holeRelsEq := by
                  simpa [targetWitness, Region.ContextPath.toFocus] using
                    child.holeRelsEq
                holeWire := child.holeWire
                context := by
                  simp only [targetWitness, Region.ContextPath.toFocus]
                  rw [DiagramContext.castHoleRels_bubble]
                  exact
                    DiagramContextIso.bubbleFrame localWire sourceFocus
                      targetFocus sourceAt targetAt frame
                      sourceNested.toFocus.context
                      (child.holeRelsEq ▸
                        child.targetWitness.toFocus.context) child.context
                body := by
                  simpa [targetWitness, Region.ContextPath.toFocus] using
                    child.body
              }⟩

/-- Identity transport preserves the concrete path, not merely the focused
region up to an arbitrary automorphism.  This proof-relevant form is needed
when a compiler permutation changes only an enclosing occurrence block while
the distinguished child route itself is retained verbatim. -/
theorem Region.ContextPath.identityAlignment
    {region : Region signature wires rels}
    {path : List Nat}
    (witness : Region.ContextPath region path) :
    ∃ alignment : RegionIso.ContextPathAlignment
        (RegionIso.refl region) witness,
      alignment.targetPath = path ∧
        ∀ index, (alignment.holeWire index).val = index.val := by
  induction witness with
  | here region =>
      refine ⟨{
        targetPath := []
        targetWitness := .here region
        holeRelsEq := rfl
        holeWire := FiniteEquiv.refl _
        context := .hole _
        body := RegionIso.refl region
      }, rfl, fun _ => rfl⟩
  | @cut outerWires rels localWires items index rest focus atIndex childBody
      isCut nested induction =>
      obtain ⟨child, childPath, childWire⟩ := induction
      let sourceIndex : Fin items.length :=
        ⟨index, ItemSeq.focusAt?_index_lt items index focus atIndex⟩
      have extendedRefl :
          extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
              (FiniteEquiv.refl (Fin localWires)) =
            FiniteEquiv.refl (Fin (outerWires + localWires)) := by
        apply FiniteEquiv.ext
        intro wire
        refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) wire <;>
          simp [extendWireEquiv, FiniteEquiv.refl]
      let frame : ItemSeqIso.Frame
          (extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
            (FiniteEquiv.refl (Fin localWires))) sourceIndex sourceIndex := by
        apply ItemSeqIso.Frame.castWire extendedRefl.symm
        exact {
          positions := FiniteEquiv.refl _
          mapped := rfl
          siblings := fun sibling _ => ItemIso.refl (items.get sibling)
        }
      let targetWitness : Region.ContextPath _
          (sourceIndex.val :: child.targetPath) :=
        .cut focus atIndex isCut child.targetWitness
      let alignment : RegionIso.ContextPathAlignment
          (RegionIso.refl (Region.mk localWires items))
          (.cut focus atIndex isCut nested) := {
        targetPath := sourceIndex.val :: child.targetPath
        targetWitness := targetWitness
        holeRelsEq := by
          simpa [targetWitness, Region.ContextPath.toFocus] using
            child.holeRelsEq
        holeWire := child.holeWire
        context := by
          simp only [targetWitness, Region.ContextPath.toFocus]
          rw [DiagramContext.castHoleRels_cut]
          have childContext : DiagramContextIso signature
              (extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
                (FiniteEquiv.refl (Fin localWires))) child.holeWire rels
              nested.toFocus.holeRels nested.toFocus.context
              (child.holeRelsEq ▸
                child.targetWitness.toFocus.context) := by
            rw [extendedRefl]
            exact child.context
          exact DiagramContextIso.cutFrame
            (FiniteEquiv.refl (Fin localWires)) focus focus atIndex atIndex
            frame nested.toFocus.context
            (child.holeRelsEq ▸ child.targetWitness.toFocus.context)
            childContext
        body := by
          simpa [targetWitness, Region.ContextPath.toFocus] using child.body
      }
      refine ⟨alignment, ?_, ?_⟩
      · simp only [alignment, sourceIndex]
        rw [childPath]
      · intro index
        exact childWire index
  | @bubble outerWires rels localWires arity items index rest focus atIndex
      childBody isBubble nested induction =>
      obtain ⟨child, childPath, childWire⟩ := induction
      let sourceIndex : Fin items.length :=
        ⟨index, ItemSeq.focusAt?_index_lt items index focus atIndex⟩
      have extendedRefl :
          extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
              (FiniteEquiv.refl (Fin localWires)) =
            FiniteEquiv.refl (Fin (outerWires + localWires)) := by
        apply FiniteEquiv.ext
        intro wire
        refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) wire <;>
          simp [extendWireEquiv, FiniteEquiv.refl]
      let frame : ItemSeqIso.Frame
          (extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
            (FiniteEquiv.refl (Fin localWires))) sourceIndex sourceIndex := by
        apply ItemSeqIso.Frame.castWire extendedRefl.symm
        exact {
          positions := FiniteEquiv.refl _
          mapped := rfl
          siblings := fun sibling _ => ItemIso.refl (items.get sibling)
        }
      let targetWitness : Region.ContextPath _
          (sourceIndex.val :: child.targetPath) :=
        .bubble focus atIndex isBubble child.targetWitness
      let alignment : RegionIso.ContextPathAlignment
          (RegionIso.refl (Region.mk localWires items))
          (.bubble focus atIndex isBubble nested) := {
        targetPath := sourceIndex.val :: child.targetPath
        targetWitness := targetWitness
        holeRelsEq := by
          simpa [targetWitness, Region.ContextPath.toFocus] using
            child.holeRelsEq
        holeWire := child.holeWire
        context := by
          simp only [targetWitness, Region.ContextPath.toFocus]
          rw [DiagramContext.castHoleRels_bubble]
          have childContext : DiagramContextIso signature
              (extendWireEquiv (FiniteEquiv.refl (Fin outerWires))
                (FiniteEquiv.refl (Fin localWires))) child.holeWire
              (arity :: rels) nested.toFocus.holeRels
              nested.toFocus.context
              (child.holeRelsEq ▸
                child.targetWitness.toFocus.context) := by
            rw [extendedRefl]
            exact child.context
          exact DiagramContextIso.bubbleFrame
            (FiniteEquiv.refl (Fin localWires)) focus focus atIndex atIndex
            frame nested.toFocus.context
            (child.holeRelsEq ▸ child.targetWitness.toFocus.context)
            childContext
        body := by
          simpa [targetWitness, Region.ContextPath.toFocus] using child.body
      }
      refine ⟨alignment, ?_, ?_⟩
      · simp only [alignment, sourceIndex]
        rw [childPath]
      · intro index
        exact childWire index

/-- Transport a semantic equivalence between two source presentations across
isomorphisms of both endpoints. -/
theorem RegionIso.transport_equivalence
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBefore sourceAfter : Region signature sourceWires rels}
    {targetBefore targetAfter : Region signature targetWires rels}
    (beforeIso : RegionIso signature wire rels sourceBefore targetBefore)
    (afterIso : RegionIso signature wire rels sourceAfter targetAfter)
    (sourceEquivalent :
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (env : Fin sourceWires → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteRegion model named env relEnv sourceBefore ↔
          denoteRegion model named env relEnv sourceAfter)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named targetEnv relEnv targetBefore ↔
      denoteRegion model named targetEnv relEnv targetAfter := by
  let sourceEnv : Fin sourceWires → model.Carrier :=
    fun index => targetEnv (wire index)
  have environments : EnvironmentsAgree wire sourceEnv targetEnv := by
    intro index
    rfl
  exact (beforeIso.denotation model named sourceEnv targetEnv relEnv
    environments).symm.trans
      ((sourceEquivalent model named sourceEnv relEnv).trans
        (afterIso.denotation model named sourceEnv targetEnv relEnv
          environments))

end VisualProof.Diagram
