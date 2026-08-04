import VisualProof.Data.Finite
import VisualProof.Diagram.Context

namespace VisualProof.Diagram

open VisualProof
open Theory

def extendWireEquiv
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)) :
    FiniteEquiv (Fin (sourceOuter + sourceLocal))
      (Fin (targetOuter + targetLocal)) where
  toFun := Fin.addCases
    (fun i => Fin.castAdd targetLocal (outer i))
    (fun i => Fin.natAdd targetOuter (localEquiv i))
  invFun := Fin.addCases
    (fun i => Fin.castAdd sourceLocal (outer.invFun i))
    (fun i => Fin.natAdd sourceOuter (localEquiv.invFun i))
  left_inv := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left, Fin.addCases_right,
        outer.left_inv, localEquiv.left_inv]
  right_inv := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.addCases_left, Fin.addCases_right,
        outer.right_inv, localEquiv.right_inv]

@[simp] theorem extendWireEquiv_outer
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (index : Fin sourceOuter) :
    extendWireEquiv outer localEquiv (Fin.castAdd sourceLocal index) =
      Fin.castAdd targetLocal (outer index) := by
  simp [extendWireEquiv]

@[simp] theorem extendWireEquiv_local
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (index : Fin sourceLocal) :
    extendWireEquiv outer localEquiv (Fin.natAdd sourceOuter index) =
      Fin.natAdd targetOuter (localEquiv index) := by
  simp [extendWireEquiv]

def EnvironmentsAgree (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (sourceEnv : Fin sourceWires -> D) (targetEnv : Fin targetWires -> D) : Prop :=
  forall i, targetEnv (wire i) = sourceEnv i

theorem extendWireEnv_agree
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceOuterEnv : Fin sourceOuter -> D)
    (targetOuterEnv : Fin targetOuter -> D)
    (sourceLocalEnv : Fin sourceLocal -> D)
    (targetLocalEnv : Fin targetLocal -> D)
    (outerAgree : EnvironmentsAgree outer sourceOuterEnv targetOuterEnv)
    (localAgree : EnvironmentsAgree localEquiv sourceLocalEnv targetLocalEnv) :
    EnvironmentsAgree (extendWireEquiv outer localEquiv)
      (extendWireEnv sourceOuterEnv sourceLocalEnv)
      (extendWireEnv targetOuterEnv targetLocalEnv) := by
  intro index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simpa only [extendWireEquiv_outer, extendWireEnv,
      Fin.addCases_left] using outerAgree i
  · simpa only [extendWireEquiv_local, extendWireEnv,
      Fin.addCases_right] using localAgree i

mutual
  inductive RegionIso (signature : List Nat) :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      Region signature sourceWires rels ->
      Region signature targetWires rels -> Prop
    | mk {sourceWires targetWires sourceLocal targetLocal : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
        {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
        (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
        (items : ItemSeqIso signature (extendWireEquiv ambient localEquiv) rels
          sourceItems targetItems) :
        RegionIso signature ambient rels
          (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)

  inductive ItemIso (signature : List Nat) :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      Item signature sourceWires rels ->
      Item signature targetWires rels -> Prop
    | equation {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
        {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
        {targetTerm : Lambda.Term 0 (Fin targetWires)}
        (output_eq : ambient sourceOutput = targetOutput)
        (term_eq : sourceTerm.mapFree ambient = targetTerm) :
        ItemIso signature ambient rels
          (.equation sourceOutput sourceTerm)
          (.equation targetOutput targetTerm)
    | atom {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        (relation : RelVar rels arity)
        {sourceArguments : Fin arity -> Fin sourceWires}
        {targetArguments : Fin arity -> Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemIso signature ambient rels
          (.atom relation sourceArguments) (.atom relation targetArguments)
    | named {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        (relation : NamedRel signature arity)
        {sourceArguments : Fin arity -> Fin sourceWires}
        {targetArguments : Fin arity -> Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemIso signature ambient rels
          (.named relation sourceArguments) (.named relation targetArguments)
    | cut {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region signature sourceWires rels}
        {targetBody : Region signature targetWires rels}
        (body : RegionIso signature ambient rels sourceBody targetBody) :
        ItemIso signature ambient rels (.cut sourceBody) (.cut targetBody)
    | bubble {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region signature sourceWires (arity :: rels)}
        {targetBody : Region signature targetWires (arity :: rels)}
        (body : RegionIso signature ambient (arity :: rels)
          sourceBody targetBody) :
        ItemIso signature ambient rels
          (.bubble arity sourceBody) (.bubble arity targetBody)

  inductive ItemSeqIso (signature : List Nat) :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      ItemSeq signature sourceWires rels ->
      ItemSeq signature targetWires rels -> Prop
    | permute {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {source : ItemSeq signature sourceWires rels}
        {target : ItemSeq signature targetWires rels}
        (positions : FiniteEquiv (Fin source.length) (Fin target.length))
        (items : forall i, ItemIso signature ambient rels
          (source.get i) (target.get (positions i))) :
        ItemSeqIso signature ambient rels source target
end

/-- Proof-relevant presentation of a region isomorphism retaining the exact
item-position equivalence. This is used when a client must replace one mapped
item instead of merely consuming the propositional isomorphism. -/
inductive RegionIsoPresentation (signature : List Nat) :
    {sourceWires targetWires : Nat} →
    (ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)) →
    (rels : RelCtx) → Region signature sourceWires rels →
    Region signature targetWires rels → Type
  | mk {sourceLocal targetLocal : Nat}
      {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
      {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
      {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
      (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
      (positions : FiniteEquiv (Fin sourceItems.length)
        (Fin targetItems.length))
      (items : ∀ index, ItemIso signature
        (extendWireEquiv ambient localEquiv) rels
        (sourceItems.get index) (targetItems.get (positions index))) :
      RegionIsoPresentation signature ambient rels
        (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)

def RegionIsoPresentation.iso
    (presentation : RegionIsoPresentation signature ambient rels source target) :
    RegionIso signature ambient rels source target := by
  cases presentation with
  | mk localEquiv positions items =>
      exact .mk localEquiv (.permute positions items)


def ItemSeq.replaceAt :
    (items : ItemSeq signature wires rels) →
    Fin items.length → Item signature wires rels →
      ItemSeq signature wires rels
  | .nil, index, _ => Fin.elim0 index
  | .cons head tail, index, replacement =>
      Fin.cases (.cons replacement tail)
        (fun rest => .cons head (ItemSeq.replaceAt tail rest replacement)) index

@[simp] theorem ItemSeq.replaceAt_length
    (items : ItemSeq signature wires rels) (index : Fin items.length)
    (replacement : Item signature wires rels) :
    (items.replaceAt index replacement).length = items.length := by
  cases items with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      induction index using Fin.cases with
      | zero => rfl
      | succ rest => simp [ItemSeq.replaceAt, ItemSeq.length,
          ItemSeq.replaceAt_length tail rest replacement]
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

theorem ItemSeq.get_replaceAt_same
    (items : ItemSeq signature wires rels) (index : Fin items.length)
    (replacement : Item signature wires rels) :
    (items.replaceAt index replacement).get
        (Fin.cast (items.replaceAt_length index replacement).symm index) =
      replacement := by
  cases items with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      induction index using Fin.cases with
      | zero => rfl
      | succ rest => simpa [ItemSeq.replaceAt, ItemSeq.get] using
          ItemSeq.get_replaceAt_same tail rest replacement
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

theorem ItemSeq.get_replaceAt_of_ne
    (items : ItemSeq signature wires rels) (index other : Fin items.length)
    (replacement : Item signature wires rels) (hne : other ≠ index) :
    (items.replaceAt index replacement).get
        (Fin.cast (items.replaceAt_length index replacement).symm other) =
      items.get other := by
  cases items with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      induction index using Fin.cases with
      | zero =>
          induction other using Fin.cases with
          | zero => exact False.elim (hne rfl)
          | succ otherRest => rfl
      | succ indexRest =>
          induction other using Fin.cases with
          | zero => rfl
          | succ otherRest => simpa [ItemSeq.replaceAt, ItemSeq.get] using
            ItemSeq.get_replaceAt_of_ne tail indexRest otherRest replacement (by
              intro heq
              apply hne
              subst otherRest
              rfl)
termination_by items.length
decreasing_by simp_all [ItemSeq.length]

theorem ItemSeqIso.replaceAt
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (sourceIndex : Fin source.length) (targetIndex : Fin target.length)
    (itemIsos : ∀ i, i ≠ sourceIndex → ItemIso signature wire rels
      (source.get i) (target.get (positions i)))
    (sourceReplacement : Item signature sourceWires rels)
    (targetReplacement : Item signature targetWires rels)
    (mapped : positions sourceIndex = targetIndex)
    (replacement : ItemIso signature wire rels sourceReplacement
      targetReplacement) :
    ItemSeqIso signature wire rels
      (source.replaceAt sourceIndex sourceReplacement)
      (target.replaceAt targetIndex targetReplacement) := by
      have hmapped := mapped
      let sourceCast : Fin (source.replaceAt sourceIndex sourceReplacement).length →
          Fin source.length :=
        Fin.cast (source.replaceAt_length sourceIndex sourceReplacement)
      let targetCast : Fin target.length →
          Fin (target.replaceAt targetIndex targetReplacement).length :=
        Fin.cast (target.replaceAt_length targetIndex targetReplacement).symm
      let replacedPositions : FiniteEquiv
          (Fin (source.replaceAt sourceIndex sourceReplacement).length)
          (Fin (target.replaceAt targetIndex targetReplacement).length) := {
        toFun := fun index => Fin.cast
          (target.replaceAt_length targetIndex targetReplacement).symm
          (positions (Fin.cast
            (source.replaceAt_length sourceIndex sourceReplacement) index))
        invFun := fun index => Fin.cast
          (source.replaceAt_length sourceIndex sourceReplacement).symm
          (positions.invFun (Fin.cast
            (target.replaceAt_length targetIndex targetReplacement) index))
        left_inv := by
          intro index
          apply Fin.ext
          simpa using congrArg Fin.val
            (positions.left_inv (Fin.cast
              (source.replaceAt_length sourceIndex sourceReplacement) index))
        right_inv := by
          intro index
          apply Fin.ext
          simpa using congrArg Fin.val
            (positions.right_inv (Fin.cast
              (target.replaceAt_length targetIndex targetReplacement) index))
      }
      refine ItemSeqIso.permute replacedPositions ?_
      intro index
      let original := sourceCast index
      by_cases hindex : original = sourceIndex
      · have htarget : positions original = targetIndex := by
          simpa [hindex] using hmapped
        have hsourceIndex : index = Fin.cast
            (source.replaceAt_length sourceIndex sourceReplacement).symm
            sourceIndex := by
          apply Fin.ext
          simpa [original, sourceCast] using congrArg Fin.val hindex
        have htargetIndex : replacedPositions index = Fin.cast
            (target.replaceAt_length targetIndex targetReplacement).symm
            targetIndex := by
          apply Fin.ext
          simpa [replacedPositions, original, sourceCast] using
            congrArg Fin.val htarget
        rw [hsourceIndex]
        have htargetIndex' : replacedPositions
            (Fin.cast
              (source.replaceAt_length sourceIndex sourceReplacement).symm
              sourceIndex) =
            Fin.cast
              (target.replaceAt_length targetIndex targetReplacement).symm
              targetIndex := by
          apply Fin.ext
          simpa [replacedPositions] using congrArg Fin.val mapped
        rw [htargetIndex',
          ItemSeq.get_replaceAt_same, ItemSeq.get_replaceAt_same]
        exact replacement
      · have htarget : positions original ≠ targetIndex := by
          intro heq
          apply hindex
          exact positions.injective (heq.trans hmapped.symm)
        have hsourceIndex : index = Fin.cast
            (source.replaceAt_length sourceIndex sourceReplacement).symm
            original := by
          apply Fin.ext
          rfl
        have htargetIndex : replacedPositions index = Fin.cast
            (target.replaceAt_length targetIndex targetReplacement).symm
            (positions original) := by
          apply Fin.ext
          rfl
        rw [hsourceIndex]
        have htargetIndex' : replacedPositions
            (Fin.cast
              (source.replaceAt_length sourceIndex sourceReplacement).symm
              original) =
            Fin.cast
              (target.replaceAt_length targetIndex targetReplacement).symm
              (positions original) := by
          apply Fin.ext
          rfl
        rw [htargetIndex',
          ItemSeq.get_replaceAt_of_ne source sourceIndex original
            sourceReplacement hindex,
          ItemSeq.get_replaceAt_of_ne target targetIndex (positions original)
            targetReplacement htarget]
        simpa using itemIsos original hindex

/-- A proof-relevant permutation of a compiler frame with one distinguished
position omitted.  The omitted item is supplied by the recursively aligned
child, so siblings may move freely without assuming the subtree currently in
the hole is already isomorphic. -/
structure ItemSeqIso.Frame
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (sourceIndex : Fin source.length) (targetIndex : Fin target.length) where
  positions : FiniteEquiv (Fin source.length) (Fin target.length)
  mapped : positions sourceIndex = targetIndex
  siblings : ∀ index, index ≠ sourceIndex →
    ItemIso signature wire rels
      (source.get index) (target.get (positions index))

theorem ItemSeqIso.Frame.replaceAt
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceIndex : Fin source.length} {targetIndex : Fin target.length}
    (frame : ItemSeqIso.Frame wire sourceIndex targetIndex)
    (sourceReplacement : Item signature sourceWires rels)
    (targetReplacement : Item signature targetWires rels)
    (replacement : ItemIso signature wire rels sourceReplacement
      targetReplacement) :
    ItemSeqIso signature wire rels
      (source.replaceAt sourceIndex sourceReplacement)
      (target.replaceAt targetIndex targetReplacement) :=
  ItemSeqIso.replaceAt frame.positions sourceIndex targetIndex frame.siblings
    sourceReplacement targetReplacement frame.mapped replacement

/-- Change only the definitional presentation of a frame's wire equivalence. -/
def ItemSeqIso.Frame.castWire
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    {first second : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceIndex : Fin source.length} {targetIndex : Fin target.length}
    (equality : first = second)
    (frame : ItemSeqIso.Frame first sourceIndex targetIndex) :
    ItemSeqIso.Frame second sourceIndex targetIndex := by
  subst second
  exact frame

private def RegionIsoReflMotive {signature : List Nat}
    {wires : Nat} (rels : RelCtx) (region : Region signature wires rels) : Prop :=
  RegionIso signature (FiniteEquiv.refl (Fin wires)) rels region region

private def ItemIsoReflMotive {signature : List Nat}
    {wires : Nat} (rels : RelCtx) (item : Item signature wires rels) : Prop :=
  ItemIso signature (FiniteEquiv.refl (Fin wires)) rels item item

private def ItemSeqIsoReflMotive {signature : List Nat}
    {wires : Nat} (rels : RelCtx) (items : ItemSeq signature wires rels) : Prop :=
  forall i, ItemIso signature (FiniteEquiv.refl (Fin wires)) rels
    (items.get i) (items.get i)

private theorem regionIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx}
    (localWires : Nat)
    (items : ItemSeq signature (wires + localWires) rels)
    (itemsIH : ItemSeqIsoReflMotive rels items) :
    RegionIsoReflMotive rels (.mk localWires items) := by
  refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
  have extended_refl :
      extendWireEquiv (FiniteEquiv.refl (Fin wires))
          (FiniteEquiv.refl (Fin localWires)) =
        FiniteEquiv.refl (Fin (wires + localWires)) := by
    apply FiniteEquiv.ext
    intro i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp [extendWireEquiv, FiniteEquiv.refl]
  rw [extended_refl]
  refine ItemSeqIso.permute (FiniteEquiv.refl (Fin items.length)) ?_
  intro i
  simpa only [FiniteEquiv.refl_apply] using itemsIH i

private theorem equationIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx}
    (output : Fin wires) (term : Lambda.Term 0 (Fin wires)) :
    ItemIsoReflMotive (signature := signature) rels (.equation output term) := by
  apply ItemIso.equation
  · rfl
  · exact Lambda.Term.mapFree_id term

private theorem atomIsoReflCase
    {signature : List Nat} {wires arity : Nat} {rels : RelCtx}
    (relation : RelVar rels arity) (arguments : Fin arity -> Fin wires) :
    ItemIsoReflMotive (signature := signature) rels (.atom relation arguments) := by
  apply ItemIso.atom relation
  funext i
  rfl

private theorem namedIsoReflCase
    {signature : List Nat} {wires arity : Nat} {rels : RelCtx}
    (relation : NamedRel signature arity) (arguments : Fin arity -> Fin wires) :
    ItemIsoReflMotive rels (.named relation arguments) := by
  apply ItemIso.named relation
  funext i
  rfl

private theorem cutIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx}
    (body : Region signature wires rels) (bodyIH : RegionIsoReflMotive rels body) :
    ItemIsoReflMotive (signature := signature) rels (.cut body) :=
  ItemIso.cut bodyIH

private theorem bubbleIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx}
    (arity : Nat)
    (body : Region signature wires (arity :: rels))
    (bodyIH : RegionIsoReflMotive (arity :: rels) body) :
    ItemIsoReflMotive (signature := signature) rels (.bubble arity body) :=
  ItemIso.bubble bodyIH

private theorem nilIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx} :
    ItemSeqIsoReflMotive (signature := signature) rels
      (ItemSeq.nil : ItemSeq signature wires rels) := by
  intro i
  exact Fin.elim0 i

private theorem consIsoReflCase
    {signature : List Nat} {wires : Nat} {rels : RelCtx}
    (item : Item signature wires rels) (tail : ItemSeq signature wires rels)
    (itemIH : ItemIsoReflMotive rels item)
    (tailIH : ItemSeqIsoReflMotive rels tail) :
    ItemSeqIsoReflMotive rels (.cons item tail) := by
  intro i
  refine Fin.cases itemIH (fun j => ?_) i
  exact tailIH j

private theorem regionIsoReflRec
    (region : Region signature wires rels) : RegionIsoReflMotive rels region := by
  apply Region.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase equationIsoReflCase atomIsoReflCase namedIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase region

private theorem itemIsoReflRec
    (item : Item signature wires rels) : ItemIsoReflMotive rels item := by
  apply Item.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase equationIsoReflCase atomIsoReflCase namedIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase item

private theorem itemSeqIsoReflRec
    (items : ItemSeq signature wires rels) :
    ItemSeqIsoReflMotive rels items := by
  apply ItemSeq.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase equationIsoReflCase atomIsoReflCase namedIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase items

theorem RegionIso.refl (region : Region signature wires rels) :
    RegionIso signature (FiniteEquiv.refl (Fin wires)) rels region region :=
  regionIsoReflRec region

theorem ItemIso.refl (item : Item signature wires rels) :
    ItemIso signature (FiniteEquiv.refl (Fin wires)) rels item item :=
  itemIsoReflRec item

theorem ItemSeqIso.refl (items : ItemSeq signature wires rels) :
    ItemSeqIso signature (FiniteEquiv.refl (Fin wires)) rels items items :=
  ItemSeqIso.permute (FiniteEquiv.refl (Fin items.length))
    (itemSeqIsoReflRec items)

private def RegionIsoSymmMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Region signature sourceWires rels)
    (target : Region signature targetWires rels)
    (_ : RegionIso signature wire rels source target) : Prop :=
  RegionIso signature wire.symm rels target source

private def ItemIsoSymmMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Item signature sourceWires rels)
    (target : Item signature targetWires rels)
    (_ : ItemIso signature wire rels source target) : Prop :=
  ItemIso signature wire.symm rels target source

private def ItemSeqIsoSymmMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : ItemSeq signature sourceWires rels)
    (target : ItemSeq signature targetWires rels)
    (_ : ItemSeqIso signature wire rels source target) : Prop :=
  ItemSeqIso signature wire.symm rels target source

private theorem extendWireEquiv_symm
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)) :
    (extendWireEquiv outer localEquiv).symm =
      extendWireEquiv outer.symm localEquiv.symm := by
  apply FiniteEquiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> rfl

private theorem regionIsoSymmCase
    {signature : List Nat}
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqIso signature (extendWireEquiv ambient localEquiv) rels
      sourceItems targetItems)
    (itemsIH : ItemSeqIsoSymmMotive (extendWireEquiv ambient localEquiv)
      rels sourceItems targetItems items) :
    RegionIsoSymmMotive ambient rels
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      (.mk localEquiv items) := by
  refine RegionIso.mk localEquiv.symm ?_
  rw [← extendWireEquiv_symm]
  exact itemsIH

private theorem equationIsoSymmCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
    {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
    {targetTerm : Lambda.Term 0 (Fin targetWires)}
    (output_eq : ambient sourceOutput = targetOutput)
    (term_eq : sourceTerm.mapFree ambient = targetTerm) :
    ItemIsoSymmMotive (signature := signature) ambient rels
      (.equation (signature := signature) sourceOutput sourceTerm)
      (.equation (signature := signature) targetOutput targetTerm)
      (.equation (signature := signature) output_eq term_eq) := by
  apply ItemIso.equation (signature := signature)
  · simpa [output_eq] using ambient.left_inv sourceOutput
  · subst targetTerm
    rw [Lambda.Term.mapFree_comp]
    have inverse_comp : ambient.symm.toFun ∘ ambient.toFun = id := by
      funext i
      exact ambient.left_inv i
    rw [inverse_comp, Lambda.Term.mapFree_id]

private theorem atomIsoSymmCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx} (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoSymmMotive (signature := signature) ambient rels
      (.atom (signature := signature) relation sourceArguments)
      (.atom (signature := signature) relation targetArguments)
      (.atom (signature := signature) relation arguments_eq) := by
  apply ItemIso.atom (signature := signature) relation
  funext i
  rw [← arguments_eq]
  exact ambient.left_inv (sourceArguments i)

private theorem namedIsoSymmCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx} (relation : NamedRel signature arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoSymmMotive ambient rels (.named relation sourceArguments)
      (.named relation targetArguments) (.named relation arguments_eq) := by
  apply ItemIso.named relation
  funext i
  rw [← arguments_eq]
  exact ambient.left_inv (sourceArguments i)

private theorem cutIsoSymmCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceBody : Region signature sourceWires rels}
    {targetBody : Region signature targetWires rels}
    (body : RegionIso signature ambient rels sourceBody targetBody)
    (bodyIH : RegionIsoSymmMotive ambient rels sourceBody targetBody body) :
    ItemIsoSymmMotive ambient rels (.cut sourceBody) (.cut targetBody)
      (.cut body) :=
  ItemIso.cut bodyIH

private theorem bubbleIsoSymmCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {targetBody : Region signature targetWires (arity :: rels)}
    (body : RegionIso signature ambient (arity :: rels) sourceBody targetBody)
    (bodyIH : RegionIsoSymmMotive ambient (arity :: rels)
      sourceBody targetBody body) :
    ItemIsoSymmMotive ambient rels (.bubble arity sourceBody)
      (.bubble arity targetBody) (.bubble body) :=
  ItemIso.bubble bodyIH

private theorem permuteIsoSymmCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : forall i, ItemIso signature ambient rels
      (source.get i) (target.get (positions i)))
    (itemsIH : forall i, ItemIsoSymmMotive ambient rels
      (source.get i) (target.get (positions i)) (items i)) :
    ItemSeqIsoSymmMotive ambient rels source target (.permute positions items) := by
  refine ItemSeqIso.permute positions.symm ?_
  intro i
  simpa only [positions.right_inv] using itemsIH (positions.invFun i)

private theorem regionIsoSymmRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target) :
    RegionIsoSymmMotive wire rels source target iso := by
  apply RegionIso.rec
    (motive_1 := RegionIsoSymmMotive)
    (motive_2 := ItemIsoSymmMotive)
    (motive_3 := ItemSeqIsoSymmMotive)
    regionIsoSymmCase equationIsoSymmCase atomIsoSymmCase namedIsoSymmCase
    cutIsoSymmCase bubbleIsoSymmCase permuteIsoSymmCase iso

private theorem itemSeqIsoSymmRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (iso : ItemSeqIso signature wire rels source target) :
    ItemSeqIsoSymmMotive wire rels source target iso := by
  apply ItemSeqIso.rec
    (motive_1 := RegionIsoSymmMotive)
    (motive_2 := ItemIsoSymmMotive)
    (motive_3 := ItemSeqIsoSymmMotive)
    regionIsoSymmCase equationIsoSymmCase atomIsoSymmCase namedIsoSymmCase
    cutIsoSymmCase bubbleIsoSymmCase permuteIsoSymmCase iso

theorem RegionIso.symm
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target) :
    RegionIso signature wire.symm rels target source :=
  regionIsoSymmRec iso

theorem ItemSeqIso.symm
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (iso : ItemSeqIso signature wire rels source target) :
    ItemSeqIso signature wire.symm rels target source :=
  itemSeqIsoSymmRec iso

private def RegionIsoTransMotive {signature : List Nat}
    {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : Region signature sourceWires rels)
    (middle : Region signature middleWires rels)
    (_ : RegionIso signature firstWire rels source middle) : Prop :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : Region signature targetWires rels},
    RegionIso signature secondWire rels middle target ->
      RegionIso signature (firstWire.trans secondWire) rels source target

private def ItemIsoTransMotive {signature : List Nat}
    {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : Item signature sourceWires rels)
    (middle : Item signature middleWires rels)
    (_ : ItemIso signature firstWire rels source middle) : Prop :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : Item signature targetWires rels},
    ItemIso signature secondWire rels middle target ->
      ItemIso signature (firstWire.trans secondWire) rels source target

private def ItemSeqIsoTransMotive {signature : List Nat}
    {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : ItemSeq signature sourceWires rels)
    (middle : ItemSeq signature middleWires rels)
    (_ : ItemSeqIso signature firstWire rels source middle) : Prop :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : ItemSeq signature targetWires rels},
    ItemSeqIso signature secondWire rels middle target ->
      ItemSeqIso signature (firstWire.trans secondWire) rels source target

private theorem extendWireEquiv_trans
    (firstOuter : FiniteEquiv (Fin sourceOuter) (Fin middleOuter))
    (secondOuter : FiniteEquiv (Fin middleOuter) (Fin targetOuter))
    (firstLocal : FiniteEquiv (Fin sourceLocal) (Fin middleLocal))
    (secondLocal : FiniteEquiv (Fin middleLocal) (Fin targetLocal)) :
    (extendWireEquiv firstOuter firstLocal).trans
        (extendWireEquiv secondOuter secondLocal) =
      extendWireEquiv (firstOuter.trans secondOuter)
        (firstLocal.trans secondLocal) := by
  apply FiniteEquiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [FiniteEquiv.trans, extendWireEquiv]

private theorem regionIsoTransCase
    {signature : List Nat}
    {sourceWires middleWires sourceLocal middleLocal : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
    {middleItems : ItemSeq signature (middleWires + middleLocal) rels}
    (firstLocal : FiniteEquiv (Fin sourceLocal) (Fin middleLocal))
    (firstItems : ItemSeqIso signature
      (extendWireEquiv firstWire firstLocal) rels sourceItems middleItems)
    (itemsIH : ItemSeqIsoTransMotive
      (extendWireEquiv firstWire firstLocal) rels
      sourceItems middleItems firstItems) :
    RegionIsoTransMotive firstWire rels
      (.mk sourceLocal sourceItems) (.mk middleLocal middleItems)
      (.mk firstLocal firstItems) := by
  intro targetWires secondWire target second
  cases second with
  | mk secondLocal secondItems =>
      refine RegionIso.mk (firstLocal.trans secondLocal) ?_
      rw [← extendWireEquiv_trans]
      exact itemsIH secondItems

private theorem equationIsoTransCase
    {signature : List Nat} {sourceWires middleWires : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceOutput : Fin sourceWires} {middleOutput : Fin middleWires}
    {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
    {middleTerm : Lambda.Term 0 (Fin middleWires)}
    (firstOutput : firstWire sourceOutput = middleOutput)
    (firstTerm : sourceTerm.mapFree firstWire = middleTerm) :
    ItemIsoTransMotive (signature := signature) firstWire rels
      (.equation (signature := signature) sourceOutput sourceTerm)
      (.equation (signature := signature) middleOutput middleTerm)
      (.equation (signature := signature) firstOutput firstTerm) := by
  intro targetWires secondWire target second
  cases second with
  | equation secondOutput secondTerm =>
      apply ItemIso.equation (signature := signature)
      · exact (congrArg secondWire firstOutput).trans secondOutput
      · calc
          sourceTerm.mapFree (firstWire.trans secondWire) =
              (sourceTerm.mapFree firstWire).mapFree secondWire := by
                rw [Lambda.Term.mapFree_comp]
                rfl
          _ = middleTerm.mapFree secondWire :=
            congrArg (fun term => term.mapFree secondWire) firstTerm
          _ = _ := secondTerm

private theorem atomIsoTransCase
    {signature : List Nat} {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx} (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {middleArguments : Fin arity -> Fin middleWires}
    (firstArguments : firstWire.toFun ∘ sourceArguments = middleArguments) :
    ItemIsoTransMotive (signature := signature) firstWire rels
      (.atom (signature := signature) relation sourceArguments)
      (.atom (signature := signature) relation middleArguments)
      (.atom (signature := signature) relation firstArguments) := by
  intro targetWires secondWire target second
  cases second with
  | atom _ secondArguments =>
      apply ItemIso.atom (signature := signature) relation
      calc
        (firstWire.trans secondWire).toFun ∘ sourceArguments =
            secondWire.toFun ∘ (firstWire.toFun ∘ sourceArguments) := rfl
        _ = secondWire.toFun ∘ middleArguments :=
          congrArg (Function.comp secondWire.toFun) firstArguments
        _ = _ := secondArguments

private theorem namedIsoTransCase
    {signature : List Nat} {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx} (relation : NamedRel signature arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {middleArguments : Fin arity -> Fin middleWires}
    (firstArguments : firstWire.toFun ∘ sourceArguments = middleArguments) :
    ItemIsoTransMotive firstWire rels (.named relation sourceArguments)
      (.named relation middleArguments) (.named relation firstArguments) := by
  intro targetWires secondWire target second
  cases second with
  | named _ secondArguments =>
      apply ItemIso.named relation
      calc
        (firstWire.trans secondWire).toFun ∘ sourceArguments =
            secondWire.toFun ∘ (firstWire.toFun ∘ sourceArguments) := rfl
        _ = secondWire.toFun ∘ middleArguments :=
          congrArg (Function.comp secondWire.toFun) firstArguments
        _ = _ := secondArguments

private theorem cutIsoTransCase
    {signature : List Nat} {sourceWires middleWires : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceBody : Region signature sourceWires rels}
    {middleBody : Region signature middleWires rels}
    (firstBody : RegionIso signature firstWire rels sourceBody middleBody)
    (bodyIH : RegionIsoTransMotive firstWire rels
      sourceBody middleBody firstBody) :
    ItemIsoTransMotive firstWire rels (.cut sourceBody) (.cut middleBody)
      (.cut firstBody) := by
  intro targetWires secondWire target second
  cases second with
  | cut secondBody => exact ItemIso.cut (bodyIH secondBody)

private theorem bubbleIsoTransCase
    {signature : List Nat} {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {middleBody : Region signature middleWires (arity :: rels)}
    (firstBody : RegionIso signature firstWire (arity :: rels)
      sourceBody middleBody)
    (bodyIH : RegionIsoTransMotive firstWire (arity :: rels)
      sourceBody middleBody firstBody) :
    ItemIsoTransMotive firstWire rels (.bubble arity sourceBody)
      (.bubble arity middleBody) (.bubble firstBody) := by
  intro targetWires secondWire target second
  cases second with
  | bubble secondBody => exact ItemIso.bubble (bodyIH secondBody)

private theorem permuteIsoTransCase
    {signature : List Nat} {sourceWires middleWires : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {middle : ItemSeq signature middleWires rels}
    (firstPositions : FiniteEquiv (Fin source.length) (Fin middle.length))
    (firstItems : forall i, ItemIso signature firstWire rels
      (source.get i) (middle.get (firstPositions i)))
    (itemsIH : forall i, ItemIsoTransMotive firstWire rels
      (source.get i) (middle.get (firstPositions i)) (firstItems i)) :
    ItemSeqIsoTransMotive firstWire rels source middle
      (.permute firstPositions firstItems) := by
  intro targetWires secondWire target second
  cases second with
  | permute secondPositions secondItems =>
      refine ItemSeqIso.permute (firstPositions.trans secondPositions) ?_
      intro i
      exact itemsIH i (secondItems (firstPositions i))

private theorem regionIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : Region signature sourceWires rels}
    {middle : Region signature middleWires rels}
    (first : RegionIso signature firstWire rels source middle) :
    RegionIsoTransMotive firstWire rels source middle first := by
  unfold RegionIsoTransMotive
  intro targetWires secondWire target second
  exact RegionIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase equationIsoTransCase atomIsoTransCase namedIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

private theorem itemSeqIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : ItemSeq signature sourceWires rels}
    {middle : ItemSeq signature middleWires rels}
    (first : ItemSeqIso signature firstWire rels source middle) :
    ItemSeqIsoTransMotive firstWire rels source middle first := by
  unfold ItemSeqIsoTransMotive
  intro targetWires secondWire target second
  exact ItemSeqIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase equationIsoTransCase atomIsoTransCase namedIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

private theorem itemIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : Item signature sourceWires rels}
    {middle : Item signature middleWires rels}
    (first : ItemIso signature firstWire rels source middle) :
    ItemIsoTransMotive firstWire rels source middle first := by
  unfold ItemIsoTransMotive
  intro targetWires secondWire target second
  exact ItemIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase equationIsoTransCase atomIsoTransCase namedIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

theorem RegionIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : Region signature sourceWires rels}
    {middle : Region signature middleWires rels}
    {target : Region signature targetWires rels}
    (first : RegionIso signature firstWire rels source middle)
    (second : RegionIso signature secondWire rels middle target) :
    RegionIso signature (firstWire.trans secondWire) rels source target :=
  regionIsoTransRec first second

theorem ItemIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : Item signature sourceWires rels}
    {middle : Item signature middleWires rels}
    {target : Item signature targetWires rels}
    (first : ItemIso signature firstWire rels source middle)
    (second : ItemIso signature secondWire rels middle target) :
    ItemIso signature (firstWire.trans secondWire) rels source target :=
  itemIsoTransRec first second

theorem ItemSeqIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : ItemSeq signature sourceWires rels}
    {middle : ItemSeq signature middleWires rels}
    {target : ItemSeq signature targetWires rels}
    (first : ItemSeqIso signature firstWire rels source middle)
    (second : ItemSeqIso signature secondWire rels middle target) :
    ItemSeqIso signature (firstWire.trans secondWire) rels source target :=
  itemSeqIsoTransRec first second

theorem denoteItemSeq_iff_get
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (items : ItemSeq signature wires relCtx) :
    denoteItemSeq model named env rels items <->
      forall i, denoteItem model named env rels (items.get i) := by
  cases items with
  | nil =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        trivial
  | cons head tail =>
      have ih := denoteItemSeq_iff_get model named env rels tail
      constructor
      · rintro ⟨hhead, htail⟩ index
        refine Fin.cases hhead (fun i => ?_) index
        exact ih.mp htail i
      · intro hall
        constructor
        · exact hall ⟨0, by simp [ItemSeq.length]⟩
        · apply ih.mpr
          intro i
          exact hall i.succ

private def RegionDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Region signature sourceWires rels)
    (right : Region signature targetWires rels)
    (_ : RegionIso signature wire rels left right) : Prop :=
  forall (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteRegion model named sourceEnv relEnv left <->
        denoteRegion model named targetEnv relEnv right)

private def ItemDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Item signature sourceWires rels)
    (right : Item signature targetWires rels)
    (_ : ItemIso signature wire rels left right) : Prop :=
  forall (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteItem model named sourceEnv relEnv left <->
        denoteItem model named targetEnv relEnv right)

private def ItemSeqDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : ItemSeq signature sourceWires rels)
    (right : ItemSeq signature targetWires rels)
    (_ : ItemSeqIso signature wire rels left right) : Prop :=
  forall (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteItemSeq model named sourceEnv relEnv left <->
        denoteItemSeq model named targetEnv relEnv right)

private theorem regionDenotationCase
    {signature : List Nat}
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqIso signature (extendWireEquiv wire localEquiv) rels
      sourceItems targetItems)
    (itemsIH : ItemSeqDenotationMotive (extendWireEquiv wire localEquiv)
      rels sourceItems targetItems items) :
    RegionDenotationMotive wire rels
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      (.mk localEquiv items) := by
  intro model named sourceEnv targetEnv relEnv henv
  constructor
  · rintro ⟨sourceLocalEnv, hitems⟩
    let targetLocalEnv := fun i => sourceLocalEnv (localEquiv.invFun i)
    refine ⟨targetLocalEnv, ?_⟩
    apply (itemsIH model named
      (extendWireEnv sourceEnv sourceLocalEnv)
      (extendWireEnv targetEnv targetLocalEnv) relEnv ?_).mp hitems
    apply extendWireEnv_agree wire localEquiv
    · exact henv
    · intro i
      simp [targetLocalEnv, localEquiv.left_inv]
  · rintro ⟨targetLocalEnv, hitems⟩
    let sourceLocalEnv := fun i => targetLocalEnv (localEquiv i)
    refine ⟨sourceLocalEnv, ?_⟩
    apply (itemsIH model named
      (extendWireEnv sourceEnv sourceLocalEnv)
      (extendWireEnv targetEnv targetLocalEnv) relEnv ?_).mpr hitems
    apply extendWireEnv_agree wire localEquiv
    · exact henv
    · intro _
      rfl

private theorem equationDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
    {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
    {targetTerm : Lambda.Term 0 (Fin targetWires)}
    (output_eq : wire sourceOutput = targetOutput)
    (term_eq : sourceTerm.mapFree wire = targetTerm) :
    ItemDenotationMotive (signature := signature) wire rels
      (.equation sourceOutput sourceTerm) (.equation targetOutput targetTerm)
      (.equation output_eq term_eq) := by
  intro model named sourceEnv targetEnv relEnv henv
  subst targetOutput
  subst targetTerm
  have env_eq : targetEnv ∘ wire.toFun = sourceEnv := funext henv
  simp only [denoteItem]
  rw [model.eval_mapFree wire.toFun, env_eq, henv]

private theorem atomDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemDenotationMotive (signature := signature) wire rels
      (.atom relation sourceArguments) (.atom relation targetArguments)
      (.atom (signature := signature) relation arguments_eq) := by
  intro model named sourceEnv targetEnv relEnv henv
  subst targetArguments
  have arguments_env_eq :
      targetEnv ∘ (wire.toFun ∘ sourceArguments) =
        sourceEnv ∘ sourceArguments := by
    funext i
    exact henv (sourceArguments i)
  simp only [denoteItem]
  rw [arguments_env_eq]

private theorem namedDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    (relation : NamedRel signature arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemDenotationMotive wire rels
      (.named relation sourceArguments) (.named relation targetArguments)
      (.named relation arguments_eq) := by
  intro model named sourceEnv targetEnv relEnv henv
  subst targetArguments
  have arguments_env_eq :
      targetEnv ∘ (wire.toFun ∘ sourceArguments) =
        sourceEnv ∘ sourceArguments := by
    funext i
    exact henv (sourceArguments i)
  simp only [denoteItem]
  rw [arguments_env_eq]

private theorem cutDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region signature sourceWires rels}
    {targetBody : Region signature targetWires rels}
    (body : RegionIso signature wire rels sourceBody targetBody)
    (bodyIH : RegionDenotationMotive wire rels sourceBody targetBody body) :
    ItemDenotationMotive wire rels (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro model named sourceEnv targetEnv relEnv henv
  constructor
  · intro hsource htarget
    exact hsource ((bodyIH model named sourceEnv targetEnv relEnv henv).mpr htarget)
  · intro htarget hsource
    exact htarget ((bodyIH model named sourceEnv targetEnv relEnv henv).mp hsource)

private theorem bubbleDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {targetBody : Region signature targetWires (arity :: rels)}
    (body : RegionIso signature wire (arity :: rels) sourceBody targetBody)
    (bodyIH : RegionDenotationMotive wire (arity :: rels)
      sourceBody targetBody body) :
    ItemDenotationMotive wire rels
      (.bubble arity sourceBody) (.bubble arity targetBody) (.bubble body) := by
  intro model named sourceEnv targetEnv relEnv henv
  constructor
  · rintro ⟨relation, hsource⟩
    exact ⟨relation, (bodyIH model named sourceEnv targetEnv
      (relation, relEnv) henv).mp hsource⟩
  · rintro ⟨relation, htarget⟩
    exact ⟨relation, (bodyIH model named sourceEnv targetEnv
      (relation, relEnv) henv).mpr htarget⟩

private theorem permuteDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : forall i, ItemIso signature wire rels
      (source.get i) (target.get (positions i)))
    (itemsIH : forall i, ItemDenotationMotive wire rels
      (source.get i) (target.get (positions i)) (items i)) :
    ItemSeqDenotationMotive wire rels source target (.permute positions items) := by
  intro model named sourceEnv targetEnv relEnv henv
  rw [denoteItemSeq_iff_get, denoteItemSeq_iff_get]
  constructor
  · intro hsource targetIndex
    have hitem := (itemsIH (positions.invFun targetIndex) model named
      sourceEnv targetEnv relEnv henv).mp
        (hsource (positions.invFun targetIndex))
    simpa only [positions.right_inv] using hitem
  · intro htarget sourceIndex
    exact (itemsIH sourceIndex model named sourceEnv targetEnv relEnv henv).mpr
      (htarget (positions sourceIndex))

private theorem regionDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region signature sourceWires rels}
    {right : Region signature targetWires rels}
    (hiso : RegionIso signature wire rels left right) :
    RegionDenotationMotive wire rels left right hiso := by
  apply RegionIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase equationDenotationCase atomDenotationCase
    namedDenotationCase cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

private theorem itemDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item signature sourceWires rels}
    {right : Item signature targetWires rels}
    (hiso : ItemIso signature wire rels left right) :
    ItemDenotationMotive wire rels left right hiso := by
  apply ItemIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase equationDenotationCase atomDenotationCase
    namedDenotationCase cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

private theorem itemSeqDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq signature sourceWires rels}
    {right : ItemSeq signature targetWires rels}
    (hiso : ItemSeqIso signature wire rels left right) :
    ItemSeqDenotationMotive wire rels left right hiso := by
  apply ItemSeqIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase equationDenotationCase atomDenotationCase
    namedDenotationCase cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

theorem RegionIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region signature sourceWires rels}
    {right : Region signature targetWires rels}
    (hiso : RegionIso signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteRegion model named sourceEnv relEnv left <->
      denoteRegion model named targetEnv relEnv right :=
  regionDenotationRec hiso model named sourceEnv targetEnv relEnv henv

theorem ItemIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item signature sourceWires rels}
    {right : Item signature targetWires rels}
    (hiso : ItemIso signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItem model named sourceEnv relEnv left <->
      denoteItem model named targetEnv relEnv right :=
  itemDenotationRec hiso model named sourceEnv targetEnv relEnv henv

theorem ItemSeqIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq signature sourceWires rels}
    {right : ItemSeq signature targetWires rels}
    (hiso : ItemSeqIso signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItemSeq model named sourceEnv relEnv left <->
      denoteItemSeq model named targetEnv relEnv right :=
  itemSeqDenotationRec hiso model named sourceEnv targetEnv relEnv henv

namespace Core

def Isomorphic (left right : Region signature wires rels) : Prop :=
  RegionIso signature (FiniteEquiv.refl (Fin wires)) rels left right

end Core

theorem iso_denotation
    {left right : Region signature wires rels}
    (hiso : Core.Isomorphic left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (env : Fin wires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named env relEnv left <->
      denoteRegion model named env relEnv right :=
  hiso.denotation model named env env relEnv (fun _ => rfl)

namespace IsomorphismExamples

def swapFinTwo : FiniteEquiv (Fin 2) (Fin 2) where
  toFun i := ⟨1 - i.val, by omega⟩
  invFun i := ⟨1 - i.val, by omega⟩
  left_inv := by
    intro i
    have hi : i = 0 \/ i = 1 := by omega
    rcases hi with rfl | rfl <;> rfl
  right_inv := by
    intro i
    have hi : i = 0 \/ i = 1 := by omega
    rcases hi with rfl | rfl <;> rfl

def twoItemSwapSource : Region [] 0 [] :=
  .mk 1 (.cons (.equation 0 (.port 0))
    (.cons (.equation 0 (.app (.port 0) (.port 0))) .nil))

def twoItemSwapTarget : Region [] 0 [] :=
  .mk 1 (.cons (.equation 0 (.app (.port 0) (.port 0)))
    (.cons (.equation 0 (.port 0)) .nil))

theorem twoItemSwap_isomorphic :
    Core.Isomorphic twoItemSwapSource twoItemSwapTarget := by
  unfold Core.Isomorphic twoItemSwapSource twoItemSwapTarget
  refine RegionIso.mk (FiniteEquiv.refl (Fin 1)) ?_
  refine ItemSeqIso.permute (by
    simpa [ItemSeq.length] using swapFinTwo) ?_
  intro i
  change Fin 2 at i
  have hi : i = 0 \/ i = 1 := by omega
  rcases hi with rfl | rfl
  · apply ItemIso.equation
    · apply Fin.ext
      rfl
    · rfl
  · apply ItemIso.equation
    · apply Fin.ext
      rfl
    · rfl

theorem twoItemSwap_denotation
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier [])
    (env : Fin 0 -> model.Carrier) (relEnv : RelEnv model.Carrier []) :
    denoteRegion model named env relEnv twoItemSwapSource <->
      denoteRegion model named env relEnv twoItemSwapTarget :=
  iso_denotation twoItemSwap_isomorphic model named env relEnv

def twoLocalWireSwapSource : Region [] 0 [] :=
  .mk 2 (.cons (.equation 0 (.port 1)) .nil)

def twoLocalWireSwapTarget : Region [] 0 [] :=
  .mk 2 (.cons (.equation 1 (.port 0)) .nil)

theorem twoLocalWireSwap_isomorphic :
    Core.Isomorphic twoLocalWireSwapSource twoLocalWireSwapTarget := by
  unfold Core.Isomorphic twoLocalWireSwapSource twoLocalWireSwapTarget
  refine RegionIso.mk swapFinTwo ?_
  refine ItemSeqIso.permute (by
    simpa [ItemSeq.length] using FiniteEquiv.refl (Fin 1)) ?_
  intro i
  change Fin 1 at i
  have hi : i = 0 := by omega
  subst i
  apply ItemIso.equation
  · apply Fin.ext
    rfl
  · rfl

theorem twoLocalWireSwap_denotation
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier [])
    (env : Fin 0 -> model.Carrier) (relEnv : RelEnv model.Carrier []) :
    denoteRegion model named env relEnv twoLocalWireSwapSource <->
      denoteRegion model named env relEnv twoLocalWireSwapTarget :=
  iso_denotation twoLocalWireSwap_isomorphic model named env relEnv

end IsomorphismExamples

end VisualProof.Diagram
