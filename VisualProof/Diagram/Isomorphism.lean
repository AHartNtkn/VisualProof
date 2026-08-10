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
  inductive RegionIso :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      Region  sourceWires rels ->
      Region  targetWires rels -> Type
    | mk {sourceWires targetWires sourceLocal targetLocal : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceItems : ItemSeq  (sourceWires + sourceLocal) rels}
        {targetItems : ItemSeq  (targetWires + targetLocal) rels}
        (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
        (items : ItemSeqIso  (extendWireEquiv ambient localEquiv) rels
          sourceItems targetItems) :
        RegionIso  ambient rels
          (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)

  inductive ItemIso :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      Item  sourceWires rels ->
      Item  targetWires rels -> Type
    | atom {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        (relation : RelVar rels arity)
        {sourceArguments : Fin arity -> Fin sourceWires}
        {targetArguments : Fin arity -> Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemIso  ambient rels
          (.atom relation sourceArguments) (.atom relation targetArguments)
    | identity {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceArguments : Fin arity -> Fin sourceWires}
        {targetArguments : Fin arity -> Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemIso  ambient rels
          (.identity arity sourceArguments) (.identity arity targetArguments)
    | cut {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region  sourceWires rels}
        {targetBody : Region  targetWires rels}
        (body : RegionIso  ambient rels sourceBody targetBody) :
        ItemIso  ambient rels (.cut sourceBody) (.cut targetBody)
    | bubble {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region  sourceWires (arity :: rels)}
        {targetBody : Region  targetWires (arity :: rels)}
        (body : RegionIso  ambient (arity :: rels)
          sourceBody targetBody) :
        ItemIso  ambient rels
          (.bubble arity sourceBody) (.bubble arity targetBody)

  inductive ItemSeqIso :
      {sourceWires targetWires : Nat} ->
      FiniteEquiv (Fin sourceWires) (Fin targetWires) ->
      (rels : RelCtx) ->
      ItemSeq  sourceWires rels ->
      ItemSeq  targetWires rels -> Type
    | permute {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {source : ItemSeq  sourceWires rels}
        {target : ItemSeq  targetWires rels}
        (positions : FiniteEquiv (Fin source.length) (Fin target.length))
        (items : forall i, ItemIso  ambient rels
          (source.get i) (target.get (positions i))) :
        ItemSeqIso  ambient rels source target
end

def RegionIso.localEquiv
    {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso ambient rels source target) :
    FiniteEquiv (Fin source.localCount) (Fin target.localCount) :=
  match iso with
  | .mk localEquiv _ => localEquiv

def RegionIso.localEquivCast
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso ambient rels source target)
    (sourceLocalEq : source.localCount = sourceLocal)
    (targetLocalEq : target.localCount = targetLocal) :
    FiniteEquiv (Fin sourceLocal) (Fin targetLocal) := by
  subst sourceLocal
  subst targetLocal
  exact iso.localEquiv

theorem RegionIso.localEquivCast_castEndpoints
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source source' : Region sourceWires rels}
    {target target' : Region targetWires rels}
    (iso : RegionIso ambient rels source target)
    (sourceEq : source = source')
    (targetEq : target = target')
    (sourceLocalEq : source.localCount = sourceLocal)
    (targetLocalEq : target.localCount = targetLocal)
    (sourceLocalEq' : source'.localCount = sourceLocal)
    (targetLocalEq' : target'.localCount = targetLocal) :
    let sourceIso := Eq.mp
      (congrArg (fun value => RegionIso ambient rels value target) sourceEq)
      iso
    let resultIso := Eq.mp
      (congrArg (fun value => RegionIso ambient rels source' value) targetEq)
      sourceIso
    resultIso.localEquivCast sourceLocalEq' targetLocalEq' =
      iso.localEquivCast sourceLocalEq targetLocalEq := by
  subst source'
  subst target'
  rfl


def ItemSeq.replaceAt :
    (items : ItemSeq  wires rels) →
    Fin items.length → Item  wires rels →
      ItemSeq  wires rels
  | .nil, index, _ => Fin.elim0 index
  | .cons head tail, index, replacement =>
      Fin.cases (.cons replacement tail)
        (fun rest => .cons head (ItemSeq.replaceAt tail rest replacement)) index

@[simp] theorem ItemSeq.replaceAt_length
    (items : ItemSeq  wires rels) (index : Fin items.length)
    (replacement : Item  wires rels) :
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
    (items : ItemSeq  wires rels) (index : Fin items.length)
    (replacement : Item  wires rels) :
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
    (items : ItemSeq  wires rels) (index other : Fin items.length)
    (replacement : Item  wires rels) (hne : other ≠ index) :
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

def ItemSeqIso.replaceAt
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (sourceIndex : Fin source.length) (targetIndex : Fin target.length)
    (itemIsos : ∀ i, i ≠ sourceIndex → ItemIso  wire rels
      (source.get i) (target.get (positions i)))
    (sourceReplacement : Item  sourceWires rels)
    (targetReplacement : Item  targetWires rels)
    (mapped : positions sourceIndex = targetIndex)
    (replacement : ItemIso  wire rels sourceReplacement
      targetReplacement) :
    ItemSeqIso  wire rels
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
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (sourceIndex : Fin source.length) (targetIndex : Fin target.length) where
  positions : FiniteEquiv (Fin source.length) (Fin target.length)
  mapped : positions sourceIndex = targetIndex
  siblings : ∀ index, index ≠ sourceIndex →
    ItemIso  wire rels
      (source.get index) (target.get (positions index))

def ItemSeqIso.Frame.replaceAt
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceIndex : Fin source.length} {targetIndex : Fin target.length}
    (frame : ItemSeqIso.Frame wire sourceIndex targetIndex)
    (sourceReplacement : Item  sourceWires rels)
    (targetReplacement : Item  targetWires rels)
    (replacement : ItemIso  wire rels sourceReplacement
      targetReplacement) :
    ItemSeqIso  wire rels
      (source.replaceAt sourceIndex sourceReplacement)
      (target.replaceAt targetIndex targetReplacement) :=
  ItemSeqIso.replaceAt frame.positions sourceIndex targetIndex frame.siblings
    sourceReplacement targetReplacement frame.mapped replacement

/-- Change only the definitional presentation of a frame's wire equivalence. -/
def ItemSeqIso.Frame.castWire
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    {first second : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceIndex : Fin source.length} {targetIndex : Fin target.length}
    (equality : first = second)
    (frame : ItemSeqIso.Frame first sourceIndex targetIndex) :
    ItemSeqIso.Frame second sourceIndex targetIndex := by
  subst second
  exact frame

private def RegionIsoReflMotive {wires : Nat} (rels : RelCtx) (region : Region  wires rels) : Type :=
  RegionIso  (FiniteEquiv.refl (Fin wires)) rels region region

private def ItemIsoReflMotive {wires : Nat} (rels : RelCtx) (item : Item  wires rels) : Type :=
  ItemIso  (FiniteEquiv.refl (Fin wires)) rels item item

private def ItemSeqIsoReflMotive {wires : Nat} (rels : RelCtx) (items : ItemSeq  wires rels) : Type :=
  forall i, ItemIso  (FiniteEquiv.refl (Fin wires)) rels
    (items.get i) (items.get i)

private def regionIsoReflCase
    {wires : Nat} {rels : RelCtx}
    (localWires : Nat)
    (items : ItemSeq  (wires + localWires) rels)
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

private def atomIsoReflCase
    {wires arity : Nat} {rels : RelCtx}
    (relation : RelVar rels arity) (arguments : Fin arity -> Fin wires) :
    ItemIsoReflMotive  rels (.atom relation arguments) := by
  apply ItemIso.atom relation
  funext i
  rfl


private def identityIsoReflCase
    {wires : Nat} {rels : RelCtx}
    (arity : Nat) (arguments : Fin arity -> Fin wires) :
    ItemIsoReflMotive  rels
      (.identity arity arguments) := by
  apply ItemIso.identity
  funext i
  rfl

private def cutIsoReflCase
    {wires : Nat} {rels : RelCtx}
    (body : Region  wires rels) (bodyIH : RegionIsoReflMotive rels body) :
    ItemIsoReflMotive  rels (.cut body) :=
  ItemIso.cut bodyIH

private def bubbleIsoReflCase
    {wires : Nat} {rels : RelCtx}
    (arity : Nat)
    (body : Region  wires (arity :: rels))
    (bodyIH : RegionIsoReflMotive (arity :: rels) body) :
    ItemIsoReflMotive  rels (.bubble arity body) :=
  ItemIso.bubble bodyIH

private def nilIsoReflCase
    {wires : Nat} {rels : RelCtx} :
    ItemSeqIsoReflMotive  rels
      (ItemSeq.nil : ItemSeq  wires rels) := by
  intro i
  exact Fin.elim0 i

private def consIsoReflCase
    {wires : Nat} {rels : RelCtx}
    (item : Item  wires rels) (tail : ItemSeq  wires rels)
    (itemIH : ItemIsoReflMotive rels item)
    (tailIH : ItemSeqIsoReflMotive rels tail) :
    ItemSeqIsoReflMotive rels (.cons item tail) := by
  intro i
  refine Fin.cases itemIH (fun j => ?_) i
  exact tailIH j

private noncomputable def regionIsoReflRec
    (region : Region  wires rels) : RegionIsoReflMotive rels region := by
  apply Region.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase atomIsoReflCase identityIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase region

private noncomputable def itemIsoReflRec
    (item : Item  wires rels) : ItemIsoReflMotive rels item := by
  apply Item.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase atomIsoReflCase identityIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase item

private noncomputable def itemSeqIsoReflRec
    (items : ItemSeq  wires rels) :
    ItemSeqIsoReflMotive rels items := by
  apply ItemSeq.rec
    (motive_1 := fun _ rels region => RegionIsoReflMotive rels region)
    (motive_2 := fun _ rels item => ItemIsoReflMotive rels item)
    (motive_3 := fun _ rels items => ItemSeqIsoReflMotive rels items)
    regionIsoReflCase atomIsoReflCase identityIsoReflCase
    cutIsoReflCase bubbleIsoReflCase nilIsoReflCase consIsoReflCase items

noncomputable def RegionIso.refl (region : Region  wires rels) :
    RegionIso  (FiniteEquiv.refl (Fin wires)) rels region region :=
  regionIsoReflRec region

noncomputable def ItemIso.refl (item : Item  wires rels) :
    ItemIso  (FiniteEquiv.refl (Fin wires)) rels item item :=
  itemIsoReflRec item

noncomputable def ItemSeqIso.refl (items : ItemSeq  wires rels) :
    ItemSeqIso  (FiniteEquiv.refl (Fin wires)) rels items items :=
  ItemSeqIso.permute (FiniteEquiv.refl (Fin items.length))
    (itemSeqIsoReflRec items)

private def RegionIsoSymmMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Region  sourceWires rels)
    (target : Region  targetWires rels)
    (_ : RegionIso  wire rels source target) : Type :=
  RegionIso  wire.symm rels target source

private def ItemIsoSymmMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Item  sourceWires rels)
    (target : Item  targetWires rels)
    (_ : ItemIso  wire rels source target) : Type :=
  ItemIso  wire.symm rels target source

private def ItemSeqIsoSymmMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : ItemSeq  sourceWires rels)
    (target : ItemSeq  targetWires rels)
    (_ : ItemSeqIso  wire rels source target) : Type :=
  ItemSeqIso  wire.symm rels target source

theorem extendWireEquiv_symm
    (outer : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)) :
    (extendWireEquiv outer localEquiv).symm =
      extendWireEquiv outer.symm localEquiv.symm := by
  apply FiniteEquiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> rfl

private def regionIsoSymmCase
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceItems : ItemSeq  (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq  (targetWires + targetLocal) rels}
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqIso  (extendWireEquiv ambient localEquiv) rels
      sourceItems targetItems)
    (itemsIH : ItemSeqIsoSymmMotive (extendWireEquiv ambient localEquiv)
      rels sourceItems targetItems items) :
    RegionIsoSymmMotive ambient rels
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      (.mk localEquiv items) := by
  refine RegionIso.mk localEquiv.symm ?_
  rw [← extendWireEquiv_symm]
  exact itemsIH

private def atomIsoSymmCase
    {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx} (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoSymmMotive  ambient rels
      (.atom  relation sourceArguments)
      (.atom  relation targetArguments)
      (.atom  relation arguments_eq) := by
  apply ItemIso.atom  relation
  funext i
  rw [← arguments_eq]
  exact ambient.left_inv (sourceArguments i)


private def identityIsoSymmCase
    {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoSymmMotive  ambient rels
      (.identity arity sourceArguments) (.identity arity targetArguments)
      (.identity arguments_eq) := by
  apply ItemIso.identity
  funext i
  rw [← arguments_eq]
  exact ambient.left_inv (sourceArguments i)

private def cutIsoSymmCase
    {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceBody : Region  sourceWires rels}
    {targetBody : Region  targetWires rels}
    (body : RegionIso  ambient rels sourceBody targetBody)
    (bodyIH : RegionIsoSymmMotive ambient rels sourceBody targetBody body) :
    ItemIsoSymmMotive ambient rels (.cut sourceBody) (.cut targetBody)
      (.cut body) :=
  ItemIso.cut bodyIH

private def bubbleIsoSymmCase
    {sourceWires targetWires arity : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {sourceBody : Region  sourceWires (arity :: rels)}
    {targetBody : Region  targetWires (arity :: rels)}
    (body : RegionIso  ambient (arity :: rels) sourceBody targetBody)
    (bodyIH : RegionIsoSymmMotive ambient (arity :: rels)
      sourceBody targetBody body) :
    ItemIsoSymmMotive ambient rels (.bubble arity sourceBody)
      (.bubble arity targetBody) (.bubble body) :=
  ItemIso.bubble bodyIH

private def permuteIsoSymmCase
    {sourceWires targetWires : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : forall i, ItemIso  ambient rels
      (source.get i) (target.get (positions i)))
    (itemsIH : forall i, ItemIsoSymmMotive ambient rels
      (source.get i) (target.get (positions i)) (items i)) :
    ItemSeqIsoSymmMotive ambient rels source target (.permute positions items) := by
  refine ItemSeqIso.permute positions.symm ?_
  intro i
  rw [← positions.right_inv i]
  change ItemIso ambient.symm rels
    (target.get (positions (positions.invFun i)))
    (source.get (positions.invFun (positions (positions.invFun i))))
  rw [positions.left_inv]
  exact itemsIH (positions.invFun i)

private noncomputable def regionIsoSymmRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region  sourceWires rels}
    {target : Region  targetWires rels}
    (iso : RegionIso  wire rels source target) :
    RegionIsoSymmMotive wire rels source target iso := by
  apply RegionIso.rec
    (motive_1 := RegionIsoSymmMotive)
    (motive_2 := ItemIsoSymmMotive)
    (motive_3 := ItemSeqIsoSymmMotive)
    regionIsoSymmCase atomIsoSymmCase identityIsoSymmCase
    cutIsoSymmCase bubbleIsoSymmCase permuteIsoSymmCase iso

private noncomputable def itemSeqIsoSymmRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (iso : ItemSeqIso  wire rels source target) :
    ItemSeqIsoSymmMotive wire rels source target iso := by
  apply ItemSeqIso.rec
    (motive_1 := RegionIsoSymmMotive)
    (motive_2 := ItemIsoSymmMotive)
    (motive_3 := ItemSeqIsoSymmMotive)
    regionIsoSymmCase atomIsoSymmCase identityIsoSymmCase
    cutIsoSymmCase bubbleIsoSymmCase permuteIsoSymmCase iso

private noncomputable def itemIsoSymmRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Item sourceWires rels}
    {target : Item targetWires rels}
    (iso : ItemIso wire rels source target) :
    ItemIsoSymmMotive wire rels source target iso := by
  apply ItemIso.rec
    (motive_1 := RegionIsoSymmMotive)
    (motive_2 := ItemIsoSymmMotive)
    (motive_3 := ItemSeqIsoSymmMotive)
    regionIsoSymmCase atomIsoSymmCase identityIsoSymmCase
    cutIsoSymmCase bubbleIsoSymmCase permuteIsoSymmCase iso

noncomputable def RegionIso.symm
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region  sourceWires rels}
    {target : Region  targetWires rels}
    (iso : RegionIso  wire rels source target) :
    RegionIso  wire.symm rels target source :=
  regionIsoSymmRec iso

noncomputable def ItemIso.symm
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Item sourceWires rels}
    {target : Item targetWires rels}
    (iso : ItemIso wire rels source target) :
    ItemIso wire.symm rels target source :=
  itemIsoSymmRec iso

noncomputable def ItemSeqIso.symm
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (iso : ItemSeqIso  wire rels source target) :
    ItemSeqIso  wire.symm rels target source :=
  itemSeqIsoSymmRec iso

private def RegionIsoTransMotive {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : Region  sourceWires rels)
    (middle : Region  middleWires rels)
    (_ : RegionIso  firstWire rels source middle) : Type :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : Region  targetWires rels},
    RegionIso  secondWire rels middle target ->
      RegionIso  (firstWire.trans secondWire) rels source target

private def ItemIsoTransMotive {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : Item  sourceWires rels)
    (middle : Item  middleWires rels)
    (_ : ItemIso  firstWire rels source middle) : Type :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : Item  targetWires rels},
    ItemIso  secondWire rels middle target ->
      ItemIso  (firstWire.trans secondWire) rels source target

private def ItemSeqIsoTransMotive {sourceWires middleWires : Nat}
    (firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires))
    (rels : RelCtx) (source : ItemSeq  sourceWires rels)
    (middle : ItemSeq  middleWires rels)
    (_ : ItemSeqIso  firstWire rels source middle) : Type :=
  forall {targetWires : Nat}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {target : ItemSeq  targetWires rels},
    ItemSeqIso  secondWire rels middle target ->
      ItemSeqIso  (firstWire.trans secondWire) rels source target

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

private def regionIsoTransCase
    {sourceWires middleWires sourceLocal middleLocal : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceItems : ItemSeq  (sourceWires + sourceLocal) rels}
    {middleItems : ItemSeq  (middleWires + middleLocal) rels}
    (firstLocal : FiniteEquiv (Fin sourceLocal) (Fin middleLocal))
    (firstItems : ItemSeqIso
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

private def atomIsoTransCase
    {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx} (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {middleArguments : Fin arity -> Fin middleWires}
    (firstArguments : firstWire.toFun ∘ sourceArguments = middleArguments) :
    ItemIsoTransMotive  firstWire rels
      (.atom  relation sourceArguments)
      (.atom  relation middleArguments)
      (.atom  relation firstArguments) := by
  intro targetWires secondWire target second
  cases second with
  | atom _ secondArguments =>
      apply ItemIso.atom  relation
      calc
        (firstWire.trans secondWire).toFun ∘ sourceArguments =
            secondWire.toFun ∘ (firstWire.toFun ∘ sourceArguments) := rfl
        _ = secondWire.toFun ∘ middleArguments :=
          congrArg (Function.comp secondWire.toFun) firstArguments
        _ = _ := secondArguments


private def identityIsoTransCase
    {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceArguments : Fin arity -> Fin sourceWires}
    {middleArguments : Fin arity -> Fin middleWires}
    (firstArguments : firstWire.toFun ∘ sourceArguments = middleArguments) :
    ItemIsoTransMotive  firstWire rels
      (.identity arity sourceArguments) (.identity arity middleArguments)
      (.identity firstArguments) := by
  intro targetWires secondWire target second
  cases second with
  | identity secondArguments =>
      apply ItemIso.identity
      calc
        (firstWire.trans secondWire).toFun ∘ sourceArguments =
            secondWire.toFun ∘ (firstWire.toFun ∘ sourceArguments) := rfl
        _ = secondWire.toFun ∘ middleArguments :=
          congrArg (Function.comp secondWire.toFun) firstArguments
        _ = _ := secondArguments

private def cutIsoTransCase
    {sourceWires middleWires : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceBody : Region  sourceWires rels}
    {middleBody : Region  middleWires rels}
    (firstBody : RegionIso  firstWire rels sourceBody middleBody)
    (bodyIH : RegionIsoTransMotive firstWire rels
      sourceBody middleBody firstBody) :
    ItemIsoTransMotive firstWire rels (.cut sourceBody) (.cut middleBody)
      (.cut firstBody) := by
  intro targetWires secondWire target second
  cases second with
  | cut secondBody => exact ItemIso.cut (bodyIH secondBody)

private def bubbleIsoTransCase
    {sourceWires middleWires arity : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {sourceBody : Region  sourceWires (arity :: rels)}
    {middleBody : Region  middleWires (arity :: rels)}
    (firstBody : RegionIso  firstWire (arity :: rels)
      sourceBody middleBody)
    (bodyIH : RegionIsoTransMotive firstWire (arity :: rels)
      sourceBody middleBody firstBody) :
    ItemIsoTransMotive firstWire rels (.bubble arity sourceBody)
      (.bubble arity middleBody) (.bubble firstBody) := by
  intro targetWires secondWire target second
  cases second with
  | bubble secondBody => exact ItemIso.bubble (bodyIH secondBody)

private def permuteIsoTransCase
    {sourceWires middleWires : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {rels : RelCtx}
    {source : ItemSeq  sourceWires rels}
    {middle : ItemSeq  middleWires rels}
    (firstPositions : FiniteEquiv (Fin source.length) (Fin middle.length))
    (firstItems : forall i, ItemIso  firstWire rels
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

private noncomputable def regionIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : Region  sourceWires rels}
    {middle : Region  middleWires rels}
    (first : RegionIso  firstWire rels source middle) :
    RegionIsoTransMotive firstWire rels source middle first := by
  unfold RegionIsoTransMotive
  intro targetWires secondWire target second
  exact RegionIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase atomIsoTransCase identityIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

private noncomputable def itemSeqIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : ItemSeq  sourceWires rels}
    {middle : ItemSeq  middleWires rels}
    (first : ItemSeqIso  firstWire rels source middle) :
    ItemSeqIsoTransMotive firstWire rels source middle first := by
  unfold ItemSeqIsoTransMotive
  intro targetWires secondWire target second
  exact ItemSeqIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase atomIsoTransCase identityIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

private noncomputable def itemIsoTransRec
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {source : Item  sourceWires rels}
    {middle : Item  middleWires rels}
    (first : ItemIso  firstWire rels source middle) :
    ItemIsoTransMotive firstWire rels source middle first := by
  unfold ItemIsoTransMotive
  intro targetWires secondWire target second
  exact ItemIso.rec
    (motive_1 := RegionIsoTransMotive)
    (motive_2 := ItemIsoTransMotive)
    (motive_3 := ItemSeqIsoTransMotive)
    regionIsoTransCase atomIsoTransCase identityIsoTransCase
    cutIsoTransCase bubbleIsoTransCase permuteIsoTransCase first second

noncomputable def RegionIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : Region  sourceWires rels}
    {middle : Region  middleWires rels}
    {target : Region  targetWires rels}
    (first : RegionIso  firstWire rels source middle)
    (second : RegionIso  secondWire rels middle target) :
    RegionIso  (firstWire.trans secondWire) rels source target :=
  regionIsoTransRec first second

theorem RegionIso.localEquivCast_trans
    {sourceWires middleWires targetWires
      sourceLocal middleLocal targetLocal : Nat}
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region sourceWires rels}
    {middle : Region middleWires rels}
    {target : Region targetWires rels}
    (first : RegionIso firstWire rels source middle)
    (second : RegionIso secondWire rels middle target)
    (sourceLocalEq : source.localCount = sourceLocal)
    (middleLocalEq : middle.localCount = middleLocal)
    (targetLocalEq : target.localCount = targetLocal) :
    (first.trans second).localEquivCast sourceLocalEq targetLocalEq =
      (first.localEquivCast sourceLocalEq middleLocalEq).trans
        (second.localEquivCast middleLocalEq targetLocalEq) := by
  subst sourceLocal
  subst middleLocal
  subst targetLocal
  cases first
  cases second
  rfl

noncomputable def ItemIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : Item  sourceWires rels}
    {middle : Item  middleWires rels}
    {target : Item  targetWires rels}
    (first : ItemIso  firstWire rels source middle)
    (second : ItemIso  secondWire rels middle target) :
    ItemIso  (firstWire.trans secondWire) rels source target :=
  itemIsoTransRec first second

noncomputable def ItemSeqIso.trans
    {firstWire : FiniteEquiv (Fin sourceWires) (Fin middleWires)}
    {secondWire : FiniteEquiv (Fin middleWires) (Fin targetWires)}
    {source : ItemSeq  sourceWires rels}
    {middle : ItemSeq  middleWires rels}
    {target : ItemSeq  targetWires rels}
    (first : ItemSeqIso  firstWire rels source middle)
    (second : ItemSeqIso  secondWire rels middle target) :
    ItemSeqIso  (firstWire.trans secondWire) rels source target :=
  itemSeqIsoTransRec first second

namespace Core

def Isomorphic (left right : Region  wires rels) : Prop :=
  Nonempty (RegionIso  (FiniteEquiv.refl (Fin wires)) rels left right)

end Core
private theorem ItemSeq.frame_length
    (frameAfter : ItemSeq wires rels) (before after : Item wires rels) :
    (frameBefore : ItemSeq wires rels) →
      (frameBefore.append (.cons before frameAfter)).length =
        (frameBefore.append (.cons after frameAfter)).length
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ
      (ItemSeq.frame_length frameAfter before after tail)

private noncomputable def ItemSeq.frame_get_iso
    (frameAfter : ItemSeq wires rels)
    {before after : Item wires rels}
    (replacement : ItemIso (FiniteEquiv.refl (Fin wires)) rels before after) :
    (frameBefore : ItemSeq wires rels) →
    ∀ index,
      ItemIso (FiniteEquiv.refl (Fin wires)) rels
        ((frameBefore.append (.cons before frameAfter)).get index)
        ((frameBefore.append (.cons after frameAfter)).get
          (Fin.cast (ItemSeq.frame_length frameAfter before after frameBefore)
            index))
  | .nil, index =>
      Fin.cases replacement
        (fun rest => ItemIso.refl (frameAfter.get rest)) index
  | .cons head tail, index => by
      refine Fin.cases (ItemIso.refl head) (fun rest => ?_) index
      simpa [ItemSeq.frame_length, ItemSeq.append, ItemSeq.length, ItemSeq.get]
        using ItemSeq.frame_get_iso frameAfter replacement tail rest

private noncomputable def ItemSeqIso.frame_refl
    (frameBefore frameAfter : ItemSeq wires rels)
    {before after : Item wires rels}
    (replacement : ItemIso (FiniteEquiv.refl (Fin wires)) rels before after) :
    ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
      (frameBefore.append (.cons before frameAfter))
      (frameBefore.append (.cons after frameAfter)) := by
  let lengthEquality :=
    ItemSeq.frame_length frameAfter before after frameBefore
  let positions : FiniteEquiv
      (Fin (frameBefore.append (.cons before frameAfter)).length)
      (Fin (frameBefore.append (.cons after frameAfter)).length) := {
    toFun := Fin.cast lengthEquality
    invFun := Fin.cast lengthEquality.symm
    left_inv := by
      intro index
      apply Fin.ext
      rfl
    right_inv := by
      intro index
      apply Fin.ext
      rfl
  }
  refine ItemSeqIso.permute positions ?_
  intro index
  exact ItemSeq.frame_get_iso frameAfter replacement frameBefore index

private theorem extendWireEquiv_refl (outer localWires : Nat) :
    extendWireEquiv (FiniteEquiv.refl (Fin outer))
        (FiniteEquiv.refl (Fin localWires)) =
      FiniteEquiv.refl (Fin (outer + localWires)) := by
  apply FiniteEquiv.ext
  intro index
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) index <;>
    simp [extendWireEquiv, FiniteEquiv.refl]

/-- Lift a canonical region-isomorphism witness through a fixed one-hole
context without erasing its recursive data. -/
noncomputable def DiagramContext.fillIso
    (context : DiagramContext outerWires holeWires outerRels holeRels)
    {before after : Region holeWires holeRels}
    (iso : RegionIso (FiniteEquiv.refl (Fin holeWires)) holeRels
      before after) :
    RegionIso (FiniteEquiv.refl (Fin outerWires)) outerRels
      (context.fill before) (context.fill after) := by
  induction context with
  | hole => exact iso
  | cut localWires frameBefore frameAfter child induction =>
      refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
      rw [extendWireEquiv_refl]
      exact ItemSeqIso.frame_refl frameBefore frameAfter
        (ItemIso.cut (induction iso))
  | bubble localWires frameBefore frameAfter arity child induction =>
      refine RegionIso.mk (FiniteEquiv.refl (Fin localWires)) ?_
      rw [extendWireEquiv_refl]
      exact ItemSeqIso.frame_refl frameBefore frameAfter
        (ItemIso.bubble (induction iso))

theorem DiagramContext.fill_iso
    (context : DiagramContext outerWires holeWires outerRels holeRels)
    {before after : Region holeWires holeRels}
    (h : Core.Isomorphic before after) :
    Core.Isomorphic (context.fill before) (context.fill after) :=
  match h with
  | ⟨iso⟩ => ⟨context.fillIso iso⟩
end VisualProof.Diagram
