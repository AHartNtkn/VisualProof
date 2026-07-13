import VisualProof.Diagram.Context

namespace VisualProof.Diagram

open VisualProof
open Theory

structure FiniteEquiv (alpha beta : Type) where
  toFun : alpha -> beta
  invFun : beta -> alpha
  left_inv : forall x, invFun (toFun x) = x
  right_inv : forall y, toFun (invFun y) = y

instance : CoeFun (FiniteEquiv alpha beta) (fun _ => alpha -> beta) where
  coe equivalence := equivalence.toFun

namespace FiniteEquiv

def refl (alpha : Type) : FiniteEquiv alpha alpha where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem refl_apply (x : alpha) : refl alpha x = x := rfl

def symm (equivalence : FiniteEquiv alpha beta) : FiniteEquiv beta alpha where
  toFun := equivalence.invFun
  invFun := equivalence.toFun
  left_inv := equivalence.right_inv
  right_inv := equivalence.left_inv

@[simp] theorem symm_toFun (equivalence : FiniteEquiv alpha beta) :
    equivalence.symm.toFun = equivalence.invFun := rfl

def trans (first : FiniteEquiv alpha beta) (second : FiniteEquiv beta gamma) :
    FiniteEquiv alpha gamma where
  toFun := second.toFun ∘ first.toFun
  invFun := first.invFun ∘ second.invFun
  left_inv := by
    intro x
    simp only [Function.comp_apply, second.left_inv, first.left_inv]
  right_inv := by
    intro z
    simp only [Function.comp_apply, first.right_inv, second.right_inv]

@[simp] theorem trans_apply (first : FiniteEquiv alpha beta)
    (second : FiniteEquiv beta gamma) (x : alpha) :
    first.trans second x = second (first x) := rfl

@[simp] theorem symm_apply_apply (equivalence : FiniteEquiv alpha beta)
    (x : alpha) : equivalence.symm (equivalence x) = x :=
  equivalence.left_inv x

@[simp] theorem apply_symm_apply (equivalence : FiniteEquiv alpha beta)
    (y : beta) : equivalence (equivalence.symm y) = y :=
  equivalence.right_inv y

@[ext] theorem ext {left right : FiniteEquiv alpha beta}
    (forward_eq : forall x, left x = right x) : left = right := by
  have forward_fun_eq : left.toFun = right.toFun := funext forward_eq
  cases left with
  | mk leftForward leftInverse leftLeft leftRight =>
      cases right with
      | mk rightForward rightInverse rightLeft rightRight =>
          simp only at forward_fun_eq
          subst rightForward
          have inverse_eq : leftInverse = rightInverse := by
            funext y
            calc
              leftInverse y = leftInverse (leftForward (rightInverse y)) :=
                congrArg leftInverse (rightRight y).symm
              _ = rightInverse y := leftLeft (rightInverse y)
          subst rightInverse
          rfl

end FiniteEquiv

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
