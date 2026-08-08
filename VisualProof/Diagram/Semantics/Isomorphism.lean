import VisualProof.Diagram.Isomorphism
import VisualProof.Diagram.Semantics

namespace VisualProof.Diagram

open VisualProof
open Theory

theorem denoteItemSeq_iff_get
    (model : Model) (env : Fin wires -> model.Carrier)
    (rels : RelEnv model.Carrier relCtx)
    (items : ItemSeq  wires relCtx) :
    denoteItemSeq model  env rels items <->
      forall i, denoteItem model  env rels (items.get i) := by
  cases items with
  | nil =>
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        trivial
  | cons head tail =>
      have ih := denoteItemSeq_iff_get model  env rels tail
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

private def RegionDenotationMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Region  sourceWires rels)
    (right : Region  targetWires rels)
    (_ : RegionIso  wire rels left right) : Prop :=
  forall (model : Model)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteRegion model  sourceEnv relEnv left <->
        denoteRegion model  targetEnv relEnv right)

private def ItemDenotationMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Item  sourceWires rels)
    (right : Item  targetWires rels)
    (_ : ItemIso  wire rels left right) : Prop :=
  forall (model : Model)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteItem model  sourceEnv relEnv left <->
        denoteItem model  targetEnv relEnv right)

private def ItemSeqDenotationMotive {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : ItemSeq  sourceWires rels)
    (right : ItemSeq  targetWires rels)
    (_ : ItemSeqIso  wire rels left right) : Prop :=
  forall (model : Model)
    (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv ->
      (denoteItemSeq model  sourceEnv relEnv left <->
        denoteItemSeq model  targetEnv relEnv right)

private theorem regionDenotationCase
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceItems : ItemSeq  (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq  (targetWires + targetLocal) rels}
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqIso  (extendWireEquiv wire localEquiv) rels
      sourceItems targetItems)
    (itemsIH : ItemSeqDenotationMotive (extendWireEquiv wire localEquiv)
      rels sourceItems targetItems items) :
    RegionDenotationMotive wire rels
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      (.mk localEquiv items) := by
  intro model  sourceEnv targetEnv relEnv henv
  constructor
  · rintro ⟨sourceLocalEnv, hitems⟩
    let targetLocalEnv := fun i => sourceLocalEnv (localEquiv.invFun i)
    refine ⟨targetLocalEnv, ?_⟩
    apply (itemsIH model
      (extendWireEnv sourceEnv sourceLocalEnv)
      (extendWireEnv targetEnv targetLocalEnv) relEnv ?_).mp hitems
    apply extendWireEnv_agree wire localEquiv
    · exact henv
    · intro i
      simp [targetLocalEnv, localEquiv.left_inv]
  · rintro ⟨targetLocalEnv, hitems⟩
    let sourceLocalEnv := fun i => targetLocalEnv (localEquiv i)
    refine ⟨sourceLocalEnv, ?_⟩
    apply (itemsIH model
      (extendWireEnv sourceEnv sourceLocalEnv)
      (extendWireEnv targetEnv targetLocalEnv) relEnv ?_).mpr hitems
    apply extendWireEnv_agree wire localEquiv
    · exact henv
    · intro _
      rfl

private theorem atomDenotationCase
    {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    (relation : RelVar rels arity)
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemDenotationMotive  wire rels
      (.atom relation sourceArguments) (.atom relation targetArguments)
      (.atom  relation arguments_eq) := by
  intro model  sourceEnv targetEnv relEnv henv
  subst targetArguments
  have arguments_env_eq :
      targetEnv ∘ (wire.toFun ∘ sourceArguments) =
        sourceEnv ∘ sourceArguments := by
    funext i
    exact henv (sourceArguments i)
  simp only [denoteItem]
  rw [arguments_env_eq]


private theorem identityDenotationCase
    {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceArguments : Fin arity -> Fin sourceWires}
    {targetArguments : Fin arity -> Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemDenotationMotive  wire rels
      (.identity arity sourceArguments) (.identity arity targetArguments)
      (.identity arguments_eq) := by
  intro model  sourceEnv targetEnv relEnv henv
  subst targetArguments
  simp only [denoteItem_identity]
  constructor
  · intro sourceDenotes left right
    calc
      targetEnv (wire (sourceArguments left)) =
          sourceEnv (sourceArguments left) := henv _
      _ = sourceEnv (sourceArguments right) := sourceDenotes left right
      _ = targetEnv (wire (sourceArguments right)) := (henv _).symm
  · intro targetDenotes left right
    calc
      sourceEnv (sourceArguments left) =
          targetEnv (wire (sourceArguments left)) := (henv _).symm
      _ = targetEnv (wire (sourceArguments right)) := targetDenotes left right
      _ = sourceEnv (sourceArguments right) := henv _

private theorem cutDenotationCase
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region  sourceWires rels}
    {targetBody : Region  targetWires rels}
    (body : RegionIso  wire rels sourceBody targetBody)
    (bodyIH : RegionDenotationMotive wire rels sourceBody targetBody body) :
    ItemDenotationMotive wire rels (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro model  sourceEnv targetEnv relEnv henv
  constructor
  · intro hsource htarget
    exact hsource ((bodyIH model  sourceEnv targetEnv relEnv henv).mpr htarget)
  · intro htarget hsource
    exact htarget ((bodyIH model  sourceEnv targetEnv relEnv henv).mp hsource)

private theorem bubbleDenotationCase
    {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region  sourceWires (arity :: rels)}
    {targetBody : Region  targetWires (arity :: rels)}
    (body : RegionIso  wire (arity :: rels) sourceBody targetBody)
    (bodyIH : RegionDenotationMotive wire (arity :: rels)
      sourceBody targetBody body) :
    ItemDenotationMotive wire rels
      (.bubble arity sourceBody) (.bubble arity targetBody) (.bubble body) := by
  intro model  sourceEnv targetEnv relEnv henv
  constructor
  · rintro ⟨relation, hsource⟩
    exact ⟨relation, (bodyIH model  sourceEnv targetEnv
      (relation, relEnv) henv).mp hsource⟩
  · rintro ⟨relation, htarget⟩
    exact ⟨relation, (bodyIH model  sourceEnv targetEnv
      (relation, relEnv) henv).mpr htarget⟩

private theorem permuteDenotationCase
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {source : ItemSeq  sourceWires rels}
    {target : ItemSeq  targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : forall i, ItemIso  wire rels
      (source.get i) (target.get (positions i)))
    (itemsIH : forall i, ItemDenotationMotive wire rels
      (source.get i) (target.get (positions i)) (items i)) :
    ItemSeqDenotationMotive wire rels source target (.permute positions items) := by
  intro model  sourceEnv targetEnv relEnv henv
  rw [denoteItemSeq_iff_get, denoteItemSeq_iff_get]
  constructor
  · intro hsource targetIndex
    have hitem := (itemsIH (positions.invFun targetIndex) model
      sourceEnv targetEnv relEnv henv).mp
        (hsource (positions.invFun targetIndex))
    simpa only [positions.right_inv] using hitem
  · intro htarget sourceIndex
    exact (itemsIH sourceIndex model  sourceEnv targetEnv relEnv henv).mpr
      (htarget (positions sourceIndex))

private theorem regionDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region  sourceWires rels}
    {right : Region  targetWires rels}
    (hiso : RegionIso  wire rels left right) :
    RegionDenotationMotive wire rels left right hiso := by
  apply RegionIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase
    cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

private theorem itemDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item  sourceWires rels}
    {right : Item  targetWires rels}
    (hiso : ItemIso  wire rels left right) :
    ItemDenotationMotive wire rels left right hiso := by
  apply ItemIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase
    cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

private theorem itemSeqDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq  sourceWires rels}
    {right : ItemSeq  targetWires rels}
    (hiso : ItemSeqIso  wire rels left right) :
    ItemSeqDenotationMotive wire rels left right hiso := by
  apply ItemSeqIso.rec
    (motive_1 := RegionDenotationMotive)
    (motive_2 := ItemDenotationMotive)
    (motive_3 := ItemSeqDenotationMotive)
    regionDenotationCase atomDenotationCase identityDenotationCase
    cutDenotationCase bubbleDenotationCase
    permuteDenotationCase hiso

theorem RegionIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region  sourceWires rels}
    {right : Region  targetWires rels}
    (hiso : RegionIso  wire rels left right)
    (model : Model) (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteRegion model  sourceEnv relEnv left <->
      denoteRegion model  targetEnv relEnv right :=
  regionDenotationRec hiso model  sourceEnv targetEnv relEnv henv

theorem ItemIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item  sourceWires rels}
    {right : Item  targetWires rels}
    (hiso : ItemIso  wire rels left right)
    (model : Model) (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItem model  sourceEnv relEnv left <->
      denoteItem model  targetEnv relEnv right :=
  itemDenotationRec hiso model  sourceEnv targetEnv relEnv henv

theorem ItemSeqIso.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq  sourceWires rels}
    {right : ItemSeq  targetWires rels}
    (hiso : ItemSeqIso  wire rels left right)
    (model : Model) (sourceEnv : Fin sourceWires -> model.Carrier)
    (targetEnv : Fin targetWires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItemSeq model  sourceEnv relEnv left <->
      denoteItemSeq model  targetEnv relEnv right :=
  itemSeqDenotationRec hiso model  sourceEnv targetEnv relEnv henv

theorem iso_denotation
    {left right : Region  wires rels}
    (hiso : Core.Isomorphic left right)
    (model : Model) (env : Fin wires -> model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model  env relEnv left <->
      denoteRegion model  env relEnv right := by
  rcases hiso with ⟨iso⟩
  exact iso.denotation model env env relEnv (fun _ => rfl)

end VisualProof.Diagram
