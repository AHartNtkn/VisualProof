import VisualProof.Diagram.OpenIsomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

mutual
  /-- Intrinsic diagram correspondence that preserves all graphical structure exactly,
  while allowing equation terms to vary by beta-eta equivalence. -/
  inductive RegionBetaEtaEquiv (signature : List Nat) :
      {sourceWires targetWires : Nat} →
      FiniteEquiv (Fin sourceWires) (Fin targetWires) →
      (rels : RelCtx) →
      Region signature sourceWires rels →
      Region signature targetWires rels → Prop
    | mk {sourceWires targetWires sourceLocal targetLocal : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
        {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
        (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
        (items : ItemSeqBetaEtaEquiv signature
          (extendWireEquiv ambient localEquiv) rels sourceItems targetItems) :
        RegionBetaEtaEquiv signature ambient rels
          (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)

  inductive ItemBetaEtaEquiv (signature : List Nat) :
      {sourceWires targetWires : Nat} →
      FiniteEquiv (Fin sourceWires) (Fin targetWires) →
      (rels : RelCtx) →
      Item signature sourceWires rels →
      Item signature targetWires rels → Prop
    | equation {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
        {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
        {targetTerm : Lambda.Term 0 (Fin targetWires)}
        (output_eq : ambient sourceOutput = targetOutput)
        (term_equiv : Lambda.BetaEta (sourceTerm.mapFree ambient) targetTerm) :
        ItemBetaEtaEquiv signature ambient rels
          (.equation sourceOutput sourceTerm)
          (.equation targetOutput targetTerm)
    | atom {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        (relation : RelVar rels arity)
        {sourceArguments : Fin arity → Fin sourceWires}
        {targetArguments : Fin arity → Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemBetaEtaEquiv signature ambient rels
          (.atom relation sourceArguments) (.atom relation targetArguments)
    | named {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        (relation : NamedRel signature arity)
        {sourceArguments : Fin arity → Fin sourceWires}
        {targetArguments : Fin arity → Fin targetWires}
        (arguments_eq : ambient.toFun ∘ sourceArguments = targetArguments) :
        ItemBetaEtaEquiv signature ambient rels
          (.named relation sourceArguments) (.named relation targetArguments)
    | cut {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region signature sourceWires rels}
        {targetBody : Region signature targetWires rels}
        (body : RegionBetaEtaEquiv signature ambient rels sourceBody targetBody) :
        ItemBetaEtaEquiv signature ambient rels (.cut sourceBody) (.cut targetBody)
    | bubble {sourceWires targetWires arity : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {sourceBody : Region signature sourceWires (arity :: rels)}
        {targetBody : Region signature targetWires (arity :: rels)}
        (body : RegionBetaEtaEquiv signature ambient (arity :: rels)
          sourceBody targetBody) :
        ItemBetaEtaEquiv signature ambient rels
          (.bubble arity sourceBody) (.bubble arity targetBody)

  inductive ItemSeqBetaEtaEquiv (signature : List Nat) :
      {sourceWires targetWires : Nat} →
      FiniteEquiv (Fin sourceWires) (Fin targetWires) →
      (rels : RelCtx) →
      ItemSeq signature sourceWires rels →
      ItemSeq signature targetWires rels → Prop
    | permute {sourceWires targetWires : Nat}
        {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
        {rels : RelCtx}
        {source : ItemSeq signature sourceWires rels}
        {target : ItemSeq signature targetWires rels}
        (positions : FiniteEquiv (Fin source.length) (Fin target.length))
        (items : ∀ i, ItemBetaEtaEquiv signature ambient rels
          (source.get i) (target.get (positions i))) :
        ItemSeqBetaEtaEquiv signature ambient rels source target
end

private theorem regionIsoToBetaEtaRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region signature sourceWires rels}
    {right : Region signature targetWires rels}
    (iso : RegionIso signature wire rels left right) :
    RegionBetaEtaEquiv signature wire rels left right := by
  apply RegionIso.rec
    (motive_1 := fun wire rels left right _ =>
      RegionBetaEtaEquiv signature wire rels left right)
    (motive_2 := fun wire rels left right _ =>
      ItemBetaEtaEquiv signature wire rels left right)
    (motive_3 := fun wire rels left right _ =>
      ItemSeqBetaEtaEquiv signature wire rels left right)
  · intro sourceWires targetWires sourceLocal targetLocal ambient rels
      sourceItems targetItems localEquiv items itemsIH
    exact .mk localEquiv itemsIH
  · intro sourceWires targetWires ambient rels sourceOutput targetOutput
      sourceTerm targetTerm output_eq term_eq
    exact .equation output_eq (term_eq ▸ .refl)
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .atom relation arguments_eq
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .named relation arguments_eq
  · intro sourceWires targetWires ambient rels sourceBody targetBody body bodyIH
    exact .cut bodyIH
  · intro sourceWires targetWires arity ambient rels sourceBody targetBody
      body bodyIH
    exact .bubble bodyIH
  · intro sourceWires targetWires ambient rels source target positions items itemsIH
    exact .permute positions itemsIH
  · exact iso

private theorem itemIsoToBetaEtaRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item signature sourceWires rels}
    {right : Item signature targetWires rels}
    (iso : ItemIso signature wire rels left right) :
    ItemBetaEtaEquiv signature wire rels left right := by
  apply ItemIso.rec
    (motive_1 := fun wire rels left right _ =>
      RegionBetaEtaEquiv signature wire rels left right)
    (motive_2 := fun wire rels left right _ =>
      ItemBetaEtaEquiv signature wire rels left right)
    (motive_3 := fun wire rels left right _ =>
      ItemSeqBetaEtaEquiv signature wire rels left right)
  · intro sourceWires targetWires sourceLocal targetLocal ambient rels
      sourceItems targetItems localEquiv items itemsIH
    exact .mk localEquiv itemsIH
  · intro sourceWires targetWires ambient rels sourceOutput targetOutput
      sourceTerm targetTerm output_eq term_eq
    exact .equation output_eq (term_eq ▸ .refl)
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .atom relation arguments_eq
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .named relation arguments_eq
  · intro sourceWires targetWires ambient rels sourceBody targetBody body bodyIH
    exact .cut bodyIH
  · intro sourceWires targetWires arity ambient rels sourceBody targetBody
      body bodyIH
    exact .bubble bodyIH
  · intro sourceWires targetWires ambient rels source target positions items itemsIH
    exact .permute positions itemsIH
  · exact iso

private theorem itemSeqIsoToBetaEtaRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq signature sourceWires rels}
    {right : ItemSeq signature targetWires rels}
    (iso : ItemSeqIso signature wire rels left right) :
    ItemSeqBetaEtaEquiv signature wire rels left right := by
  apply ItemSeqIso.rec
    (motive_1 := fun wire rels left right _ =>
      RegionBetaEtaEquiv signature wire rels left right)
    (motive_2 := fun wire rels left right _ =>
      ItemBetaEtaEquiv signature wire rels left right)
    (motive_3 := fun wire rels left right _ =>
      ItemSeqBetaEtaEquiv signature wire rels left right)
  · intro sourceWires targetWires sourceLocal targetLocal ambient rels
      sourceItems targetItems localEquiv items itemsIH
    exact .mk localEquiv itemsIH
  · intro sourceWires targetWires ambient rels sourceOutput targetOutput
      sourceTerm targetTerm output_eq term_eq
    exact .equation output_eq (term_eq ▸ .refl)
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .atom relation arguments_eq
  · intro sourceWires targetWires arity ambient rels relation
      sourceArguments targetArguments arguments_eq
    exact .named relation arguments_eq
  · intro sourceWires targetWires ambient rels sourceBody targetBody body bodyIH
    exact .cut bodyIH
  · intro sourceWires targetWires arity ambient rels sourceBody targetBody
      body bodyIH
    exact .bubble bodyIH
  · intro sourceWires targetWires ambient rels source target positions items itemsIH
    exact .permute positions itemsIH
  · exact iso

theorem RegionIso.toBetaEtaEquiv
    (iso : RegionIso signature wire rels left right) :
    RegionBetaEtaEquiv signature wire rels left right :=
  regionIsoToBetaEtaRec iso

theorem ItemIso.toBetaEtaEquiv
    (iso : ItemIso signature wire rels left right) :
    ItemBetaEtaEquiv signature wire rels left right :=
  itemIsoToBetaEtaRec iso

theorem ItemSeqIso.toBetaEtaEquiv
    (iso : ItemSeqIso signature wire rels left right) :
    ItemSeqBetaEtaEquiv signature wire rels left right :=
  itemSeqIsoToBetaEtaRec iso

private def RegionBetaEtaDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Region signature sourceWires rels)
    (right : Region signature targetWires rels)
    (_ : RegionBetaEtaEquiv signature wire rels left right) : Prop :=
  ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv →
      (denoteRegion model named sourceEnv relEnv left ↔
        denoteRegion model named targetEnv relEnv right)

private def ItemBetaEtaDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : Item signature sourceWires rels)
    (right : Item signature targetWires rels)
    (_ : ItemBetaEtaEquiv signature wire rels left right) : Prop :=
  ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv →
      (denoteItem model named sourceEnv relEnv left ↔
        denoteItem model named targetEnv relEnv right)

private def ItemSeqBetaEtaDenotationMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (left : ItemSeq signature sourceWires rels)
    (right : ItemSeq signature targetWires rels)
    (_ : ItemSeqBetaEtaEquiv signature wire rels left right) : Prop :=
  ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels),
    EnvironmentsAgree wire sourceEnv targetEnv →
      (denoteItemSeq model named sourceEnv relEnv left ↔
        denoteItemSeq model named targetEnv relEnv right)

private theorem regionBetaEtaDenotationCase
    {signature : List Nat}
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqBetaEtaEquiv signature
      (extendWireEquiv wire localEquiv) rels sourceItems targetItems)
    (itemsIH : ItemSeqBetaEtaDenotationMotive
      (extendWireEquiv wire localEquiv) rels sourceItems targetItems items) :
    RegionBetaEtaDenotationMotive wire rels
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

private theorem equationBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
    {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
    {targetTerm : Lambda.Term 0 (Fin targetWires)}
    (output_eq : wire sourceOutput = targetOutput)
    (term_equiv : Lambda.BetaEta (sourceTerm.mapFree wire) targetTerm) :
    ItemBetaEtaDenotationMotive (signature := signature) wire rels
      (.equation sourceOutput sourceTerm) (.equation targetOutput targetTerm)
      (.equation output_eq term_equiv) := by
  intro model named sourceEnv targetEnv relEnv henv
  have env_eq : targetEnv ∘ wire.toFun = sourceEnv := funext henv
  have term_eval : model.eval sourceTerm sourceEnv =
      model.eval targetTerm targetEnv := by
    calc
      model.eval sourceTerm sourceEnv =
          model.eval sourceTerm (targetEnv ∘ wire.toFun) := by rw [env_eq]
      _ = model.eval (sourceTerm.mapFree wire.toFun) targetEnv :=
        (model.eval_mapFree wire.toFun sourceTerm targetEnv).symm
      _ = model.eval targetTerm targetEnv := model.betaEta_sound term_equiv
  simp only [denoteItem]
  constructor
  · intro sourceEquation
    calc
      targetEnv targetOutput = targetEnv (wire sourceOutput) :=
        congrArg targetEnv output_eq.symm
      _ = sourceEnv sourceOutput := henv sourceOutput
      _ = model.eval sourceTerm sourceEnv := sourceEquation
      _ = model.eval targetTerm targetEnv := term_eval
  · intro targetEquation
    calc
      sourceEnv sourceOutput = targetEnv (wire sourceOutput) :=
        (henv sourceOutput).symm
      _ = targetEnv targetOutput := congrArg targetEnv output_eq
      _ = model.eval targetTerm targetEnv := targetEquation
      _ = model.eval sourceTerm sourceEnv := term_eval.symm

private theorem atomBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    (relation : RelVar rels arity)
    {sourceArguments : Fin arity → Fin sourceWires}
    {targetArguments : Fin arity → Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemBetaEtaDenotationMotive (signature := signature) wire rels
      (.atom relation sourceArguments) (.atom relation targetArguments)
      (.atom relation arguments_eq) := by
  intro model named sourceEnv targetEnv relEnv henv
  subst targetArguments
  have arguments_env_eq :
      targetEnv ∘ (wire.toFun ∘ sourceArguments) =
        sourceEnv ∘ sourceArguments := by
    funext i
    exact henv (sourceArguments i)
  simp only [denoteItem]
  rw [arguments_env_eq]

private theorem namedBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    (relation : NamedRel signature arity)
    {sourceArguments : Fin arity → Fin sourceWires}
    {targetArguments : Fin arity → Fin targetWires}
    (arguments_eq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemBetaEtaDenotationMotive wire rels
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

private theorem cutBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region signature sourceWires rels}
    {targetBody : Region signature targetWires rels}
    (body : RegionBetaEtaEquiv signature wire rels sourceBody targetBody)
    (bodyIH : RegionBetaEtaDenotationMotive wire rels sourceBody targetBody body) :
    ItemBetaEtaDenotationMotive wire rels (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro model named sourceEnv targetEnv relEnv henv
  constructor
  · intro hsource htarget
    exact hsource ((bodyIH model named sourceEnv targetEnv relEnv henv).mpr htarget)
  · intro htarget hsource
    exact htarget ((bodyIH model named sourceEnv targetEnv relEnv henv).mp hsource)

private theorem bubbleBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires arity : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {targetBody : Region signature targetWires (arity :: rels)}
    (body : RegionBetaEtaEquiv signature wire (arity :: rels)
      sourceBody targetBody)
    (bodyIH : RegionBetaEtaDenotationMotive wire (arity :: rels)
      sourceBody targetBody body) :
    ItemBetaEtaDenotationMotive wire rels
      (.bubble arity sourceBody) (.bubble arity targetBody) (.bubble body) := by
  intro model named sourceEnv targetEnv relEnv henv
  constructor
  · rintro ⟨relation, hsource⟩
    exact ⟨relation, (bodyIH model named sourceEnv targetEnv
      (relation, relEnv) henv).mp hsource⟩
  · rintro ⟨relation, htarget⟩
    exact ⟨relation, (bodyIH model named sourceEnv targetEnv
      (relation, relEnv) henv).mpr htarget⟩

private theorem permuteBetaEtaDenotationCase
    {signature : List Nat} {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)} {rels : RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ i, ItemBetaEtaEquiv signature wire rels
      (source.get i) (target.get (positions i)))
    (itemsIH : ∀ i, ItemBetaEtaDenotationMotive wire rels
      (source.get i) (target.get (positions i)) (items i)) :
    ItemSeqBetaEtaDenotationMotive wire rels source target
      (.permute positions items) := by
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

private theorem regionBetaEtaDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region signature sourceWires rels}
    {right : Region signature targetWires rels}
    (equiv : RegionBetaEtaEquiv signature wire rels left right) :
    RegionBetaEtaDenotationMotive wire rels left right equiv := by
  apply RegionBetaEtaEquiv.rec
    (motive_1 := RegionBetaEtaDenotationMotive)
    (motive_2 := ItemBetaEtaDenotationMotive)
    (motive_3 := ItemSeqBetaEtaDenotationMotive)
    regionBetaEtaDenotationCase equationBetaEtaDenotationCase
    atomBetaEtaDenotationCase namedBetaEtaDenotationCase
    cutBetaEtaDenotationCase bubbleBetaEtaDenotationCase
    permuteBetaEtaDenotationCase equiv

private theorem itemBetaEtaDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item signature sourceWires rels}
    {right : Item signature targetWires rels}
    (equiv : ItemBetaEtaEquiv signature wire rels left right) :
    ItemBetaEtaDenotationMotive wire rels left right equiv := by
  apply ItemBetaEtaEquiv.rec
    (motive_1 := RegionBetaEtaDenotationMotive)
    (motive_2 := ItemBetaEtaDenotationMotive)
    (motive_3 := ItemSeqBetaEtaDenotationMotive)
    regionBetaEtaDenotationCase equationBetaEtaDenotationCase
    atomBetaEtaDenotationCase namedBetaEtaDenotationCase
    cutBetaEtaDenotationCase bubbleBetaEtaDenotationCase
    permuteBetaEtaDenotationCase equiv

private theorem itemSeqBetaEtaDenotationRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq signature sourceWires rels}
    {right : ItemSeq signature targetWires rels}
    (equiv : ItemSeqBetaEtaEquiv signature wire rels left right) :
    ItemSeqBetaEtaDenotationMotive wire rels left right equiv := by
  apply ItemSeqBetaEtaEquiv.rec
    (motive_1 := RegionBetaEtaDenotationMotive)
    (motive_2 := ItemBetaEtaDenotationMotive)
    (motive_3 := ItemSeqBetaEtaDenotationMotive)
    regionBetaEtaDenotationCase equationBetaEtaDenotationCase
    atomBetaEtaDenotationCase namedBetaEtaDenotationCase
    cutBetaEtaDenotationCase bubbleBetaEtaDenotationCase
    permuteBetaEtaDenotationCase equiv

theorem RegionBetaEtaEquiv.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Region signature sourceWires rels}
    {right : Region signature targetWires rels}
    (equiv : RegionBetaEtaEquiv signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteRegion model named sourceEnv relEnv left ↔
      denoteRegion model named targetEnv relEnv right :=
  regionBetaEtaDenotationRec equiv model named sourceEnv targetEnv relEnv henv

theorem ItemBetaEtaEquiv.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : Item signature sourceWires rels}
    {right : Item signature targetWires rels}
    (equiv : ItemBetaEtaEquiv signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItem model named sourceEnv relEnv left ↔
      denoteItem model named targetEnv relEnv right :=
  itemBetaEtaDenotationRec equiv model named sourceEnv targetEnv relEnv henv

theorem ItemSeqBetaEtaEquiv.denotation
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {left : ItemSeq signature sourceWires rels}
    {right : ItemSeq signature targetWires rels}
    (equiv : ItemSeqBetaEtaEquiv signature wire rels left right)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceWires → model.Carrier)
    (targetEnv : Fin targetWires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (henv : EnvironmentsAgree wire sourceEnv targetEnv) :
    denoteItemSeq model named sourceEnv relEnv left ↔
      denoteItemSeq model named targetEnv relEnv right :=
  itemSeqBetaEtaDenotationRec equiv model named sourceEnv targetEnv relEnv henv

/-- Ordered-open intrinsic equivalence with beta-eta equation correspondence. -/
structure OpenDiagramBetaEtaEquiv
    (source target : OpenDiagram signature arity) where
  external : FiniteEquiv (Fin source.externalClasses)
    (Fin target.externalClasses)
  boundary : ∀ i, external (source.boundary i) = target.boundary i
  body : RegionBetaEtaEquiv signature external [] source.body target.body

namespace OpenDiagramBetaEtaEquiv

def ofArityEq {sourceArity targetArity : Nat}
    {source : OpenDiagram signature sourceArity}
    {target : OpenDiagram signature targetArity}
    (arityEq : sourceArity = targetArity)
    (external : FiniteEquiv (Fin source.externalClasses)
      (Fin target.externalClasses))
    (boundary : ∀ position,
      external (source.boundary position) =
        target.boundary (Fin.cast arityEq position))
    (body : RegionBetaEtaEquiv signature external [] source.body target.body) :
    OpenDiagramBetaEtaEquiv source (target.castArity arityEq.symm) := by
  subst targetArity
  exact { external := external, boundary := boundary, body := body }

def ofOpenDiagramIso {source target : OpenDiagram signature arity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramBetaEtaEquiv source target where
  external := iso.external
  boundary := iso.boundary
  body := iso.body.toBetaEtaEquiv

def transportAssignment {source target : OpenDiagram signature arity}
    (equiv : OpenDiagramBetaEtaEquiv source target)
    (assignment : BoundaryAssignment source D) : BoundaryAssignment target D where
  args := assignment.args
  classes := assignment.classes ∘ equiv.external.invFun
  agrees := by
    intro i
    change assignment.classes (equiv.external.invFun (target.boundary i)) =
      assignment.args i
    rw [← equiv.boundary i, equiv.external.left_inv]
    exact assignment.agrees i

theorem preservesDenotation {source target : OpenDiagram signature arity}
    (equiv : OpenDiagramBetaEtaEquiv source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier) :
    denoteOpen model named source args → denoteOpen model named target args := by
  rintro ⟨sourceAssignment, sourceArgs, sourceBody⟩
  let targetAssignment := equiv.transportAssignment sourceAssignment
  refine ⟨targetAssignment, sourceArgs, ?_⟩
  apply (equiv.body.denotation model named sourceAssignment.classes
    targetAssignment.classes PUnit.unit ?_).mp sourceBody
  intro sourceClass
  change sourceAssignment.classes
      (equiv.external.invFun (equiv.external sourceClass)) =
    sourceAssignment.classes sourceClass
  rw [equiv.external.left_inv]

theorem denoteOpen_iff {source target : OpenDiagram signature arity}
    (equiv : OpenDiagramBetaEtaEquiv source target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier) :
    denoteOpen model named source args ↔ denoteOpen model named target args := by
  constructor
  · exact equiv.preservesDenotation model named args
  · rintro ⟨targetAssignment, targetArgs, targetBody⟩
    let sourceAssignment : BoundaryAssignment source model.Carrier := {
      args := targetAssignment.args
      classes := targetAssignment.classes ∘ equiv.external
      agrees := by
        intro i
        change targetAssignment.classes (equiv.external (source.boundary i)) =
          targetAssignment.args i
        rw [equiv.boundary i]
        exact targetAssignment.agrees i
    }
    refine ⟨sourceAssignment, targetArgs, ?_⟩
    apply (equiv.body.denotation model named sourceAssignment.classes
      targetAssignment.classes PUnit.unit ?_).mpr targetBody
    intro sourceClass
    rfl

end OpenDiagramBetaEtaEquiv

end VisualProof.Diagram
