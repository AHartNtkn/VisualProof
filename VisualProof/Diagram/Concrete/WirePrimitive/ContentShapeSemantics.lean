import VisualProof.Diagram.Concrete.WirePrimitive.ContentSemantics

namespace VisualProof

namespace ConcreteWirePrimitive

namespace ContentShapeSemantics

universe u

open ContentAlignment

/-- Extend one outer environment by an ordered intrinsic value block. -/
def extendValues
    {pre : PreModel.{u}} :
    {bound : List Sig} →
      ConcreteElaboration.WireValues pre bound →
      Env pre outer →
      Env pre (bound ++ outer)
  | [], .nil, outerEnv => outerEnv
  | _ :: _, .cons head tail, outerEnv =>
      (extendValues tail outerEnv).extend head

/-- Read the ordered local prefix back from one complete environment. -/
def valuesFromEnv
    {pre : PreModel.{u}} :
    (bound : List Sig) →
      Env pre (bound ++ outer) →
      ConcreteElaboration.WireValues pre bound
  | [], _ => .nil
  | _ :: rest, env =>
      .cons (env _ .here)
        (valuesFromEnv rest (fun signature value =>
          env signature (.there value)))

@[simp] theorem extendValues_outer
    {pre : PreModel.{u}}
    {bound outer : List Sig}
    (values : ConcreteElaboration.WireValues pre bound)
    (outerEnv : Env pre outer)
    {signature : Sig}
    (value : Var outer signature) :
    extendValues values outerEnv signature
        (Var.appendRight bound value) =
      outerEnv signature value := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simpa [extendValues, Var.appendRight] using induction

theorem extendValues_from
    {pre : PreModel.{u}}
    (bound : List Sig)
    (env : Env pre (bound ++ outer))
    (outerEnv : Env pre outer)
    (agrees :
      ∀ {signature : Sig} (value : Var outer signature),
        env signature (Var.appendRight bound value) =
          outerEnv signature value) :
    extendValues (valuesFromEnv bound env) outerEnv = env := by
  induction bound with
  | nil =>
      funext signature value
      exact (agrees value).symm
  | cons head rest induction =>
      let tailEnv : Env pre (rest ++ outer) :=
        fun signature value => env signature (.there value)
      have tailAgrees :
          ∀ {signature : Sig} (value : Var outer signature),
            tailEnv signature (Var.appendRight rest value) =
              outerEnv signature value := by
        intro signature value
        exact agrees value
      have tailExact :=
        induction tailEnv tailAgrees
      funext signature value
      cases value with
      | here => rfl
      | there value =>
          exact congrFun (congrFun tailExact signature) value

private theorem bindMany_fill_hole
    (bound : List Sig)
    (inner :
      DiagramContext definitions hole (bound ++ outer))
    (body : Region definitions hole) :
    (DiagramContext.bindMany bound inner).fill body =
      (DiagramContext.bindMany bound
        (.hole :
          DiagramContext definitions
            (bound ++ outer) (bound ++ outer))).fill
        (inner.fill body) := by
  induction bound generalizing hole outer with
  | nil => rfl
  | cons signature rest induction =>
      simp only [DiagramContext.bindMany]
      rw [induction (.bind signature inner)]
      rw [induction
        (.bind signature
          (.hole :
            DiagramContext definitions
              (signature :: rest ++ outer)
              (signature :: rest ++ outer)))]
      rfl

/--
Denotation of the context-level ordered binder block is existential choice of
exactly one value per ordered signature.
-/
theorem denote_bindMany
    (bound : List Sig)
    (body : Region definitions (bound ++ outer))
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (outerEnv : Env pre outer) :
    denoteRegion pre definitionEnv outerEnv
        ((DiagramContext.bindMany bound
          (.hole :
            DiagramContext definitions
              (bound ++ outer) (bound ++ outer))).fill body) ↔
      ∃ values : ConcreteElaboration.WireValues pre bound,
        denoteRegion pre definitionEnv
          (extendValues values outerEnv) body := by
  induction bound with
  | nil =>
      constructor
      · intro holds
        exact ⟨.nil, holds⟩
      · rintro ⟨values, holds⟩
        cases values
        exact holds
  | cons signature rest induction =>
      simp only [DiagramContext.bindMany]
      rw [bindMany_fill_hole rest
        (.bind signature
          (.hole :
            DiagramContext definitions
              (signature :: rest ++ outer)
              (signature :: rest ++ outer)))
        body]
      rw [induction]
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      constructor
      · rintro ⟨tailValues, headValue, holds⟩
        exact ⟨.cons headValue tailValues, holds⟩
      · rintro ⟨values, holds⟩
        cases values with
        | cons headValue tailValues =>
            exact ⟨tailValues, headValue, holds⟩

/-- Any checked site frame is an exact denotational presentation of its root. -/
theorem SiteCompilation.denotes
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv base ↔
      denoteRegion pre definitionEnv Env.empty
        (compiled.frame.context.fill compiled.frame.siteBody) := by
  rw [elaborate_denotes_checked]
  have checkedExact :
      compiled.checked = elaborate base :=
    Option.some.inj
      (compiled.root_generated.symm.trans
        (elaborateWith_compiles definitions base.val base.property))
  rw [compiled.frame_fills_checked, checkedExact]

/--
The checked cut factorization equates the complete source and target local
binder blocks by choosing complementary full-model relation witnesses.
-/
theorem cutLocalDenotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.targetWire).scope}
    (factorization :
      ContentAlignment.CutFactorization result sourceScope targetScope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (siteEnv : Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures source.val (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            sourceScope.frame.siteBody)) ↔
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter)
              (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            targetScope.frame.siteBody)) := by
  rw [denote_bindMany, denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceLocalHolds⟩
    let sourceLocalEnv :=
      extendValues sourceValues siteEnv
    let sourceEnv :=
      factorization.context.sourceEnvironment sourceLocalEnv
    let targetWitness :
        model.toPreModel.Domain (.rel factorization.arguments) :=
      fun values =>
        ¬sourceEnv _ factorization.sourceHead values
    let commonEnv :
        Env model.toPreModel
          ((.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs) :=
      sourceEnv.extend targetWitness
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          sourceScope.frame.siteBody :=
      (factorization.context.sourceBody_denotes model.toPreModel
        definitionEnv sourceLocalEnv sourceScope.frame.siteBody).mp
        sourceLocalHolds
    have pointwise :
        ∀ values,
          model.toPreModel.apply
              (commonEnv _ (.there factorization.sourceHead)) values ↔
            ¬model.toPreModel.apply
              (commonEnv _ (.here :
                Var
                  ((.rel factorization.arguments) ::
                    sourceScope.frame.visible.sigs)
                  (.rel factorization.arguments)))
              values := by
      intro values
      change
        model.toPreModel.apply
            (sourceEnv _ factorization.sourceHead) values ↔
          ¬¬model.toPreModel.apply
            (sourceEnv _ factorization.sourceHead) values
      exact Classical.not_not.symm
    let targetEnv : Env model.toPreModel targetScope.frame.visible.sigs :=
      Env.comp commonEnv
        (separateVar factorization.targetHead
          factorization.alignment.backward)
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          targetScope.frame.siteBody := by
      apply
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          pointwise).mp
      simpa [commonEnv, ContentAlignment.weakenOne, Env.comp] using
        sourceHolds
    let targetLocalEnv :=
      factorization.context.targetLocalEnvironment targetEnv
    have targetLocalHolds :
        denoteRegion model.toPreModel definitionEnv targetLocalEnv
          (factorization.context.targetBody targetScope.frame.siteBody) :=
      by
        apply
          (factorization.context.targetBody_denotes model.toPreModel
            definitionEnv targetLocalEnv targetScope.frame.siteBody).mpr
        dsimp only [targetLocalEnv]
        rw [factorization.context.targetEnvironment_local]
        exact targetHolds
    have targetOuter :
        ∀ {signature : Sig}
            (value :
              Var factorization.context.siteOuter signature),
          targetLocalEnv signature
              (Var.appendRight
                (localSignatures result.checked.val
                  (result.checked.val.wires result.targetWire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetLocalEnvironment_outer]
      calc
        targetEnv signature
            (factorization.context.targetOuterEmbedding value) =
          commonEnv signature
            (separateVar factorization.targetHead
              factorization.alignment.backward
              (factorization.context.targetOuterEmbedding value)) := rfl
        _ =
          commonEnv signature
            (.there
              (factorization.context.sourceOuterEmbedding value)) := by
              rw [
                factorization.environmentAlignment.targetOuter.agrees
                  value]
        _ =
          sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) := rfl
        _ =
          sourceLocalEnv signature
            (Var.appendRight
              (localSignatures source.val
                (source.val.wires wire).scope) value) :=
              factorization.context.sourceEnvironment_outer
                sourceLocalEnv value
        _ = siteEnv signature value :=
              extendValues_outer sourceValues siteEnv value
    refine
      ⟨valuesFromEnv
          (localSignatures result.checked.val
            (result.checked.val.wires result.targetWire).scope)
          targetLocalEnv, ?_⟩
    rw [extendValues_from
      (localSignatures result.checked.val
        (result.checked.val.wires result.targetWire).scope)
      targetLocalEnv siteEnv targetOuter]
    exact targetLocalHolds
  · rintro ⟨targetValues, targetLocalHolds⟩
    let targetLocalEnv :=
      extendValues targetValues siteEnv
    let targetEnv :=
      factorization.context.targetEnvironment targetLocalEnv
    let sourceWitness :
        model.toPreModel.Domain (.rel factorization.arguments) :=
      fun values =>
        ¬targetEnv _ factorization.targetHead values
    let sourceEnv : Env model.toPreModel sourceScope.frame.visible.sigs :=
      Env.comp (targetEnv.extend sourceWitness)
        (separateVar factorization.sourceHead
          factorization.alignment.forward)
    let commonEnv :
        Env model.toPreModel
          ((.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs) :=
      sourceEnv.extend (targetEnv _ factorization.targetHead)
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          targetScope.frame.siteBody :=
      (factorization.context.targetBody_denotes model.toPreModel
        definitionEnv targetLocalEnv targetScope.frame.siteBody).mp
        targetLocalHolds
    have pointwise :
        ∀ values,
          model.toPreModel.apply
              (commonEnv _ (.there factorization.sourceHead)) values ↔
            ¬model.toPreModel.apply
              (commonEnv _ (.here :
                Var
                  ((.rel factorization.arguments) ::
                    sourceScope.frame.visible.sigs)
                  (.rel factorization.arguments)))
              values := by
      intro values
      simp [commonEnv, sourceEnv, sourceWitness, Env.comp,
        ContentAlignment.separateVar]
      change
        (¬targetEnv _ factorization.targetHead
          (PreModel.Args.toFull values)) ↔
          ¬targetEnv _ factorization.targetHead
            (PreModel.Args.toFull values)
      exact Iff.rfl
    have reconstructed :
        Env.comp commonEnv
            (separateVar factorization.targetHead
              factorization.alignment.backward) =
          targetEnv := by
      simpa [commonEnv, sourceEnv] using
        factorization.environmentAlignment.reconstructTarget
          targetEnv sourceWitness
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          sourceScope.frame.siteBody := by
      apply
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          pointwise).mpr
      rw [reconstructed]
      exact targetHolds
    let sourceLocalEnv :=
      factorization.context.sourceLocalEnvironment sourceEnv
    have sourceLocalHolds :
        denoteRegion model.toPreModel definitionEnv sourceLocalEnv
          (factorization.context.sourceBody sourceScope.frame.siteBody) :=
      by
        apply
          (factorization.context.sourceBody_denotes model.toPreModel
            definitionEnv sourceLocalEnv sourceScope.frame.siteBody).mpr
        dsimp only [sourceLocalEnv]
        rw [factorization.context.sourceEnvironment_local]
        exact sourceHolds
    have sourceOuter :
        ∀ {signature : Sig}
            (value :
              Var factorization.context.siteOuter signature),
          sourceLocalEnv signature
              (Var.appendRight
                (localSignatures source.val
                  (source.val.wires wire).scope) value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceLocalEnvironment_outer]
      calc
        sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) =
          (targetEnv.extend sourceWitness) signature
            (separateVar factorization.sourceHead
              factorization.alignment.forward
              (factorization.context.sourceOuterEmbedding value)) := rfl
        _ =
          (targetEnv.extend sourceWitness) signature
            (.there
              (factorization.context.targetOuterEmbedding value)) := by
              rw [
                factorization.environmentAlignment.sourceOuter.agrees
                  value]
        _ =
          targetEnv signature
            (factorization.context.targetOuterEmbedding value) := rfl
        _ =
          targetLocalEnv signature
            (Var.appendRight
              (localSignatures result.checked.val
                (result.checked.val.wires result.targetWire).scope)
              value) :=
              factorization.context.targetEnvironment_outer
                targetLocalEnv value
        _ = siteEnv signature value :=
              extendValues_outer targetValues siteEnv value
    refine
      ⟨valuesFromEnv
          (localSignatures source.val (source.val.wires wire).scope)
          sourceLocalEnv, ?_⟩
    rw [extendValues_from
      (localSignatures source.val (source.val.wires wire).scope)
      sourceLocalEnv siteEnv sourceOuter]
    exact sourceLocalHolds

/--
The checked parallel factorization equates the complete local binder blocks:
diagonal witnesses introduce a split and intersection eliminates it.
-/
theorem parallelLocalDenotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    {sourceScope :
      SiteCompilation source (source.val.wires wire).scope}
    {targetScope :
      SiteCompilation result.checked
        (result.checked.val.wires result.firstWire).scope}
    (factorization :
      ContentAlignment.ParallelFactorization result sourceScope targetScope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    (siteEnv : Env model.toPreModel factorization.context.siteOuter) :
    denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures source.val (source.val.wires wire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter)
              (localSignatures source.val
                  (source.val.wires wire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.sourceBody
            sourceScope.frame.siteBody)) ↔
      denoteRegion model.toPreModel definitionEnv siteEnv
        ((DiagramContext.bindMany
          (localSignatures result.checked.val
            (result.checked.val.wires result.firstWire).scope)
          (.hole :
            DiagramContext definitions
              (localSignatures result.checked.val
                  (result.checked.val.wires result.firstWire).scope ++
                factorization.context.siteOuter)
              (localSignatures result.checked.val
                  (result.checked.val.wires result.firstWire).scope ++
                factorization.context.siteOuter))).fill
          (factorization.context.targetBody
            targetScope.frame.siteBody)) := by
  rw [denote_bindMany, denote_bindMany]
  constructor
  · rintro ⟨sourceValues, sourceLocalHolds⟩
    let sourceLocalEnv :=
      extendValues sourceValues siteEnv
    let sourceEnv :=
      factorization.context.sourceEnvironment sourceLocalEnv
    let sourceRelation :=
      sourceEnv _ factorization.sourceHead
    let commonEnv :
        Env model.toPreModel
          ((.rel factorization.arguments) ::
            (.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs) :=
      (sourceEnv.extend sourceRelation).extend sourceRelation
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          sourceScope.frame.siteBody :=
      (factorization.context.sourceBody_denotes model.toPreModel
        definitionEnv sourceLocalEnv sourceScope.frame.siteBody).mp
        sourceLocalHolds
    have pointwise :
        ∀ values,
          model.toPreModel.apply
              (commonEnv _ (.there (.there factorization.sourceHead)))
              values ↔
            (model.toPreModel.apply
                (commonEnv _ (.here :
                  Var
                    ((.rel factorization.arguments) ::
                      (.rel factorization.arguments) ::
                      sourceScope.frame.visible.sigs)
                    (.rel factorization.arguments)))
                values ∧
              model.toPreModel.apply
                (commonEnv _ (.there (.here :
                  Var
                    ((.rel factorization.arguments) ::
                      sourceScope.frame.visible.sigs)
                    (.rel factorization.arguments))))
                values) := by
      intro values
      change
        model.toPreModel.apply sourceRelation values ↔
          (model.toPreModel.apply sourceRelation values ∧
            model.toPreModel.apply sourceRelation values)
      constructor
      · intro holds
        exact ⟨holds, holds⟩
      · exact And.left
    let targetEnv : Env model.toPreModel targetScope.frame.visible.sigs :=
      Env.comp commonEnv
        (separateVar factorization.firstHead
          (separateVar factorization.secondHead
            factorization.alignment.backward))
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          targetScope.frame.siteBody := by
      apply
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          pointwise).mp
      simpa [commonEnv, ContentAlignment.weakenTwo, Env.comp] using
        sourceHolds
    let targetLocalEnv :=
      factorization.context.targetLocalEnvironment targetEnv
    have targetLocalHolds :
        denoteRegion model.toPreModel definitionEnv targetLocalEnv
          (factorization.context.targetBody targetScope.frame.siteBody) := by
      apply
        (factorization.context.targetBody_denotes model.toPreModel
          definitionEnv targetLocalEnv targetScope.frame.siteBody).mpr
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetEnvironment_local]
      exact targetHolds
    have targetOuter :
        ∀ {signature : Sig}
            (value :
              Var factorization.context.siteOuter signature),
          targetLocalEnv signature
              (Var.appendRight
                (localSignatures result.checked.val
                  (result.checked.val.wires result.firstWire).scope)
                value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [targetLocalEnv]
      rw [factorization.context.targetLocalEnvironment_outer]
      calc
        targetEnv signature
            (factorization.context.targetOuterEmbedding value) =
          commonEnv signature
            (separateVar factorization.firstHead
              (separateVar factorization.secondHead
                factorization.alignment.backward)
              (factorization.context.targetOuterEmbedding value)) := rfl
        _ =
          commonEnv signature
            (.there (.there
              (factorization.context.sourceOuterEmbedding value))) := by
              rw [
                factorization.environmentAlignment.targetOuter.agrees
                  value]
        _ =
          sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) := rfl
        _ =
          sourceLocalEnv signature
            (Var.appendRight
              (localSignatures source.val
                (source.val.wires wire).scope) value) :=
              factorization.context.sourceEnvironment_outer
                sourceLocalEnv value
        _ = siteEnv signature value :=
              extendValues_outer sourceValues siteEnv value
    refine
      ⟨valuesFromEnv
          (localSignatures result.checked.val
            (result.checked.val.wires result.firstWire).scope)
          targetLocalEnv, ?_⟩
    rw [extendValues_from
      (localSignatures result.checked.val
        (result.checked.val.wires result.firstWire).scope)
      targetLocalEnv siteEnv targetOuter]
    exact targetLocalHolds
  · rintro ⟨targetValues, targetLocalHolds⟩
    let targetLocalEnv :=
      extendValues targetValues siteEnv
    let targetEnv :=
      factorization.context.targetEnvironment targetLocalEnv
    let sourceWitness :
        model.toPreModel.Domain (.rel factorization.arguments) :=
      fun values =>
        targetEnv _ factorization.firstHead values ∧
          targetEnv _ factorization.secondHead values
    let sourceEnv : Env model.toPreModel sourceScope.frame.visible.sigs :=
      Env.comp (targetEnv.extend sourceWitness)
        (separateVar factorization.sourceHead
          factorization.alignment.forward)
    let commonEnv :
        Env model.toPreModel
          ((.rel factorization.arguments) ::
            (.rel factorization.arguments) ::
            sourceScope.frame.visible.sigs) :=
      (sourceEnv.extend
        (targetEnv _ factorization.secondHead)).extend
          (targetEnv _ factorization.firstHead)
    have targetHolds :
        denoteRegion model.toPreModel definitionEnv targetEnv
          targetScope.frame.siteBody :=
      (factorization.context.targetBody_denotes model.toPreModel
        definitionEnv targetLocalEnv targetScope.frame.siteBody).mp
        targetLocalHolds
    have pointwise :
        ∀ values,
          model.toPreModel.apply
              (commonEnv _ (.there (.there factorization.sourceHead)))
              values ↔
            (model.toPreModel.apply
                (commonEnv _ (.here :
                  Var
                    ((.rel factorization.arguments) ::
                      (.rel factorization.arguments) ::
                      sourceScope.frame.visible.sigs)
                    (.rel factorization.arguments)))
                values ∧
              model.toPreModel.apply
                (commonEnv _ (.there (.here :
                  Var
                    ((.rel factorization.arguments) ::
                      sourceScope.frame.visible.sigs)
                    (.rel factorization.arguments))))
                values) := by
      intro values
      simp [commonEnv, sourceEnv, sourceWitness, Env.comp,
        ContentAlignment.separateVar]
      change
        (targetEnv _ factorization.firstHead
            (PreModel.Args.toFull values) ∧
          targetEnv _ factorization.secondHead
            (PreModel.Args.toFull values)) ↔
          (targetEnv _ factorization.firstHead
              (PreModel.Args.toFull values) ∧
            targetEnv _ factorization.secondHead
              (PreModel.Args.toFull values))
      exact Iff.rfl
    have reconstructed :
        Env.comp commonEnv
            (separateVar factorization.firstHead
              (separateVar factorization.secondHead
                factorization.alignment.backward)) =
          targetEnv := by
      simpa [commonEnv, sourceEnv] using
        factorization.environmentAlignment.reconstructTarget
          targetEnv sourceWitness
    have sourceHolds :
        denoteRegion model.toPreModel definitionEnv sourceEnv
          sourceScope.frame.siteBody := by
      apply
        (factorization.denotes model.toPreModel definitionEnv commonEnv
          pointwise).mpr
      rw [reconstructed]
      exact targetHolds
    let sourceLocalEnv :=
      factorization.context.sourceLocalEnvironment sourceEnv
    have sourceLocalHolds :
        denoteRegion model.toPreModel definitionEnv sourceLocalEnv
          (factorization.context.sourceBody sourceScope.frame.siteBody) := by
      apply
        (factorization.context.sourceBody_denotes model.toPreModel
          definitionEnv sourceLocalEnv sourceScope.frame.siteBody).mpr
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceEnvironment_local]
      exact sourceHolds
    have sourceOuter :
        ∀ {signature : Sig}
            (value :
              Var factorization.context.siteOuter signature),
          sourceLocalEnv signature
              (Var.appendRight
                (localSignatures source.val
                  (source.val.wires wire).scope) value) =
            siteEnv signature value := by
      intro signature value
      dsimp only [sourceLocalEnv]
      rw [factorization.context.sourceLocalEnvironment_outer]
      calc
        sourceEnv signature
            (factorization.context.sourceOuterEmbedding value) =
          (targetEnv.extend sourceWitness) signature
            (separateVar factorization.sourceHead
              factorization.alignment.forward
              (factorization.context.sourceOuterEmbedding value)) := rfl
        _ =
          (targetEnv.extend sourceWitness) signature
            (.there
              (factorization.context.targetOuterEmbedding value)) := by
              rw [
                factorization.environmentAlignment.sourceOuter.agrees
                  value]
        _ =
          targetEnv signature
            (factorization.context.targetOuterEmbedding value) := rfl
        _ =
          targetLocalEnv signature
            (Var.appendRight
              (localSignatures result.checked.val
                (result.checked.val.wires result.firstWire).scope)
              value) :=
              factorization.context.targetEnvironment_outer
                targetLocalEnv value
        _ = siteEnv signature value :=
              extendValues_outer targetValues siteEnv value
    refine
      ⟨valuesFromEnv
          (localSignatures source.val (source.val.wires wire).scope)
          sourceLocalEnv, ?_⟩
    rw [extendValues_from
      (localSignatures source.val (source.val.wires wire).scope)
      sourceLocalEnv siteEnv sourceOuter]
    exact sourceLocalHolds

end ContentShapeSemantics

namespace CutWrapResult.SiteLedger

/-- Every accepted cut-wrap ledger is a whole-diagram equivalence. -/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : CutWrapResult source wire}
    (ledger : CutWrapResult.SiteLedger result)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes ledger.sourceScope
    model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes ledger.targetScope
      model.toPreModel definitionEnv]
  exact
    ledger.factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        ContentShapeSemantics.cutLocalDenotes ledger.factorization model
          definitionEnv siteEnv)

end CutWrapResult.SiteLedger

namespace ParallelSplitResult.SiteLedger

/-- Every accepted parallel-split ledger is a whole-diagram equivalence. -/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ParallelSplitResult source wire}
    (ledger : ParallelSplitResult.SiteLedger result)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv result.checked := by
  rw [ContentShapeSemantics.SiteCompilation.denotes ledger.sourceScope
    model.toPreModel definitionEnv,
    ContentShapeSemantics.SiteCompilation.denotes ledger.firstScope
      model.toPreModel definitionEnv]
  exact
    ledger.factorization.context.closeDenotes model.toPreModel definitionEnv
      (fun siteEnv =>
        ContentShapeSemantics.parallelLocalDenotes ledger.factorization model
          definitionEnv siteEnv)

end ParallelSplitResult.SiteLedger

end ConcreteWirePrimitive

end VisualProof
