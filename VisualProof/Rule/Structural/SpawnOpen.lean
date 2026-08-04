import VisualProof.Rule.Structural.SpawnTransport

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

/-- Reverse semantic obligation when the spawn site is the open root sheet. -/
def SpawnRootSiteReflection
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) : Prop :=
  ∀ (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
      []),
    ConcreteElaboration.compileRoot? signature source.val.diagram
        source.val.exposedWires source.val.hiddenWires = some sourceBody →
      ConcreteElaboration.compileRoot? signature
          (spawnNodeRaw source.val.diagram node scope portCount port)
          (spawnNodeRawOpen source.val node scope portCount port).exposedWires
          (spawnNodeRawOpen source.val node scope portCount port).hiddenWires =
            some targetBody →
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin
          (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
            → model.Carrier),
        denoteRegion (relCtx := []) model named
            (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
              portCount port) PUnit.unit sourceBody →
          denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody

/-- A root-site callback is needed only when the spawn site is the root.
Keeping that condition opaque lets descendant-route induction avoid carrying
an irrelevant impossible root obligation. -/
def SpawnRootSiteReflectionAtRoot
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) : Prop :=
  source.val.diagram.root = scope →
    SpawnRootSiteReflection source node scope portCount port

/-- Shared root compiler split for projection and optional reflection. -/
private theorem spawnNodeRaw_compileRoot_route_kernel
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
      [])
    (hsourceBody : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (htargetBody : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram node scope portCount port)
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires
      (spawnNodeRawOpen source.val node scope portCount port).hiddenWires =
        some targetBody) :
    ((∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 0 →
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody →
        denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody) ∧
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 1 →
      denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody →
        denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody)) ∧
    ((SpawnRootSiteReflectionAtRoot source node scope portCount port ∧
        SpawnRegionSiteReflection (signature := signature) source.val.diagram node
          scope portCount port) →
      ((∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin
          (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
            model.Carrier),
        depth % 2 = 0 →
        denoteRegion (relCtx := []) model named
            (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
              portCount port) PUnit.unit sourceBody →
          denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody) ∧
      (∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin
          (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
            model.Carrier),
        depth % 2 = 1 →
        denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody →
          denoteRegion (relCtx := []) model named
            (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
              portCount port) PUnit.unit sourceBody))) := by
  let input := source.val.diagram
  let spawnScope := scope
  let targetOpen := spawnNodeRawOpen source.val node spawnScope portCount port
  cases route with
  | here =>
      cases hdepth
      constructor
      · constructor
        · intro model named outerEnv _ hdenotes
          exact spawnNodeRaw_compileRoot_site_projects source node spawnScope
            portCount port hnode rfl htarget sourceBody targetBody hsourceBody
            htargetBody model named outerEnv hdenotes
        · intro _ _ _ hodd
          simp at hodd
      · rintro ⟨hrootReflect, _⟩
        constructor
        · intro model named outerEnv _ hdenotes
          exact hrootReflect rfl sourceBody targetBody hsourceBody htargetBody model
            named outerEnv hdenotes
        · intro _ _ _ hodd
          simp at hodd
  | @step _ child _ rest hparent position hposition tail =>
      have hne : input.root ≠ spawnScope := by
        intro heq
        have hrootScope : input.root = scope := by exact heq
        have htailEncloses :=
          regionRoute_encloses input source.property.diagram_well_formed tail
        rw [← hrootScope] at htailEncloses
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          source.property.diagram_well_formed hparent)
          htailEncloses
      change ConcreteElaboration.compileRoot? signature input
          source.val.exposedWires source.val.hiddenWires = some sourceBody
        at hsourceBody
      change ConcreteElaboration.compileRoot? signature targetOpen.diagram
          targetOpen.exposedWires targetOpen.hiddenWires = some targetBody
        at htargetBody
      simp only [ConcreteElaboration.compileRoot?] at hsourceBody htargetBody
      change (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input input.regionCount)
        source.val.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input input.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot
            source.val.exposedWires source.val.hiddenWires items)) =
        some sourceBody at hsourceBody
      change (ConcreteElaboration.compileOccurrencesWith? signature
        targetOpen.diagram
        (ConcreteElaboration.compileRegion? signature targetOpen.diagram
          input.regionCount) targetOpen.rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences targetOpen.diagram input.root)).bind
          (fun items => some (ConcreteElaboration.finishRoot
            targetOpen.exposedWires targetOpen.hiddenWires items)) =
        some targetBody at htargetBody
      cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
          input (ConcreteElaboration.compileRegion? signature input
            input.regionCount) source.val.rootWires
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences input input.root) with
      | none => simp [hsourceItems] at hsourceBody
      | some sourceItems =>
        simp only [hsourceItems, Option.bind_some, Option.some.injEq]
          at hsourceBody
        cases hsourceBody
        cases htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
            targetOpen.diagram
            (ConcreteElaboration.compileRegion? signature targetOpen.diagram
              input.regionCount) targetOpen.rootWires
            ConcreteElaboration.BinderContext.empty
            (ConcreteElaboration.localOccurrences targetOpen.diagram input.root) with
        | none => simp [input, targetOpen, htargetItems] at htargetBody
        | some targetItems =>
          simp only [htargetItems, Option.bind_some, Option.some.injEq]
            at htargetBody
          cases htargetBody
          obtain ⟨before, after, hlocal, hbeforeAway, hafterAway⟩ :=
            localOccurrences_split_at_child input input.root child position
              hposition
          have htargetLocal :
              ConcreteElaboration.localOccurrences targetOpen.diagram input.root =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            change ConcreteElaboration.localOccurrences
                (spawnNodeRaw input node spawnScope portCount port) input.root = _
            rw [spawnNodeRaw_localOccurrences_old_of_ne input node spawnScope
              input.root portCount port hnode hne, hlocal]
          have hsourceFramed := hsourceItems
          rw [hlocal] at hsourceFramed
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, hsourceBefore,
              hsourceFocus, hsourceAfter, hsourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input
                input.regionCount) source.val.rootWires
              ConcreteElaboration.BinderContext.empty before after (.child child)
              sourceItems hsourceFramed
          have htargetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                targetOpen.diagram
                (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                  input.regionCount) targetOpen.rootWires
                ConcreteElaboration.BinderContext.empty
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← htargetLocal]
            exact htargetItems
          obtain ⟨targetBefore, targetFocus, targetAfter, htargetBefore,
              htargetFocus, htargetAfter, htargetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                input.regionCount) targetOpen.rootWires
              ConcreteElaboration.BinderContext.empty
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              htargetFramed
          cases hcount : input.regionCount with
          | zero =>
            let impossible : Fin 0 := Fin.cast (by simpa [hcount]) child
            exact Fin.elim0 impossible
          | succ childFuel =>
            let embedding := spawnNodeRawOpenRootEmbeddingAway source.val node
              spawnScope portCount port hne
            have hsourceExact := OpenConcreteDiagram.rootWires_exact source.val
              source.property
            have htargetOpenWf := spawnNodeRawOpen_wellFormed source node spawnScope
              portCount port htarget
            have htargetExact := OpenConcreteDiagram.rootWires_exact targetOpen
              htargetOpenWf
            have hbeforeMap := spawnNodeRaw_compileRootOccurrencesAway input node
              spawnScope child portCount port
              source.property.diagram_well_formed htarget hnode hparent tail
              input.regionCount source.val.rootWires targetOpen.rootWires
              embedding hsourceExact htargetExact before (by
                intro occurrence hmem
                rw [hlocal]
                simp [hmem]) hbeforeAway
            change ConcreteElaboration.compileOccurrencesWith? signature
                targetOpen.diagram
                (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                  input.regionCount) targetOpen.rootWires
                ConcreteElaboration.BinderContext.empty
                (before.map (spawnNodeRaw_oldOccurrence input)) = _
              at hbeforeMap
            rw [hsourceBefore, htargetBefore] at hbeforeMap
            have hbeforeEq : targetBefore = sourceBefore.renameWires
                embedding.index := Option.some.inj hbeforeMap
            have hafterMap := spawnNodeRaw_compileRootOccurrencesAway input node
              spawnScope child portCount port
              source.property.diagram_well_formed htarget hnode hparent tail
              input.regionCount source.val.rootWires targetOpen.rootWires
              embedding hsourceExact htargetExact after (by
                intro occurrence hmem
                rw [hlocal]
                simp [hmem]) hafterAway
            change ConcreteElaboration.compileOccurrencesWith? signature
                targetOpen.diagram
                (ConcreteElaboration.compileRegion? signature targetOpen.diagram
                  input.regionCount) targetOpen.rootWires
                ConcreteElaboration.BinderContext.empty
                (after.map (spawnNodeRaw_oldOccurrence input)) = _
              at hafterMap
            rw [hsourceAfter, htargetAfter] at hafterMap
            have hafterEq : targetAfter = sourceAfter.renameWires
                embedding.index := Option.some.inj hafterMap
            obtain ⟨tailDepth, tailDepthProof⟩ :=
              regionRoute_hasCutDepth_exists
                source.property.diagram_well_formed tail
            change (input.regions child).parent? = some input.root at hparent
            cases childRegion : input.regions child with
            | sheet =>
              rw [childRegion] at hparent
              contradiction
            | cut parent =>
              have hparentEq : parent = input.root := by
                simpa [childRegion, CRegion.parent?] using hparent
              subst parent
              have child_is_cut : input.regions child = .cut input.root :=
                childRegion
              have headDepth :
                  (Diagram.Splice.RegionRoute.step hparent position hposition
                    tail).HasCutDepth (tailDepth + 1) :=
                .cut (hparent := hparent) (hposition := hposition)
                  child_is_cut tailDepthProof
              have hdepthRel : depth = tailDepth + 1 :=
                regionRoute_cutDepth_unique hdepth headDepth
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                child_is_cut] at hsourceFocus
              simp only [spawnNodeRaw_oldOccurrence,
                ConcreteElaboration.compileOccurrenceWith?] at htargetFocus
              rw [show targetOpen.diagram.regions child = input.regions child
                by rfl, childRegion] at htargetFocus
              simp only at htargetFocus
              change (ConcreteElaboration.compileRegion? signature
                targetOpen.diagram input.regionCount child targetOpen.rootWires
                ConcreteElaboration.BinderContext.empty).bind
                  (fun body => some (Item.cut body)) = some targetFocus
                at htargetFocus
              rw [hcount] at hsourceFocus htargetFocus
              cases hsourceChild : ConcreteElaboration.compileRegion? signature
                  input (childFuel + 1) child source.val.rootWires
                  ConcreteElaboration.BinderContext.empty with
              | none => simp [hsourceChild] at hsourceFocus
              | some sourceChild =>
                simp [hsourceChild] at hsourceFocus
                subst sourceFocus
                cases htargetChild : ConcreteElaboration.compileRegion? signature
                    targetOpen.diagram (childFuel + 1) child targetOpen.rootWires
                    ConcreteElaboration.BinderContext.empty with
                | none => simp [htargetChild] at htargetFocus
                | some targetChild =>
                  simp [htargetChild] at htargetFocus
                  subst targetFocus
                  have hchild := spawnNodeRaw_compileRegion_route_projects input
                    node spawnScope portCount port source.property.diagram_well_formed
                    htarget hnode tail tailDepthProof childFuel source.val.rootWires
                    targetOpen.rootWires embedding
                    ConcreteElaboration.BinderContext.empty
                    (hsourceExact.extend_child source.property.diagram_well_formed
                      hparent)
                    (htargetExact.extend_child htarget hparent)
                    sourceChild targetChild hsourceChild htargetChild
                  constructor
                  · constructor
                    · intro model named outerEnv heven hdenotes
                      have htailOdd : tailDepth % 2 = 1 := by omega
                      apply spawnNodeRaw_finishRoot_away_projects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame] at hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame]
                      rcases hitems with ⟨hb, hf, ha⟩
                      refine ⟨hb, ?_, ha⟩
                      intro hs
                      have hs' := (denoteRegion_renameWires (relCtx := [])
                        currentModel currentNamed embedding.index rawEnv
                        PUnit.unit sourceChild).1 hs
                      exact hf (hchild.2 currentModel currentNamed rawEnv
                        PUnit.unit htailOdd hs')
                    · intro model named outerEnv hodd hdenotes
                      have htailEven : tailDepth % 2 = 0 := by omega
                      apply spawnNodeRaw_finishRoot_away_reflects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hb, hf, ha⟩
                      refine ⟨hb, ?_, ha⟩
                      intro ht
                      have hs := hchild.1 currentModel currentNamed rawEnv
                        PUnit.unit htailEven ht
                      exact hf ((denoteRegion_renameWires (relCtx := [])
                        currentModel currentNamed embedding.index rawEnv
                        PUnit.unit sourceChild).2 hs)
                  · rintro ⟨_, hregionReflect⟩
                    have hchildReverse :=
                      spawnNodeRaw_compileRegion_route_reflects input node
                        spawnScope portCount port
                        source.property.diagram_well_formed htarget hnode
                        hregionReflect tail tailDepthProof childFuel
                        source.val.rootWires targetOpen.rootWires embedding
                        ConcreteElaboration.BinderContext.empty
                        (hsourceExact.extend_child
                          source.property.diagram_well_formed hparent)
                        (htargetExact.extend_child htarget hparent)
                        sourceChild targetChild hsourceChild htargetChild
                    constructor
                    · intro model named outerEnv heven hdenotes
                      have htailOdd : tailDepth % 2 = 1 := by omega
                      apply spawnNodeRaw_finishRoot_away_reflects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hb, hf, ha⟩
                      refine ⟨hb, ?_, ha⟩
                      intro ht
                      have hs := hchildReverse.2 currentModel currentNamed rawEnv
                        PUnit.unit htailOdd ht
                      exact hf ((denoteRegion_renameWires (relCtx := [])
                        currentModel currentNamed embedding.index rawEnv
                        PUnit.unit sourceChild).2 hs)
                    · intro model named outerEnv hodd hdenotes
                      have htailEven : tailDepth % 2 = 0 := by omega
                      apply spawnNodeRaw_finishRoot_away_projects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame] at hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame]
                      rcases hitems with ⟨hb, hf, ha⟩
                      refine ⟨hb, ?_, ha⟩
                      intro hs
                      have hs' := (denoteRegion_renameWires (relCtx := [])
                        currentModel currentNamed embedding.index rawEnv
                        PUnit.unit sourceChild).1 hs
                      exact hf (hchildReverse.1 currentModel currentNamed rawEnv
                        PUnit.unit htailEven hs')
            | bubble parent arity =>
              have hparentEq : parent = input.root := by
                simpa [childRegion, CRegion.parent?] using hparent
              subst parent
              have child_is_bubble :
                  input.regions child = .bubble input.root arity := childRegion
              have headDepth :
                  (Diagram.Splice.RegionRoute.step hparent position hposition
                    tail).HasCutDepth tailDepth :=
                .bubble (hparent := hparent) (hposition := hposition)
                  child_is_bubble tailDepthProof
              have hdepthRel : depth = tailDepth :=
                regionRoute_cutDepth_unique hdepth headDepth
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                child_is_bubble] at hsourceFocus
              simp only [spawnNodeRaw_oldOccurrence,
                ConcreteElaboration.compileOccurrenceWith?] at htargetFocus
              rw [show targetOpen.diagram.regions child = input.regions child
                by rfl, childRegion] at htargetFocus
              simp only at htargetFocus
              change (ConcreteElaboration.compileRegion? signature
                targetOpen.diagram input.regionCount child targetOpen.rootWires
                (ConcreteElaboration.BinderContext.empty.push child _)).bind
                  (fun body => some (Item.bubble _ body)) = some targetFocus
                at htargetFocus
              rw [hcount] at hsourceFocus htargetFocus
              cases hsourceChild : ConcreteElaboration.compileRegion? signature
                  input (childFuel + 1) child source.val.rootWires
                  (ConcreteElaboration.BinderContext.empty.push child arity) with
              | none => simp [hsourceChild] at hsourceFocus
              | some sourceChild =>
                simp [hsourceChild] at hsourceFocus
                subst sourceFocus
                cases htargetChild : ConcreteElaboration.compileRegion? signature
                    targetOpen.diagram (childFuel + 1) child targetOpen.rootWires
                    (ConcreteElaboration.BinderContext.empty.push child arity) with
                | none => simp [htargetChild] at htargetFocus
                | some targetChild =>
                  simp [htargetChild] at htargetFocus
                  subst targetFocus
                  have hchild := spawnNodeRaw_compileRegion_route_projects input
                    node spawnScope portCount port source.property.diagram_well_formed
                    htarget hnode tail tailDepthProof childFuel source.val.rootWires
                    targetOpen.rootWires embedding
                    (ConcreteElaboration.BinderContext.empty.push child arity)
                    (hsourceExact.extend_child source.property.diagram_well_formed
                      hparent)
                    (htargetExact.extend_child htarget hparent)
                    sourceChild targetChild hsourceChild htargetChild
                  constructor
                  · constructor
                    · intro model named outerEnv heven hdenotes
                      apply spawnNodeRaw_finishRoot_away_projects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame] at hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame]
                      rcases hitems with ⟨hb, ⟨relation, hf⟩, ha⟩
                      refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                      have hs := hchild.1 currentModel currentNamed rawEnv
                        (relation, PUnit.unit) (by omega) hf
                      exact (denoteRegion_renameWires (relCtx := [arity])
                        currentModel currentNamed embedding.index rawEnv
                        (relation, PUnit.unit) sourceChild).2 hs
                    · intro model named outerEnv hodd hdenotes
                      apply spawnNodeRaw_finishRoot_away_reflects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hb, ⟨relation, hf⟩, ha⟩
                      refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                      have hs := (denoteRegion_renameWires (relCtx := [arity])
                        currentModel currentNamed embedding.index rawEnv
                        (relation, PUnit.unit) sourceChild).1 hf
                      exact hchild.2 currentModel currentNamed rawEnv
                        (relation, PUnit.unit) (by omega) hs
                  · rintro ⟨_, hregionReflect⟩
                    have hchildReverse :=
                      spawnNodeRaw_compileRegion_route_reflects input node
                        spawnScope portCount port
                        source.property.diagram_well_formed htarget hnode
                        hregionReflect tail tailDepthProof childFuel
                        source.val.rootWires targetOpen.rootWires embedding
                        (ConcreteElaboration.BinderContext.empty.push child arity)
                        (hsourceExact.extend_child
                          source.property.diagram_well_formed hparent)
                        (htargetExact.extend_child htarget hparent)
                        sourceChild targetChild hsourceChild htargetChild
                    constructor
                    · intro model named outerEnv heven hdenotes
                      apply spawnNodeRaw_finishRoot_away_reflects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame] at hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame]
                      rcases hitems with ⟨hb, ⟨relation, hf⟩, ha⟩
                      refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                      have hs := (denoteRegion_renameWires (relCtx := [arity])
                        currentModel currentNamed embedding.index rawEnv
                        (relation, PUnit.unit) sourceChild).1 hf
                      exact hchildReverse.1 currentModel currentNamed rawEnv
                        (relation, PUnit.unit) (by omega) hs
                    · intro model named outerEnv hodd hdenotes
                      apply spawnNodeRaw_finishRoot_away_projects source.val node
                        spawnScope portCount port hne sourceItems targetItems _
                        model named outerEnv hdenotes
                      intro currentModel currentNamed rawEnv hitems
                      rw [htargetItemsEq, hbeforeEq, hafterEq,
                        denoteItemSeq_frame] at hitems
                      rw [hsourceItemsEq, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame]
                      rcases hitems with ⟨hb, ⟨relation, hf⟩, ha⟩
                      refine ⟨hb, ⟨relation, ?_⟩, ha⟩
                      have hs := hchildReverse.2 currentModel currentNamed rawEnv
                        (relation, PUnit.unit) (by omega) hf
                      exact (denoteRegion_renameWires (relCtx := [arity])
                        currentModel currentNamed embedding.index rawEnv
                        (relation, PUnit.unit) sourceChild).2 hs

/-- The route projection lifted through the open sheet compiler. -/
theorem spawnNodeRaw_compileRoot_route_projects
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
      [])
    (hsourceBody : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (htargetBody : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram node scope portCount port)
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires
      (spawnNodeRawOpen source.val node scope portCount port).hiddenWires =
        some targetBody) :
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 0 →
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody →
        denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody) ∧
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 1 →
      denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody →
        denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody) :=
  (spawnNodeRaw_compileRoot_route_kernel source node scope portCount port hnode
    htarget route hdepth sourceBody targetBody hsourceBody htargetBody).1

/-- Reverse transport through the open root compiler, sharing both the root
split and the descendant route kernel with ordinary spawn projection. -/
theorem spawnNodeRaw_compileRoot_route_reflects
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    (hrootReflect : SpawnRootSiteReflectionAtRoot source node scope portCount port)
    (hregionReflect : SpawnRegionSiteReflection (signature := signature)
      source.val.diagram node scope portCount port)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (sourceBody : Region signature source.val.exposedWires.length [])
    (targetBody : Region signature
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length
      [])
    (hsourceBody : ConcreteElaboration.compileRoot? signature
      source.val.diagram source.val.exposedWires source.val.hiddenWires =
        some sourceBody)
    (htargetBody : ConcreteElaboration.compileRoot? signature
      (spawnNodeRaw source.val.diagram node scope portCount port)
      (spawnNodeRawOpen source.val node scope portCount port).exposedWires
      (spawnNodeRawOpen source.val node scope portCount port).hiddenWires =
        some targetBody) :
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 0 →
      denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody →
        denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody) ∧
    (∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin
        (spawnNodeRawOpen source.val node scope portCount port).exposedWires.length →
          model.Carrier),
      depth % 2 = 1 →
      denoteRegion (relCtx := []) model named outerEnv PUnit.unit targetBody →
        denoteRegion (relCtx := []) model named
          (outerEnv ∘ spawnNodeRawOpenExternalClass source.val node scope
            portCount port) PUnit.unit sourceBody) :=
  (spawnNodeRaw_compileRoot_route_kernel source node scope portCount port hnode
    htarget route hdepth sourceBody targetBody hsourceBody htargetBody).2
      ⟨hrootReflect, hregionReflect⟩

/-- Public ordered-open semantic projection for raw spawn.  Boundary positions
and repeated aliases are transported positionwise; the implication direction
is exactly the route cut parity. -/
theorem spawnNodeRawOpen_projects
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let targetOpen := spawnNodeRawOpen source.val node scope portCount port
    let targetWf := spawnNodeRawOpen_wellFormed source node scope portCount port
      htarget
    let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
      by simp [targetOpen, spawnNodeRawOpen]
    (depth % 2 = 0 →
      targetOpen.denote targetWf model named (args ∘ Fin.cast boundaryLength) →
        source.denote model named args) ∧
    (depth % 2 = 1 →
      source.denote model named args →
        targetOpen.denote targetWf model named
          (args ∘ Fin.cast boundaryLength)) := by
  dsimp only
  let targetOpen := spawnNodeRawOpen source.val node scope portCount port
  let targetWf := spawnNodeRawOpen_wellFormed source node scope portCount port
    htarget
  let target : CheckedOpenDiagram signature := ⟨targetOpen, targetWf⟩
  let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
    by simp [targetOpen, spawnNodeRawOpen]
  obtain ⟨sourceBody, hsourceCompile, hsourceElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation source
  obtain ⟨targetBody, htargetCompile, htargetElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation target
  have hroot := spawnNodeRaw_compileRoot_route_projects source node scope
    portCount port hnode htarget route hdepth sourceBody targetBody
    hsourceCompile htargetCompile
  constructor
  · intro heven htargetDenotes
    change denoteOpen model named target.elaborate
        (args ∘ Fin.cast boundaryLength) at htargetDenotes
    rcases htargetDenotes with ⟨targetAssignment, htargetArgs, htargetBody⟩
    rw [htargetElaborate] at htargetBody
    let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
      args := args
      classes := targetAssignment.classes ∘
        spawnNodeRawOpenExternalClass source.val node scope portCount port
      agrees := by
        intro position
        have hclass := spawnNodeRawOpen_boundaryClass source.val node scope
          portCount port position
        have hagree := targetAssignment.agrees
          (spawnNodeRawOpenBoundaryPosition source.val node scope portCount port
            position)
        change targetAssignment.classes
            (target.val.boundaryClass
              (spawnNodeRawOpenBoundaryPosition source.val node scope portCount
                port position)) = _ at hagree
        rw [hclass] at hagree
        rw [htargetArgs] at hagree
        simpa [boundaryLength, spawnNodeRawOpenBoundaryPosition] using hagree
    }
    refine ⟨sourceAssignment, rfl, ?_⟩
    rw [hsourceElaborate]
    exact hroot.1 model named targetAssignment.classes heven htargetBody
  · intro hodd hsourceDenotes
    change denoteOpen model named source.elaborate args at hsourceDenotes
    rcases hsourceDenotes with ⟨sourceAssignment, hsourceArgs, hsourceBody⟩
    rw [hsourceElaborate] at hsourceBody
    let exposedLength : targetOpen.exposedWires.length =
        source.val.exposedWires.length := by
      rw [spawnNodeRawOpen_exposedWires]
      exact List.length_map _
    let targetClasses : Fin targetOpen.exposedWires.length → model.Carrier :=
      sourceAssignment.classes ∘ Fin.cast exposedLength
    have hsourceClasses : targetClasses ∘
        spawnNodeRawOpenExternalClass source.val node scope portCount port =
      sourceAssignment.classes := by
      funext external
      apply congrArg sourceAssignment.classes
      rfl
    let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
      args := args ∘ Fin.cast boundaryLength
      classes := targetClasses
      agrees := by
        intro targetPosition
        let sourcePosition : Fin source.val.boundary.length :=
          Fin.cast boundaryLength targetPosition
        have hclass := spawnNodeRawOpen_boundaryClass source.val node scope
          portCount port sourcePosition
        have hposition :
            spawnNodeRawOpenBoundaryPosition source.val node scope portCount port
              sourcePosition = targetPosition := by
          apply Fin.ext
          rfl
        rw [hposition] at hclass
        change sourceAssignment.classes
            (Fin.cast exposedLength
              (target.val.boundaryClass targetPosition)) = _
        have hbackClass : Fin.cast exposedLength
            (target.val.boundaryClass targetPosition) =
          source.val.boundaryClass sourcePosition := by
          rw [hclass]
          apply Fin.ext
          rfl
        calc
          sourceAssignment.classes
              (Fin.cast exposedLength
                (target.val.boundaryClass targetPosition)) =
            sourceAssignment.classes
              (source.val.boundaryClass sourcePosition) :=
                congrArg sourceAssignment.classes hbackClass
          _ = sourceAssignment.args sourcePosition :=
            sourceAssignment.agrees sourcePosition
          _ = args sourcePosition := congrFun hsourceArgs sourcePosition
          _ = (args ∘ Fin.cast boundaryLength) targetPosition := rfl
    }
    refine ⟨targetAssignment, rfl, ?_⟩
    rw [htargetElaborate]
    apply hroot.2 model named targetClasses hodd
    rw [hsourceClasses]
    exact hsourceBody

/-- Ordered-open reverse transport for equivalence-capable spawn
specializations.  Boundary positions and aliases use the same positional
transport as projection; only the route implication is reversed. -/
theorem spawnNodeRawOpen_reflects
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hnode : node.region = scope)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature)
    (hrootReflect : SpawnRootSiteReflectionAtRoot source node scope portCount port)
    (hregionReflect : SpawnRegionSiteReflection (signature := signature)
      source.val.diagram node scope portCount port)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute source.val.diagram
      source.val.diagram.root scope path)
    {depth : Nat} (hdepth : route.HasCutDepth depth)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let targetOpen := spawnNodeRawOpen source.val node scope portCount port
    let targetWf := spawnNodeRawOpen_wellFormed source node scope portCount port
      htarget
    let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
      by simp [targetOpen, spawnNodeRawOpen]
    (depth % 2 = 0 → source.denote model named args →
      targetOpen.denote targetWf model named (args ∘ Fin.cast boundaryLength)) ∧
    (depth % 2 = 1 →
      targetOpen.denote targetWf model named (args ∘ Fin.cast boundaryLength) →
        source.denote model named args) := by
  dsimp only
  let targetOpen := spawnNodeRawOpen source.val node scope portCount port
  let targetWf := spawnNodeRawOpen_wellFormed source node scope portCount port
    htarget
  let target : CheckedOpenDiagram signature := ⟨targetOpen, targetWf⟩
  let boundaryLength : targetOpen.boundary.length = source.val.boundary.length :=
    by simp [targetOpen, spawnNodeRawOpen]
  obtain ⟨sourceBody, hsourceCompile, hsourceElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation source
  obtain ⟨targetBody, htargetCompile, htargetElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation target
  have hroot := spawnNodeRaw_compileRoot_route_reflects source node scope
    portCount port hnode htarget hrootReflect hregionReflect route hdepth
    sourceBody targetBody hsourceCompile htargetCompile
  constructor
  · intro heven hsourceDenotes
    change denoteOpen model named source.elaborate args at hsourceDenotes
    rcases hsourceDenotes with ⟨sourceAssignment, hsourceArgs, hsourceBody⟩
    rw [hsourceElaborate] at hsourceBody
    let exposedLength : targetOpen.exposedWires.length =
        source.val.exposedWires.length := by
      rw [spawnNodeRawOpen_exposedWires]
      exact List.length_map _
    let targetClasses : Fin targetOpen.exposedWires.length → model.Carrier :=
      sourceAssignment.classes ∘ Fin.cast exposedLength
    have hsourceClasses : targetClasses ∘
        spawnNodeRawOpenExternalClass source.val node scope portCount port =
      sourceAssignment.classes := by
      funext external
      apply congrArg sourceAssignment.classes
      rfl
    let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
      args := args ∘ Fin.cast boundaryLength
      classes := targetClasses
      agrees := by
        intro targetPosition
        let sourcePosition : Fin source.val.boundary.length :=
          Fin.cast boundaryLength targetPosition
        have hclass := spawnNodeRawOpen_boundaryClass source.val node scope
          portCount port sourcePosition
        have hposition :
            spawnNodeRawOpenBoundaryPosition source.val node scope portCount port
              sourcePosition = targetPosition := by
          apply Fin.ext
          rfl
        rw [hposition] at hclass
        change sourceAssignment.classes
            (Fin.cast exposedLength (target.val.boundaryClass targetPosition)) = _
        have hbackClass : Fin.cast exposedLength
            (target.val.boundaryClass targetPosition) =
          source.val.boundaryClass sourcePosition := by
          rw [hclass]
          apply Fin.ext
          rfl
        calc
          sourceAssignment.classes
              (Fin.cast exposedLength
                (target.val.boundaryClass targetPosition)) =
            sourceAssignment.classes
              (source.val.boundaryClass sourcePosition) :=
                congrArg sourceAssignment.classes hbackClass
          _ = sourceAssignment.args sourcePosition :=
            sourceAssignment.agrees sourcePosition
          _ = args sourcePosition := congrFun hsourceArgs sourcePosition
          _ = (args ∘ Fin.cast boundaryLength) targetPosition := rfl
    }
    refine ⟨targetAssignment, rfl, ?_⟩
    rw [htargetElaborate]
    apply hroot.1 model named targetClasses heven
    rw [hsourceClasses]
    exact hsourceBody
  · intro hodd htargetDenotes
    change denoteOpen model named target.elaborate
        (args ∘ Fin.cast boundaryLength) at htargetDenotes
    rcases htargetDenotes with ⟨targetAssignment, htargetArgs, htargetBody⟩
    rw [htargetElaborate] at htargetBody
    let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
      args := args
      classes := targetAssignment.classes ∘
        spawnNodeRawOpenExternalClass source.val node scope portCount port
      agrees := by
        intro position
        have hclass := spawnNodeRawOpen_boundaryClass source.val node scope
          portCount port position
        have hagree := targetAssignment.agrees
          (spawnNodeRawOpenBoundaryPosition source.val node scope portCount port
            position)
        change targetAssignment.classes
            (target.val.boundaryClass
              (spawnNodeRawOpenBoundaryPosition source.val node scope portCount
                port position)) = _ at hagree
        rw [hclass] at hagree
        rw [htargetArgs] at hagree
        simpa [boundaryLength, spawnNodeRawOpenBoundaryPosition] using hagree
    }
    refine ⟨sourceAssignment, rfl, ?_⟩
    rw [hsourceElaborate]
    exact hroot.2 model named targetAssignment.classes hodd htargetBody

/-- Spawn is locally a target-to-source projection.  Odd cut depth consumes
that projection contravariantly for forward replay; even depth consumes it
covariantly for backward replay. -/
theorem spawn_context_sound
    (orientation : Orientation)
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (polarity : spawnPolarity orientation ctx.cutDepth)
    (localProjection : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv target →
        denoteRegion model named holeEnv holeRelEnv source) :
    DirectedImplication orientation
      (denoteRegion model named env rels (ctx.fill source))
      (denoteRegion model named env rels (ctx.fill target)) := by
  cases orientation with
  | forward =>
      exact context_anti model named env rels polarity localProjection
  | backward =>
      exact context_mono model named env rels polarity localProjection

/-- Reusable bidirectional semantic route lift.  A site equivalence is
transported through an arbitrary intrinsic context without choosing a rule
orientation; cuts reverse both implications together and bubbles preserve
them.  Closed-term spawn uses this theorem with the two site directions, so it
does not require another semantic context induction. -/
theorem context_equiv
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (localEquiv : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv source ↔
        denoteRegion model named holeEnv holeRelEnv target) :
    denoteRegion model named env rels (ctx.fill source) ↔
      denoteRegion model named env rels (ctx.fill target) := by
  by_cases heven : ctx.cutDepth % 2 = 0
  · constructor
    · exact context_mono model named env rels heven
        (fun holeEnv holeRelEnv => (localEquiv holeEnv holeRelEnv).mp)
    · exact context_mono model named env rels heven
        (fun holeEnv holeRelEnv => (localEquiv holeEnv holeRelEnv).mpr)
  · have hodd : ctx.cutDepth % 2 = 1 := by omega
    constructor
    · exact context_anti model named env rels hodd
        (fun holeEnv holeRelEnv => (localEquiv holeEnv holeRelEnv).mpr)
    · exact context_anti model named env rels hodd
        (fun holeEnv holeRelEnv => (localEquiv holeEnv holeRelEnv).mp)

/-- The sole concrete compiler produces an intrinsic item for the appended
node in every covering wire/binder context. -/
theorem spawnNodeRaw_compileNode?_complete
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hwf : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (context : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (binders : ConcreteElaboration.BinderContext
      (spawnNodeRaw input node scope portCount port) rels)
    (hwires : context.Covers scope) (hbinders : binders.Covers scope)
    (hregion : node.region = scope) :
    ∃ item, ConcreteElaboration.compileNode? signature
      (spawnNodeRaw input node scope portCount port) context binders
      (Fin.last input.nodeCount) = some item := by
  apply ConcreteElaboration.compileNode?_complete hwf hwires hbinders
  rw [spawnNodeRaw_newNode]
  exact hregion

private def checkRawReceipt (input : CheckedDiagram signature)
    (raw : ConcreteDiagram) (provenance : WireProvenance input.val raw)
    (interface : InterfaceTransport input.val raw) :
    Except StepError (StepReceipt input) :=
  match hcheck : checkWellFormed signature raw with
  | .error error => .error (.resultNotWellFormed error)
  | .ok result => .ok (StepReceipt.ofChecked input raw provenance interface
      result hcheck)

theorem castTarget_provenance_image_realizes
    (expected : WireProvenance source raw)
    (resultEq : result = raw) (wire : Fin source.wireCount) :
    Option.map (Fin.cast (congrArg ConcreteDiagram.wireCount resultEq))
        ((expected.castTarget resultEq.symm).image? wire) =
      expected.image? wire := by
  subst raw
  simp [WireProvenance.castTarget]

theorem castTarget_interface_image_realizes
    (expected : InterfaceTransport source raw)
    (resultEq : result = raw) (wire : Fin source.wireCount) :
    Option.map (Fin.cast (congrArg ConcreteDiagram.wireCount resultEq))
        ((expected.castTarget resultEq.symm).image? wire) =
      expected.image? wire := by
  subst raw
  simp [InterfaceTransport.castTarget]

def applyOpenTermSpawn (orientation : Orientation)
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) (freePorts : Nat)
    (term : Lambda.Term 0 (Fin freePorts)) :
    Except StepError (StepReceipt input) :=
  if spawnPolarity orientation
      (concreteCutDepth input.val region) then
    if 0 < freePorts then
      let raw := spawnNodeRaw input.val (.term region freePorts term) region
        (freePorts + 1) (Fin.cases .output fun index => .free index)
      checkRawReceipt input raw
        (spawnNodeWireProvenance input.val (.term region freePorts term) region
          (freePorts + 1) (Fin.cases .output fun index => .free index))
        (spawnNodeInterfaceTransport input.val (.term region freePorts term)
          region (freePorts + 1)
          (Fin.cases .output fun index => .free index))
    else
      .error .openTermRequired
  else
    .error .wrongPolarity

def applyRelationSpawn (orientation : Orientation)
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) (definition arity : Nat) :
    Except StepError (StepReceipt input) :=
  if spawnPolarity orientation
      (concreteCutDepth input.val region) then
    if signature[definition]? = some arity then
      let raw := spawnNodeRaw input.val (.named region definition arity)
        region arity (fun index => .arg index)
      checkRawReceipt input raw
        (spawnNodeWireProvenance input.val (.named region definition arity)
          region arity (fun index => .arg index))
        (spawnNodeInterfaceTransport input.val (.named region definition arity)
          region arity (fun index => .arg index))
    else
      .error .unknownDefinition
  else
    .error .wrongPolarity

def applyBoundRelationSpawn (orientation : Orientation)
    (input : CheckedDiagram signature)
    (region binder : Fin input.val.regionCount) (arity : Nat) :
    Except StepError (StepReceipt input) :=
  if spawnPolarity orientation
      (concreteCutDepth input.val region) then
    if input.val.binderArity? binder = some arity then
      if input.val.Encloses binder region then
        let raw := spawnNodeRaw input.val (.atom region binder) region arity
          (fun index => .arg index)
        checkRawReceipt input raw
          (spawnNodeWireProvenance input.val (.atom region binder) region arity
            (fun index => .arg index))
          (spawnNodeInterfaceTransport input.val (.atom region binder) region
            arity (fun index => .arg index))
      else
        .error .binderDoesNotEnclose
    else
      .error .binderKindOrArityMismatch
  else
    .error .wrongPolarity

theorem applyOpenTermSpawn_preserves_raw
    (happly : applyOpenTermSpawn orientation input region freePorts term =
      .ok result) :
    result.result.val = spawnNodeRaw input.val (.term region freePorts term) region
      (freePorts + 1) (Fin.cases .output fun index => .free index) := by
  unfold applyOpenTermSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyRelationSpawn_preserves_raw
    (happly : applyRelationSpawn orientation input region definition arity =
      .ok result) :
    result.result.val = spawnNodeRaw input.val (.named region definition arity)
      region arity (fun index => .arg index) := by
  unfold applyRelationSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyBoundRelationSpawn_preserves_raw
    (happly : applyBoundRelationSpawn orientation input region binder arity =
      .ok result) :
    result.result.val = spawnNodeRaw input.val (.atom region binder) region arity
      (fun index => .arg index) := by
  unfold applyBoundRelationSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact checkWellFormed_preserves_input hcheck

theorem applyOpenTermSpawn_realizes
    (happly : applyOpenTermSpawn orientation input region freePorts term =
      .ok result) :
    result.Realizes
      (spawnNodeRaw input.val (.term region freePorts term) region
        (freePorts + 1) (Fin.cases .output fun index => .free index))
      (spawnNodeWireProvenance input.val (.term region freePorts term) region
        (freePorts + 1) (Fin.cases .output fun index => .free index))
      (spawnNodeInterfaceTransport input.val (.term region freePorts term) region
        (freePorts + 1) (Fin.cases .output fun index => .free index)) := by
  unfold applyOpenTermSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

theorem applyRelationSpawn_realizes
    (happly : applyRelationSpawn orientation input region definition arity =
      .ok result) :
    result.Realizes
      (spawnNodeRaw input.val (.named region definition arity) region arity
        (fun index => .arg index))
      (spawnNodeWireProvenance input.val (.named region definition arity)
        region arity (fun index => .arg index))
      (spawnNodeInterfaceTransport input.val (.named region definition arity)
        region arity (fun index => .arg index)) := by
  unfold applyRelationSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

theorem applyBoundRelationSpawn_realizes
    (happly : applyBoundRelationSpawn orientation input region binder arity =
      .ok result) :
    result.Realizes
      (spawnNodeRaw input.val (.atom region binder) region arity
        (fun index => .arg index))
      (spawnNodeWireProvenance input.val (.atom region binder) region arity
        (fun index => .arg index))
      (spawnNodeInterfaceTransport input.val (.atom region binder) region arity
        (fun index => .arg index)) := by
  unfold applyBoundRelationSpawn at happly
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  split at happly <;> try contradiction
  dsimp only at happly
  unfold checkRawReceipt at happly
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck

theorem applyOpenTermSpawn_success {signature : List Nat}
    (orientation : Orientation) (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) (freePorts : Nat)
    (term : Lambda.Term 0 (Fin freePorts)) (result : StepReceipt input)
    (happly : applyOpenTermSpawn orientation input region freePorts term =
      .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val region) ∧
      0 < freePorts ∧
      result.result.val = spawnNodeRaw input.val
        (.term region freePorts term) region (freePorts + 1)
        (Fin.cases .output fun index => .free index) := by
  have hpolarity : spawnPolarity orientation
      (concreteCutDepth input.val region) := by
    by_cases h : spawnPolarity orientation
        (concreteCutDepth input.val region)
    · exact h
    · simp [applyOpenTermSpawn, h] at happly
  have hopen : 0 < freePorts := by
    by_cases h : 0 < freePorts
    · exact h
    · simp [applyOpenTermSpawn, hpolarity, h] at happly
  exact ⟨hpolarity, hopen, applyOpenTermSpawn_preserves_raw happly⟩

theorem applyRelationSpawn_success {signature : List Nat}
    (orientation : Orientation) (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount) (definition arity : Nat)
    (result : StepReceipt input)
    (happly : applyRelationSpawn orientation input region definition arity =
      .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val region) ∧
      signature[definition]? = some arity ∧
      result.result.val = spawnNodeRaw input.val
        (.named region definition arity) region arity
        (fun index => .arg index) := by
  have hpolarity : spawnPolarity orientation
      (concreteCutDepth input.val region) := by
    by_cases h : spawnPolarity orientation
        (concreteCutDepth input.val region)
    · exact h
    · simp [applyRelationSpawn, h] at happly
  have hdefinition : signature[definition]? = some arity := by
    by_cases h : signature[definition]? = some arity
    · exact h
    · simp [applyRelationSpawn, hpolarity, h] at happly
  exact ⟨hpolarity, hdefinition, applyRelationSpawn_preserves_raw happly⟩

theorem applyBoundRelationSpawn_success {signature : List Nat}
    (orientation : Orientation) (input : CheckedDiagram signature)
    (region binder : Fin input.val.regionCount) (arity : Nat)
    (result : StepReceipt input)
    (happly : applyBoundRelationSpawn orientation input region binder arity =
      .ok result) :
    spawnPolarity orientation (concreteCutDepth input.val region) ∧
      input.val.binderArity? binder = some arity ∧
      input.val.Encloses binder region ∧
      result.result.val = spawnNodeRaw input.val (.atom region binder) region
        arity (fun index => .arg index) := by
  have hpolarity : spawnPolarity orientation
      (concreteCutDepth input.val region) := by
    by_cases h : spawnPolarity orientation
        (concreteCutDepth input.val region)
    · exact h
    · simp [applyBoundRelationSpawn, h] at happly
  have harity : input.val.binderArity? binder = some arity := by
    by_cases h : input.val.binderArity? binder = some arity
    · exact h
    · simp [applyBoundRelationSpawn, hpolarity, h] at happly
  have hencloses : input.val.Encloses binder region := by
    by_cases h : input.val.Encloses binder region
    · exact h
    · simp [applyBoundRelationSpawn, hpolarity, harity, h] at happly
  exact ⟨hpolarity, harity, hencloses,
    applyBoundRelationSpawn_preserves_raw happly⟩

end VisualProof.Rule
