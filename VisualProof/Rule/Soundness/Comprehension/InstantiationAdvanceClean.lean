import VisualProof.Rule.Soundness.Comprehension.InstantiationCleanSubtreeCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Inserted material is disjoint from every retained-frame subtree: following
parents from a frame region stays in the frame block and therefore cannot
reach a material region. -/
theorem material_not_encloses_frame
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (material : Fin input.pattern.val.diagram.regionCount)
    (hmaterial : input.binderSpine.IsMaterialRegion material)
    (frame : Fin input.frame.val.regionCount) :
    ¬ layout.plugRaw.Encloses (layout.bodyRegion material)
      (layout.frameRegion frame) := by
  rintro ⟨⟨steps, bound⟩, climb⟩
  induction steps generalizing frame with
  | zero =>
      have equality : layout.frameRegion frame =
          layout.bodyRegion material := by
        simpa [ConcreteDiagram.climb] using Option.some.inj climb
      rw [layout.bodyRegion_material material hmaterial] at equality
      exact layout.frameRegion_ne_materialRegion frame _ equality
  | succ steps induction =>
      cases frameRegion : input.frame.val.regions frame with
      | sheet =>
          simp [ConcreteDiagram.climb, Splice.Input.PlugLayout.plugRaw,
            frameRegion, Splice.Input.PlugLayout.mapFrameRegion,
            CRegion.parent?] at climb
      | cut parent =>
          have tail : layout.plugRaw.climb steps
              (layout.frameRegion parent) =
                some (layout.bodyRegion material) := by
            simpa [ConcreteDiagram.climb,
              Splice.Input.PlugLayout.plugRaw, frameRegion,
              Splice.Input.PlugLayout.mapFrameRegion, CRegion.parent?]
              using climb
          exact induction parent (by omega) tail
      | bubble parent arity =>
          have tail : layout.plugRaw.climb steps
              (layout.frameRegion parent) =
                some (layout.bodyRegion material) := by
            simpa [ConcreteDiagram.climb,
              Splice.Input.PlugLayout.plugRaw, frameRegion,
              Splice.Input.PlugLayout.mapFrameRegion, CRegion.parent?]
              using climb
          exact induction parent (by omega) tail

/-- Every inserted material subtree is clean for the next survivor compiler.
The executor records processed atoms solely as retained-frame node images. -/
theorem advance_material_clean
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (material : Fin comprehension.val.diagram.regionCount)
    (hmaterial : payload.binderSpine.IsMaterialRegion material) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    ∀ node, node ∈ next.processedAtoms →
      ¬ next.diagram.val.Encloses (layout.bodyRegion material)
        (next.diagram.val.nodes node).region := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  change ∀ node : Fin layout.nodeCount,
    node ∈ state.processedAtoms.map layout.frameNode ++
        [layout.frameNode atom] →
      ¬ layout.plugRaw.Encloses (layout.bodyRegion material)
        (layout.plugNode node).region
  intro node processed
  rw [List.mem_append] at processed
  obtain mapped | current := processed
  · obtain ⟨original, _, rfl⟩ := List.mem_map.mp mapped
    change ¬ layout.plugRaw.Encloses (layout.bodyRegion material)
      (layout.plugNode (layout.frameNode original)).region
    rw [layout.plugNode_frameNode, layout.mapFrameNode_region]
    exact material_not_encloses_frame layout material hmaterial
      (state.diagram.val.nodes original).region
  · have equality : node = layout.frameNode atom := by simpa using current
    subst node
    change ¬ layout.plugRaw.Encloses (layout.bodyRegion material)
      (layout.plugNode (layout.frameNode atom)).region
    rw [layout.plugNode_frameNode, layout.mapFrameNode_region]
    exact material_not_encloses_frame layout material hmaterial
      (state.diagram.val.nodes atom).region

/-- On every inserted material subtree, the next survivor compiler is exactly
the authoritative ordered compiler. -/
theorem advance_compileSurvivorRegion_eq_material
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    {rels : Theory.RelCtx}
    (fuel : Nat)
    (material : Fin comprehension.val.diagram.regionCount)
    (hmaterial : payload.binderSpine.IsMaterialRegion material)
    (context : ConcreteElaboration.WireContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val)
    (relBinders : ConcreteElaboration.BinderContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val rels) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    compileSurvivorRegion? signature next fuel (layout.bodyRegion material)
        context relBinders =
      ConcreteElaboration.compileRegion? signature next.diagram.val fuel
        (layout.bodyRegion material) context relBinders := by
  dsimp only
  apply compileSurvivorRegion_eq_of_clean_subtree
  exact advance_material_clean comprehension attachments binders payload state
    atom tail site arguments hadmissible material hmaterial

end InstantiationSemantic

end VisualProof.Rule
