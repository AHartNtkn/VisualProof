import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- On a subtree containing no processed atom, the survivor compiler is the
authoritative compiler.  The proof follows the actual ordered occurrence
compiler and propagates cleanliness only through certified direct children. -/
theorem compileSurvivorRegion_eq_of_clean_subtree
    {signature : List Nat}
    (state : InstantiationState origin parameterCount proxyCount) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (region : Fin state.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext state.diagram.val)
      (binders : ConcreteElaboration.BinderContext state.diagram.val rels),
      (∀ node, node ∈ state.processedAtoms →
        ¬ state.diagram.val.Encloses region
          (state.diagram.val.nodes node).region) →
      compileSurvivorRegion? signature state fuel region context binders =
        ConcreteElaboration.compileRegion? signature state.diagram.val fuel
          region context binders := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region context binders clean
      rfl
  | succ fuel ih =>
      intro region context binders clean
      let occurrences :=
        ConcreteElaboration.localOccurrences state.diagram.val region
      have allSurvive : occurrences.filter (dropOccurrenceSurvives state) =
          occurrences := by
        apply List.filter_eq_self.mpr
        intro occurrence member
        cases occurrence with
        | node node =>
            simp only [dropOccurrenceSurvives, instantiationAtomDomain,
              decide_eq_true_eq]
            intro processed
            apply clean node processed
            have localEq :=
              (ConcreteElaboration.mem_localOccurrences_node
                state.diagram.val region node).1 member
            rw [localEq]
            exact ConcreteDiagram.Encloses.refl state.diagram.val region
        | child child => rfl
      have compileListEq : ∀
          (items : List (ConcreteElaboration.LocalOccurrence
            state.diagram.val.regionCount state.diagram.val.nodeCount)),
          (∀ occurrence, occurrence ∈ items → occurrence ∈ occurrences) →
          ConcreteElaboration.compileOccurrencesWith? signature
              state.diagram.val (compileSurvivorRegion? signature state fuel)
              (context.extend region) binders items =
            ConcreteElaboration.compileOccurrencesWith? signature
              state.diagram.val
              (ConcreteElaboration.compileRegion? signature state.diagram.val
                fuel)
              (context.extend region) binders items := by
        intro items subset
        induction items with
        | nil => rfl
        | cons occurrence tail induction =>
            have headMember : occurrence ∈ occurrences :=
              subset occurrence (by simp)
            have tailSubset : ∀ current, current ∈ tail →
                current ∈ occurrences := by
              intro current currentMember
              exact subset current (by simp [currentMember])
            have tailEq := induction tailSubset
            have headEq :
                ConcreteElaboration.compileOccurrenceWith? signature
                    state.diagram.val
                    (compileSurvivorRegion? signature state fuel)
                    (context.extend region) binders occurrence =
                  ConcreteElaboration.compileOccurrenceWith? signature
                    state.diagram.val
                    (ConcreteElaboration.compileRegion? signature
                      state.diagram.val fuel)
                    (context.extend region) binders occurrence := by
              cases occurrence with
              | node node => rfl
              | child child =>
                  have parentEq :=
                    (ConcreteElaboration.mem_localOccurrences_child
                      state.diagram.val region child).1 headMember
                  have parentEncloses : state.diagram.val.Encloses region
                      child := by
                    have positive : 0 < state.diagram.val.regionCount :=
                      Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
                    refine ⟨⟨1, by omega⟩, ?_⟩
                    simp [ConcreteDiagram.climb, parentEq]
                  have childClean : ∀ node,
                      node ∈ state.processedAtoms →
                        ¬ state.diagram.val.Encloses child
                          (state.diagram.val.nodes node).region := by
                    intro node processed childEncloses
                    exact clean node processed
                      (ConcreteElaboration.checked_encloses_trans
                        state.diagram.property parentEncloses childEncloses)
                  have recurseEq := ih child (context.extend region) binders
                    childClean
                  cases hregion : state.diagram.val.regions child with
                  | sheet =>
                      simp [ConcreteElaboration.compileOccurrenceWith?,
                        hregion]
                  | cut parent =>
                      simp only [ConcreteElaboration.compileOccurrenceWith?,
                        hregion]
                      rw [recurseEq]
                  | bubble parent arity =>
                      simp only [ConcreteElaboration.compileOccurrenceWith?,
                        hregion]
                      rw [ih child (context.extend region)
                        (binders.push child arity) childClean]
            simp only [ConcreteElaboration.compileOccurrencesWith?]
            rw [headEq, tailEq]
      unfold compileSurvivorRegion? ConcreteElaboration.compileRegion?
      dsimp only
      rw [allSurvive]
      rw [compileListEq occurrences (fun _ member => member)]

end InstantiationSemantic

end VisualProof.Rule
