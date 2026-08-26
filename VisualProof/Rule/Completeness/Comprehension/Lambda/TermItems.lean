import VisualProof.Rule.Completeness.Comprehension.Sites
import VisualProof.Rule.Lambda.TermLeaf

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory

/-- Derive one complete selected-application layer through the Lambda term
leaf. The preparation is indexed by the deterministic all-sites edit endpoint,
and this theorem owns the single directed primitive at the binder home. -/
theorem itemsTerm
    {outer localBefore localAfter : List Sig}
    {freeArity : Nat} {term : VisualProof.Lambda.Term 0 (Fin freeArity)}
    {pattern : OpenDiagram (Lambda.TermLeaf.arguments freeArity)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (Lambda.TermLeaf.arguments freeArity) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    {instantiated : Region outer}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Lambda.TermLeaf.rootFrame outer localBefore localAfter
          freeArity).sourceKeep
        (Lambda.TermLeaf.rootFrame outer localBefore localAfter
          freeArity).selected
        source result)
    (sites : ItemsSites (Lambda.TermLeaf.operation freeArity term) PUnit.unit
      evidence)
    (request : Telescope.Request instantiated
      (.mk
        (localBefore ++
          .rel (Lambda.TermLeaf.arguments freeArity) :: localAfter)
        source))
    (prepare : request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        (itemsEdit (operation := Lambda.TermLeaf.operation freeArity term)
          PUnit.unit evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Lambda.TermLeaf.operation freeArity term)
      PUnit.unit evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
      let description : Lambda.TermLeaf.Leaves.Description outer := {
        freeArity := freeArity
        term := term
        localBefore := localBefore
        localAfter := localAfter
        items := source
        itemsEdit := edit
      }
      have stagedEq :
          Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
            description.target := by
        change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
          Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
        rw [runEq]
      let preparation : request.Preparation description.target :=
        stagedEq ▸ prepare
      have pendingEq :
          (.mk
            (localBefore ++
              .rel (Lambda.TermLeaf.arguments freeArity) :: localAfter)
            source : Region outer) = description.source := by
        rfl
      have rawPendingCanonical :
          (request.occurrence.context.fill description.source).Canonical := by
        rw [← pendingEq]
        exact request.pendingCanonical
      have rawPendingExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded
            request.occurrence.interface.boundaryWire
            (request.occurrence.context.fill description.source) := by
        rw [← pendingEq]
        exact request.pendingExternalTwoEnded
      have pendingIso : RegionIso (WireEquiv.refl outer)
          (.mk
            (localBefore ++
              .rel (Lambda.TermLeaf.arguments freeArity) :: localAfter)
            source)
          description.source := by
        rw [← pendingEq]
        exact RegionIso.refl _
      let branch : request.Branch preparation.prepared := {
        rawPrepared := description.target
        rawPending := description.source
        localRule := Lambda.TermLeaf.Local
        inject := fun step => Step.lambdaTermLeaf step
        preparedCanonical := preparation.preparedCanonical
        preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
        rawPreparedCanonical := preparation.rawPreparedCanonical
        rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
        rawPendingCanonical := rawPendingCanonical
        rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
        preparedIso := preparation.preparedIso
        pendingIso := pendingIso
        localStep := .abstractTerm (.mk description)
        preparation := preparation.telescope
      }
      exact branch.derive

end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
