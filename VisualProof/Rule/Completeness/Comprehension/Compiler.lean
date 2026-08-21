import VisualProof.Rule.Completeness.Comprehension.Telescope

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Compiler

/-- Compile a singleton retained atom through the formal-application leaf at
the comprehension binder's home occurrence. -/
theorem itemsAtom
    {outer localBefore localAfter before after : List Sig}
    {pattern : OpenDiagram
      (before ++ .rel (before ++ after) :: after)}
    (head : Var (outer ++ (localBefore ++ localAfter))
      (.rel (before ++ after)))
    (ports : Vars (outer ++ (localBefore ++ localAfter))
      (before ++ after))
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil
        ((Region.singleton (.atom head ports)).conjoin
          (Region.blank (outer ++ (localBefore ++ localAfter)))))
      (.mk
        (localBefore ++
          .rel (before ++ .rel (before ++ after) :: after) :: localAfter)
        (.cons
          (.atom
            ((Leaf.Formal.rootFrame outer localBefore localAfter before after).sourceKeep
              head)
            (ports.map fun wire =>
              (Leaf.Formal.rootFrame outer localBefore localAfter before after).sourceKeep
                wire))
          .nil))) :
    request.Result := by
  let frame := Leaf.Formal.rootFrame outer localBefore localAfter before after
  let itemEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        frame.sourceKeep frame.selected
        (.atom (frame.sourceKeep head)
          (ports.map fun wire => frame.sourceKeep wire))
        (Region.singleton (.atom head ports)) :=
    .atom head ports
  let tailEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        frame.sourceKeep frame.selected .nil
        (Region.blank (outer ++ (localBefore ++ localAfter))) :=
    .nil
  let evidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      itemEvidence tailEvidence
  let sites : ItemsSites (Leaf.Formal.operation before after) PUnit.unit
      evidence :=
    .cons (.atom (pattern := pattern) head ports) (.nil tailEvidence)
  exact items (operation := Leaf.Formal.operation before after)
    (frame := frame) PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Formal.Applies.Description outer := {
            before := before
            after := after
            localBefore := localBefore
            localAfter := localAfter
            items := .cons
              (.atom (frame.sourceKeep head)
                (ports.map fun wire => frame.sourceKeep wire))
              .nil
            itemsEdit := edit
          }
          have argumentsNe :
              before ++ .rel (before ++ after) :: after ≠ before ++ after := by
            intro equality
            have lengths := congrArg List.length equality
            simp only [List.length_append, List.length_cons] at lengths
            omega
          have runResult : edit.run =
              (Region.singleton (.atom head ports)).conjoin
                (Region.blank (outer ++ (localBefore ++ localAfter))) := by
            simpa only [frame, Leaf.Formal.rootFrame] using
              Transform.ItemsEdit.run_singletonAtom
                (operation := Leaf.Formal.operation before after)
                argumentsNe head ports edit
          have preparedEq :
              Region.adjoinAt (localBefore ++ localAfter) .nil
                  ((Region.singleton (.atom head ports)).conjoin
                    (Region.blank
                      (outer ++ (localBefore ++ localAfter)))) =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton (.atom head ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter)))) =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runResult]
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                (.cons
                  (.atom
                    ((Leaf.Formal.rootFrame outer localBefore localAfter
                      before after).sourceKeep head)
                    (ports.map fun wire =>
                      (Leaf.Formal.rootFrame outer localBefore localAfter
                        before after).sourceKeep wire))
                  .nil) : Region outer) =
                description.source := by
            rfl
          have rawPreparedCanonical :
              (request.occurrence.context.fill
                description.target).Canonical := by
            rw [← preparedEq]
            exact request.instantiatedCanonical
          have rawPreparedExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.target) := by
            rw [← preparedEq]
            exact request.instantiatedExternalTwoEnded
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have preparedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton (.atom head ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter)))))
              description.target := by
            rw [← preparedEq]
            exact RegionIso.refl _
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                (.cons
                  (.atom
                    ((Leaf.Formal.rootFrame outer localBefore localAfter
                      before after).sourceKeep head)
                    (ports.map fun wire =>
                      (Leaf.Formal.rootFrame outer localBefore localAfter
                        before after).sourceKeep wire))
                  .nil))
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch
              (Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton (.atom head ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter))))) := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Formal.Local
            inject := fun step => Step.formalApplication step
            preparedCanonical := request.instantiatedCanonical
            preparedExternalTwoEnded :=
              request.instantiatedExternalTwoEnded
            rawPreparedCanonical := rawPreparedCanonical
            rawPreparedExternalTwoEnded := rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparedIso
            pendingIso := pendingIso
            localStep := .abstractFormal (.mk description)
            preparation := Telescope.refl request.polarity
              request.occurrence.interface request.occurrence.context
              request.instantiatedCanonical
              request.instantiatedExternalTwoEnded request.continuation.1
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

/-- Compile a singleton retained identity through the identity leaf at the
comprehension binder's home occurrence. -/
theorem itemsIdentity
    {outer localBefore localAfter : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram (List.replicate arity signature)}
    (ports : Fin arity →
      Var (outer ++ (localBefore ++ localAfter)) signature)
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil
        ((Region.singleton (.identity signature arity ports)).conjoin
          (Region.blank (outer ++ (localBefore ++ localAfter)))))
      (.mk
        (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
        (.cons
          (.identity signature arity fun position =>
            (Leaf.Identity.rootFrame outer localBefore localAfter signature
              arity).sourceKeep (ports position))
          .nil))) :
    request.Result := by
  let frame := Leaf.Identity.rootFrame outer localBefore localAfter signature
    arity
  let itemEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        frame.sourceKeep frame.selected
        (.identity signature arity fun position =>
          frame.sourceKeep (ports position))
        (Region.singleton (.identity signature arity ports)) :=
    .identity signature arity ports
  let tailEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        frame.sourceKeep frame.selected .nil
        (Region.blank (outer ++ (localBefore ++ localAfter))) :=
    .nil
  let evidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      itemEvidence tailEvidence
  let sites : ItemsSites (Leaf.Identity.operation signature arity) PUnit.unit
      evidence :=
    .cons (.identity (pattern := pattern) signature arity ports)
      (.nil tailEvidence)
  exact items (operation := Leaf.Identity.operation signature arity)
    (frame := frame) PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Identity.Leaves.Description outer := {
            signature := signature
            arity := arity
            localBefore := localBefore
            localAfter := localAfter
            items := .cons
              (.identity signature arity fun position =>
                frame.sourceKeep (ports position))
              .nil
            itemsEdit := edit
          }
          have runResult : edit.run =
              (Region.singleton (.identity signature arity ports)).conjoin
                (Region.blank (outer ++ (localBefore ++ localAfter))) := by
            simpa only [frame, Leaf.Identity.rootFrame] using
              Transform.ItemsEdit.run_singletonIdentity
                (operation := Leaf.Identity.operation signature arity)
                signature arity ports edit
          have preparedEq :
              Region.adjoinAt (localBefore ++ localAfter) .nil
                  ((Region.singleton
                    (.identity signature arity ports)).conjoin
                    (Region.blank
                      (outer ++ (localBefore ++ localAfter)))) =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton
                  (.identity signature arity ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter)))) =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runResult]
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                (.cons
                  (.identity signature arity fun position =>
                    (Leaf.Identity.rootFrame outer localBefore localAfter
                      signature arity).sourceKeep (ports position))
                  .nil) : Region outer) =
                description.source := by
            rfl
          have rawPreparedCanonical :
              (request.occurrence.context.fill
                description.target).Canonical := by
            rw [← preparedEq]
            exact request.instantiatedCanonical
          have rawPreparedExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.target) := by
            rw [← preparedEq]
            exact request.instantiatedExternalTwoEnded
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have preparedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton
                  (.identity signature arity ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter)))))
              description.target := by
            rw [← preparedEq]
            exact RegionIso.refl _
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                (.cons
                  (.identity signature arity fun position =>
                    (Leaf.Identity.rootFrame outer localBefore localAfter
                      signature arity).sourceKeep (ports position))
                  .nil))
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch
              (Region.adjoinAt (localBefore ++ localAfter) .nil
                ((Region.singleton
                  (.identity signature arity ports)).conjoin
                  (Region.blank
                    (outer ++ (localBefore ++ localAfter))))) := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Identity.Local
            inject := fun step => Step.identityLeaf step
            preparedCanonical := request.instantiatedCanonical
            preparedExternalTwoEnded :=
              request.instantiatedExternalTwoEnded
            rawPreparedCanonical := rawPreparedCanonical
            rawPreparedExternalTwoEnded := rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparedIso
            pendingIso := pendingIso
            localStep := .abstractIdentity (.mk description)
            preparation := Telescope.refl request.polarity
              request.occurrence.interface request.occurrence.context
              request.instantiatedCanonical
              request.instantiatedExternalTwoEnded request.continuation.1
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

end Compiler

end VisualProof.Rule.Completeness.Comprehension
