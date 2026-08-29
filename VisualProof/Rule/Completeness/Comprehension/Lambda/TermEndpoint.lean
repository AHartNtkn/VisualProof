import VisualProof.Rule.Completeness.Comprehension.Lambda.TermSupport

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory
open WirePrimitive

/-- The selected-site endpoint transformation for a positional Lambda term
leaf. The recording payload is irrelevant to the primitive endpoint. -/
theorem positionalTermLeafEndpoint
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity))
    (site : (recordingOperation
      (Lambda.TermLeaf.operation freeArity term) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedStrict
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application)
        ((recordingOperation
          (Lambda.TermLeaf.operation freeArity term) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application)
        ((recordingOperation
          (Lambda.TermLeaf.operation freeArity term) originalArguments).site
            frame PUnit.unit application site) := by
  rcases site with ⟨⟨⟨termOutput, termPorts⟩, applicationEq⟩,
    recordedApplication⟩
  subst application
  have targetEq :
      (recordingOperation
        (Lambda.TermLeaf.operation freeArity term) originalArguments).site
          frame PUnit.unit (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts)
          ⟨⟨⟨termOutput, termPorts⟩, rfl⟩, recordedApplication⟩ =
        positionalTermApplication freeArity term
          (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts) := by
    change Region.singleton (.term (frame.targetKeep termOutput) freeArity
      (fun slot => frame.targetKeep (termPorts slot)) term) = _
    rw [targetKeepEq]
    simp [positionalTermApplication, WireRenaming.id]
  rw [targetEq]
  refine ⟨?_, positionalTermInstantiation_scope freeArity term
    (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts)⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedApplication :=
    (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts).map
      fun wire => rename wire
  let positional :=
    VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalTermPattern freeArity term) mappedApplication
  let direct := positionalTermApplication freeArity term mappedApplication
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalTermPattern freeArity term)
      (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts)).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems positional
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [sourceBefore, sourceAfter, positional, mappedApplication,
      EqualityNormalization.instantiate_renameWires]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter := RegionIso.ofEq sourceEq
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical (fun _ => by rw [sourceEq]) sourcePresentation
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((positionalTermApplication freeArity term
      (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts)).renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems direct
  have targetEq' : targetBefore = targetAfter := by
    simp only [targetBefore, targetAfter, direct, mappedApplication,
      positionalTermApplication, Region.singleton_renameWires,
      Item.renameWires, Lambda.TermLeaf.Vars.fromTerm_map,
      Lambda.TermLeaf.Vars.output_fromTerm,
      Lambda.TermLeaf.Vars.ports_fromTerm]
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetAfterCanonical :
      (presentedOccurrence.context.fill targetAfter).Canonical := by
    rw [← targetEq']
    exact targetCanonical
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill targetAfter) := by
    intro wireSignature wire
    rw [← targetEq']
    exact targetExternalTwoEnded wire
  let targetOpen := presentedOccurrence.interface.withBody
    (presentedOccurrence.context.fill targetAfter) targetAfterCanonical
      targetAfterExternalTwoEnded
  let directOccurrence : Occurrence targetAfter targetOpen :=
    exactOccurrence presentedOccurrence.interface presentedOccurrence.context
      targetAfter targetAfterCanonical targetAfterExternalTwoEnded
  have core := equatesPositionalTermApplication freeArity term
    mappedApplication directOccurrence presentedOccurrence.sourceCanonical
      presentedOccurrence.sourceExternalTwoEnded
  let targetIso : OpenDiagramIso targetOpen
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetAfterCanonical targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context
        (RegionIso.ofEq targetEq'.symm))
  exact ⟨transGen_iso presentedOccurrence.host_iso.symm core.2 targetIso,
    transGen_iso targetIso core.1 presentedOccurrence.host_iso.symm⟩

end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
