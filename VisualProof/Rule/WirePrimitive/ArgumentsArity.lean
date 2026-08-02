import VisualProof.Rule.WirePrimitive.ArgumentsCore

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

structure AppliedArityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.ScopedArityShiftLedger result sourceArguments
      newArgument
  private accepted :
    ConcreteWirePrimitive.arityShift source wire newArgument = .ok result
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact :
    result.spec.localCount = result.sites.sites.length

structure AppliedArityUnshift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private fixedSignature : Sig
  private ledger :
    ArgumentsSemantics.ScopedArityUnshiftLedger result sourceArguments
      fixedSignature
  private accepted :
    ConcreteWirePrimitive.arityUnshift source wire position = .ok result
  private local_count_exact : result.spec.localCount = 0
  private removed_local_exact :
    ∀ sourceWire, sourceWire ∈ result.spec.removedWires →
      ∃ site, site ∈ result.sites.sites ∧
        (source.val.wires sourceWire).endpoints =
          [⟨site.node, .arg position⟩]


namespace AppliedArityShift

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (_ : AppliedArityShift source wire newArgument) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :=
  applied.result

/-- Exhaustive source application sites of the shifted head. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    AllAppliedSites source wire :=
  applied.result.sites

/-- Arity shift removes only its acted source head. -/
theorem sourceRemovedWires_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    applied.argumentResult.sourceRemovedWires = [wire] :=
  applied.source_removed_exact

/-- The exact source relation argument vector selected by the checker. -/
def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) : List Sig :=
  applied.sourceArguments

/-- Exact relation signature of the live source wire. -/
theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :=
  applied.result.target

/-- The replacement relation wire allocated by this checked rewrite. -/
def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    applied.target.val.WireId :=
  applied.result.targetWire

/-- Exhaustive applied sites on the replacement relation wire. -/
def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.frame.targetSites

/-- Canonical generated target node for one ordered source site. -/
def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.NodeId :=
  applied.result.targetNode site

/-- Canonical fresh local argument wire corresponding to one ordered source
site. -/
def targetLocalWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.WireId :=
  applied.result.targetLocalWire
    (Fin.cast applied.local_count_exact.symm site)

/-- Every indexed shift-local wire belongs to the construction's exact
fresh-local block. -/
theorem targetLocalWire_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (site : Fin applied.sourceSites.sites.length) :
    applied.targetLocalWire site ∈
      applied.argumentResult.targetLocalWires := by
  unfold targetLocalWire ConcreteWirePrimitive.ArgumentResult.targetLocalWires
  apply List.mem_map.mpr
  exact ⟨Fin.cast applied.local_count_exact.symm site,
    Data.Finite.mem_allFin _, rfl⟩

/-- The shift construction's removed target block consists exactly of its
fresh head and one indexed local wire per source site. -/
theorem targetRemovedWire_cases
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (targetWire : applied.target.val.WireId)
    (removed : targetWire ∈
      applied.argumentResult.targetRemovedWires) :
    targetWire = applied.targetWire ∨
      ∃ site : Fin applied.sourceSites.sites.length,
        targetWire = applied.targetLocalWire site := by
  unfold ConcreteWirePrimitive.ArgumentResult.targetRemovedWires at removed
  rcases List.mem_cons.mp removed with head | removedLocal
  · exact Or.inl head
  · unfold ConcreteWirePrimitive.ArgumentResult.targetLocalWires at removedLocal
    rcases List.mem_map.mp removedLocal with ⟨fresh, _member, exact⟩
    right
    let site : Fin applied.sourceSites.sites.length :=
      Fin.cast applied.local_count_exact fresh
    refine ⟨site, exact.symm.trans ?_⟩
    unfold targetLocalWire
    congr 2

/-- Arity shift appends exactly one argument signature. -/
theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    applied.result.targetArguments =
      applied.sourceArgumentList ++ [newArgument] := by
  unfold sourceArgumentList
  calc
    applied.result.targetArguments =
        ConcreteWirePrimitive.insertAt applied.sourceArguments
          applied.ledger.insertion.position newArgument :=
      applied.ledger.insertion.largerExact.symm
    _ = ConcreteWirePrimitive.insertAt applied.sourceArguments
          applied.sourceArguments.length newArgument := by
      rw [applied.ledger.position_exact]
    _ = applied.sourceArguments ++ [newArgument] := by
      induction applied.sourceArguments with
      | nil => rfl
      | cons head tail induction =>
          simp [ConcreteWirePrimitive.insertAt, induction]

/-- The appended argument port of each generated shift node is owned by its
exact construction-local wire. -/
theorem targetNode_local_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site,
          .arg (applied.sourceSites.sites.get site).arguments.length⟩ =
      some (applied.targetLocalWire site) := by
  have sourceLength :
      (applied.sourceSites.sites.get site).arguments.length =
      applied.sourceArgumentList.length := by
    exact (applied.sourceSites.sites.get site).arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          applied.sourceArgumentList applied.sourceWire_signature
          (applied.sourceSites.sites.get site)))
  have referenceBound :
      (applied.sourceSites.sites.get site).arguments.length <
      (applied.result.spec.arguments site).length := by
    change
      (applied.result.sites.sites.get site).arguments.length <
        (applied.result.spec.arguments site).length
    rw [ArgumentsSemantics.arityShift_spec_arguments_length source wire
      applied.sourceArgumentList applied.sourceWire_signature
      applied.sourceSites newArgument applied.result applied.accepted]
    simp
  have targetBound :
      (applied.sourceSites.sites.get site).arguments.length <
      applied.result.targetArguments.length := by
    rw [applied.targetArguments_exact, sourceLength]
    simp
  have owner :=
    ArgumentsSemantics.arityShift_targetNode_local_owner source wire
      applied.sourceArgumentList applied.sourceWire_signature
      applied.sourceSites newArgument applied.result applied.accepted site
      referenceBound targetBound
  simpa [targetNode, targetLocalWire] using owner

/-- Every retained argument coordinate of a generated shift node is owned
by the exact construction image of its source-site attachment. -/
theorem targetNode_existing_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (site : Fin applied.sourceSites.sites.length)
    (index : Nat)
    (bound : index <
      (applied.sourceSites.sites.get site).arguments.length) :
    applied.target.val.endpointOwner?
        ⟨applied.targetNode site, .arg index⟩ =
      some (applied.argumentResult.retainedWireImage
        ((applied.sourceSites.sites.get site).arguments[index]'bound) (by
          rw [applied.sourceRemovedWires_exact]
          simpa using
            (applied.sourceSites.sites.get site).argument_ne_head
              index bound)) := by
  let sourceSite := applied.sourceSites.sites.get site
  have sourceLength : sourceSite.arguments.length =
      applied.sourceArgumentList.length :=
    sourceSite.arguments_length.trans
      (congrArg List.length
        (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
          applied.sourceArgumentList applied.sourceWire_signature sourceSite))
  have rawLength :
      (applied.argumentResult.sites.sites.get site).arguments.length =
        applied.sourceArgumentList.length := by
    simpa [sourceSite, sourceSites, argumentResult] using sourceLength
  have referenceBound : index <
      (applied.argumentResult.spec.arguments site).length := by
    rw [ArgumentsSemantics.arityShift_spec_arguments_length source wire
      applied.sourceArgumentList applied.sourceWire_signature
      applied.sourceSites newArgument applied.argumentResult applied.accepted]
    rw [rawLength]
    rw [sourceLength] at bound
    omega
  have targetBound : index <
      applied.argumentResult.targetArguments.length := by
    change index < applied.result.targetArguments.length
    rw [applied.targetArguments_exact, List.length_append]
    simp only [List.length_singleton, Nat.add_comm]
    rw [sourceLength] at bound
    omega
  have owner := ArgumentsSemantics.arityShift_targetNode_existing_owner
    source wire applied.sourceArgumentList applied.sourceWire_signature
    applied.sourceSites newArgument applied.argumentResult applied.accepted
    site index bound referenceBound targetBound
  have rawRetained :
      (applied.argumentResult.sites.sites.get site).arguments[index]'
          (by simpa [sourceSites, argumentResult] using bound) ∉
      applied.argumentResult.sourceRemovedWires := by
    rw [applied.sourceRemovedWires_exact]
    simpa using
      (applied.argumentResult.sites.sites.get site).argument_ne_head
        index (by simpa [sourceSites, argumentResult] using bound)
  have contextExact :=
    applied.argumentResult.contextWireMap_retained
      ((applied.argumentResult.sites.sites.get site).arguments[index]'
        (by simpa [sourceSites, argumentResult] using bound)) rawRetained
  have final := owner.trans (congrArg some contextExact)
  simpa [sourceSite, sourceSites, argumentResult] using final

/-- Exact relation signature of the fresh live wire. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    (applied.target.val.wires applied.targetWire).sig =
      .rel (applied.sourceArgumentList ++ [newArgument]) := by
  change
    (applied.result.checked.val.wires applied.result.targetWire).sig =
      .rel (applied.sourceArgumentList ++ [newArgument])
  rw [applied.result.targetWire_signature,
    applied.targetArguments_exact]

/-- Exact target image of a retained source wire. -/
def transportRetainedWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.target.val.WireId :=
  applied.result.retainedWire sourceWire (by
    unfold ConcreteWireQuantifier.Internal.retainedWires
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin sourceWire, ?_⟩
    rw [applied.source_removed_exact]
    simp [different])

/-- Arity-shift ambient transport preserves the exact wire signature. -/
theorem transportRetainedWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires
        (applied.transportRetainedWire sourceWire different)).sig =
      (source.val.wires sourceWire).sig :=
  applied.result.retainedWire_signature sourceWire _

/-- The image of a retained ambient wire cannot be the fresh live head. -/
theorem transportRetainedWire_ne_targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.transportRetainedWire sourceWire different ≠
      applied.targetWire :=
  applied.result.retainedWire_ne_targetWire sourceWire _

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (_ : AppliedArityShift source wire newArgument) : StepTag :=
  .arityShift

end AppliedArityShift

namespace AppliedArityUnshift

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArityUnshift source wire position) := source

/-- Checker-owned concrete construction receipt for transport proofs. -/
def argumentResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :=
  applied.result

/-- Exhaustive source application sites of the unshifted head. -/
def sourceSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    AllAppliedSites source wire :=
  applied.result.sites

/-- Exact source argument vector selected by arity unshift. -/
def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) : List Sig :=
  applied.sourceArguments

/-- Exact relation signature of the unshift source head. -/
theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

/-- Exact target argument vector produced by the accepted unshift. -/
theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    applied.argumentResult.targetArguments =
      ConcreteWirePrimitive.eraseAt applied.sourceArgumentList position := by
  exact ConcreteWirePrimitive.arityUnshift_targetArguments_exact source wire
    applied.sourceArgumentList applied.sourceWire_signature position
    applied.argumentResult applied.accepted

/-- Exact ordered retained attachment tuple at each accepted unshift site. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.argumentResult.spec.arguments site =
      existingReferences
        (ConcreteWirePrimitive.eraseAt
          (applied.sourceSites.sites.get site).arguments position) := by
  exact ConcreteWirePrimitive.arityUnshift_arguments_exact source wire
    applied.sourceArgumentList applied.sourceWire_signature position
    applied.argumentResult applied.accepted site


def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

/-- Canonical generated target node for one ordered source site. -/
def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position)
    (site : Fin applied.sourceSites.sites.length) :
    applied.target.val.NodeId :=
  applied.result.targetNode site

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.frame.targetSites

/-- Arity unshift creates no local target wires, so its generated removal
block consists only of the replacement head. -/
theorem targetRemovedWires_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    applied.argumentResult.targetRemovedWires = [applied.targetWire] := by
  exact applied.result.targetRemovedWires_headOnly applied.local_count_exact

/-- Full source removal set: the acted head followed by every selected local
argument wire. -/
def sourceRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    List source.val.WireId :=
  applied.result.sourceRemovedWires

/-- Every removed non-head wire is one checked singleton local argument. -/
theorem removedLocal_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position)
    (sourceWire : source.val.WireId)
    (removed : sourceWire ∈ applied.result.spec.removedWires) :
    ∃ site, site ∈ applied.sourceSites.sites ∧
      (source.val.wires sourceWire).endpoints =
        [⟨site.node, .arg position⟩] :=
  applied.removed_local_exact sourceWire removed

/-- Every source site owns one checked singleton local wire selected for
unshift removal. -/
theorem siteLocal_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position)
    (site : Fin applied.sourceSites.sites.length) :
    ∃ sourceWire, sourceWire ∈ applied.result.spec.removedWires ∧
      (source.val.wires sourceWire).endpoints =
        [⟨(applied.sourceSites.sites.get site).node, .arg position⟩] := by
  exact ConcreteWirePrimitive.arityUnshift_site_local_removed source wire
    position applied.result applied.accepted site

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArityUnshift source wire position) : StepTag :=
  .arityUnshift

end AppliedArityUnshift

def applyArityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) :
    Except WireArgumentError
      (AppliedArityShift source wire newArgument) := by
  match accepted :
      ConcreteWirePrimitive.arityShift source wire newArgument with
  | .error error => exact .error (.concreteRejected error)
  | .ok result =>
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => exact .error .semanticLedgerRejected
      | .rel sourceArguments =>
          match ledgerAccepted :
              ArgumentsSemantics.checkScopedArityShiftLedger result
                sourceArguments sourceSignature newArgument with
          | none =>
              have complete :=
                ArgumentsSemantics.checkScopedArityShiftLedger_complete_of_accepted
                  sourceArguments sourceSignature newArgument result accepted
              simp [ledgerAccepted] at complete
          | some ledger =>
              exact .ok
                ⟨result, sourceArguments, sourceSignature, ledger,
                  accepted,
                  ConcreteWirePrimitive.arityShift_sourceRemovedWires_exact
                    source wire newArgument result accepted,
                  ConcreteWirePrimitive.arityShift_localCount_exact source
                    wire sourceArguments sourceSignature result.sites
                    newArgument result accepted⟩

def applyArityUnshift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArityUnshift source wire position) := do
  match accepted :
      ConcreteWirePrimitive.arityUnshift source wire position with
  | .error error => throw (.concreteRejected error)
  | .ok result =>
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      match _fixedExact : sourceArguments[position]? with
      | none => throw .semanticLedgerRejected
      | some fixedSignature => do
          let ledger ←
            Internal.optionToExcept .semanticLedgerRejected <|
              ArgumentsSemantics.checkScopedArityUnshiftLedger result
                sourceArguments sourceSignature position fixedSignature
          pure
            ⟨result, sourceArguments, sourceSignature, fixedSignature,
              ledger, accepted,
              ConcreteWirePrimitive.arityUnshift_localCount_exact source wire
                position result accepted,
              ConcreteWirePrimitive.arityUnshift_removedWire_local_exact
                source wire position result accepted⟩


theorem arity_shift_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (newArgument : Sig)
    (applied : AppliedArityShift source wire newArgument)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked arity unshift is the inverse full-model cylindrification. -/
theorem arity_unshift_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArityUnshift source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

end Arguments

end WirePrimitive

end VisualProof
