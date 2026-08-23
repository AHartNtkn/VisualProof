import VisualProof.Rule.Completeness.Erasure.Exposure.Support

namespace VisualProof.Rule.Completeness.Erasure.Exposure

open Diagram
open Theory

def State.Supports
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) : Prop :=
  ∀ position : Fin signatures.length,
    ∀ localIndex : Fin state.locals.length,
      (state.materialMap
        ((variables.get position).appendLeft material.locals)).index.val =
          outer.length + localIndex.val →
      RegionPath.RootedTwo
        (state.before.incidencePaths
          (outer.length + localIndex.val) 0)

theorem State.advance_before_rooted
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (localIndex : Fin state.locals.length)
    (rooted : RegionPath.RootedTwo
      (state.before.incidencePaths
        (outer.length + localIndex.val) 0)) :
    RegionPath.RootedTwo
      ((state.advance selected).before.incidencePaths
        (outer.length + localIndex.val) 0) := by
  let wireIndex := outer.length + localIndex.val
  have shiftedRoot :=
    (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff
      state.before wireIndex 0 1).mpr rooted
  have renamedPaths :
      (state.before.renameWires
        (Identification.retainWire outer state.locals signature 1)).incidencePaths
          wireIndex 1 =
        state.before.incidencePaths wireIndex 1 := by
    apply ItemSeq.incidencePaths_renameWires_of_index_iff
    · have bound := localIndex.isLt
      simp only [wireIndex, List.length_append]
      omega
    · have bound := localIndex.isLt
      simp only [wireIndex, List.length_append]
      omega
    · intro wireSignature wire
      rw [retainWire_index]
  rw [← renamedPaths] at shiftedRoot
  apply RegionPath.RootedTwo.of_sublist ?_ shiftedRoot
  simp only [State.advance, ItemSeq.incidencePaths, Nat.zero_add]
  exact List.sublist_append_right _ _

theorem State.supports_advance_tail
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (tail : Vars materialWires signatures)
    (injective : VariablesIndexInjective (Vars.cons selected tail))
    (supported : state.Supports (.cons selected tail)) :
    (state.advance selected).Supports tail := by
  intro position localIndex targetIndex
  let wire := tail.get position
  have different : wire.index.val ≠ selected.index.val := by
    intro equality
    have positionsEqual :
        (Fin.succ position : Fin (signature :: signatures).length) = 0 := by
      apply injective
      simpa [wire] using equality
    have values := congrArg Fin.val positionsEqual
    simp at values
  have redirected := redirectMaterial_other_external state.materialMap
    selected wire different
  have retainedIndex := congrArg (fun mapped => mapped.index.val) redirected
  change
    (redirectMaterial state.materialMap selected
      (wire.appendLeft material.locals)).index.val =
      (Identification.retainWire outer state.locals signature 1
        (state.materialMap
          (wire.appendLeft material.locals))).index.val at retainedIndex
  rw [retainWire_index] at retainedIndex
  have old : localIndex.val < state.locals.length := by
    by_cases isOld : localIndex.val < state.locals.length
    · exact isOld
    have bound := localIndex.isLt
    change localIndex.val < (state.locals ++ [signature]).length at bound
    have freshValue : localIndex.val = state.locals.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    have freshIndex :
        (Identification.freshLocalWire outer state.locals signature
          (0 : Fin 1)).index.val = outer.length + localIndex.val := by
      simp [Identification.freshLocalWire, freshValue]
    have redirectedFresh :
        (redirectMaterial state.materialMap selected
          (wire.appendLeft material.locals)).index.val =
            (Identification.freshLocalWire outer state.locals signature
              (0 : Fin 1)).index.val := targetIndex.trans freshIndex.symm
    have sourceEqual :=
      (redirectMaterial_fresh_index_iff state.materialMap selected
        (wire.appendLeft material.locals)).mp redirectedFresh
    have externalEqual : wire.index.val = selected.index.val := by
      simpa only [Var.index_appendLeft] using sourceEqual
    exact False.elim (different externalEqual)
  let oldIndex : Fin state.locals.length := ⟨localIndex.val, old⟩
  have oldTarget :
      (state.materialMap
        (wire.appendLeft material.locals)).index.val =
          outer.length + oldIndex.val := by
    rw [← retainedIndex]
    simpa [oldIndex] using targetIndex
  exact State.advance_before_rooted state selected oldIndex
    (supported (Fin.succ position) oldIndex (by
      simpa [wire] using oldTarget))

theorem oneWire
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence state.region source)
    (targetCanonical : (state.advance selected).region.Canonical)
    (applicability :
      Identification.Local.Applicability (exposureData state selected)) :
    ∃ filledCanonical :
        (occurrence.context.fill (state.advance selected).region).Canonical,
      ∃ filledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill (state.advance selected).region),
        Relation.ReflTransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill (state.advance selected).region)
              filledCanonical filledExternalTwoEnded) ∧
          Relation.ReflTransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill (state.advance selected).region)
              filledCanonical filledExternalTwoEnded)
            source := by
  change Occurrence
    (Vacuity.Pin.plain state.locals state.items) source at occurrence
  let survivor :=
    state.materialMap (selected.appendLeft material.locals)
  let baseItems := state.items.append (sourceSupportSuffix state selected)
  have equality :
      ∃ equalityCanonical :
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)).Canonical,
        ∃ equalityExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Vacuity.Pin.present state.locals baseItems signature survivor)),
          Relation.ReflTransGen Step source
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Vacuity.Pin.present state.locals baseItems signature survivor))
                equalityCanonical equalityExternalTwoEnded) ∧
            Relation.ReflTransGen Step
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Vacuity.Pin.present state.locals baseItems signature survivor))
                equalityCanonical equalityExternalTwoEnded)
              source := by
    by_cases unused : material.incidencePaths selected.index.val = []
    · obtain ⟨supportCanonical, supportExternalTwoEnded, supportStep⟩ :=
        pinStep occurrence signature survivor
      let supportEndpoint := occurrence.interface.withBody
        (occurrence.context.fill
          (Vacuity.Pin.present state.locals state.items signature survivor))
        supportCanonical supportExternalTwoEnded
      let supportOccurrence : Occurrence
          (Vacuity.Pin.plain state.locals baseItems) supportEndpoint := {
        interface := occurrence.interface
        context := occurrence.context
        sourceCanonical := by
          simpa [baseItems, sourceSupportSuffix, unused, survivor,
            Vacuity.Pin.plain, Vacuity.Pin.present] using supportCanonical
        sourceExternalTwoEnded := by
          intro wireSignature wire
          simpa [baseItems, sourceSupportSuffix, unused, survivor,
            Vacuity.Pin.plain, Vacuity.Pin.present] using
              supportExternalTwoEnded wire
        host_iso := by
          simpa [supportEndpoint, baseItems, sourceSupportSuffix, unused,
            survivor, Vacuity.Pin.plain, Vacuity.Pin.present] using
              OpenDiagramIso.refl supportEndpoint
      }
      obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalityStep⟩ :=
        pinStep supportOccurrence signature survivor
      have equalityCanonical' :
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)).Canonical := by
        simpa [supportOccurrence] using equalityCanonical
      have equalityExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)) := by
        intro wireSignature wire
        simpa [supportOccurrence] using equalityExternalTwoEnded wire
      have equalityStepForward : Step supportEndpoint
          (occurrence.interface.withBody
            (occurrence.context.fill
              (Vacuity.Pin.present state.locals baseItems signature survivor))
            equalityCanonical' equalityExternalTwoEnded') := by
        simpa [supportOccurrence] using equalityStep.1
      have equalityStepReverse : Step
          (occurrence.interface.withBody
            (occurrence.context.fill
              (Vacuity.Pin.present state.locals baseItems signature survivor))
            equalityCanonical' equalityExternalTwoEnded') supportEndpoint := by
        simpa [supportOccurrence] using equalityStep.2
      have supportStepForward : Step source supportEndpoint := by
        simpa [supportEndpoint] using supportStep.1
      have supportStepReverse : Step supportEndpoint source := by
        simpa [supportEndpoint] using supportStep.2
      refine ⟨equalityCanonical', equalityExternalTwoEnded', ?_⟩
      exact ⟨.tail (.tail .refl supportStepForward) equalityStepForward,
        .tail (.tail .refl equalityStepReverse) supportStepReverse⟩
    · obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalityStep⟩ :=
        pinStep occurrence signature survivor
      have equalityExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)) := by
        intro wireSignature wire
        simpa [baseItems, sourceSupportSuffix, unused] using
          equalityExternalTwoEnded wire
      refine ⟨?_, ?_, ?_⟩
      · simpa [baseItems, sourceSupportSuffix, unused] using equalityCanonical
      · exact equalityExternalTwoEnded'
      · exact ⟨.tail .refl (by
          simpa [baseItems, sourceSupportSuffix, unused] using equalityStep.1),
          .tail .refl (by
            simpa [baseItems, sourceSupportSuffix, unused] using
              equalityStep.2)⟩
  obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalitySteps⟩ :=
    equality
  let equalityEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Vacuity.Pin.present state.locals baseItems signature survivor))
    equalityCanonical equalityExternalTwoEnded
  let appendOccurrence : Occurrence
      (Vacuity.Pin.present state.locals baseItems signature survivor)
      equalityEndpoint :=
    exactOccurrence occurrence.interface occurrence.context
      (Vacuity.Pin.present state.locals baseItems signature survivor)
      equalityCanonical equalityExternalTwoEnded
  have frontValidity := Vacuity.Pin.frontValidity appendOccurrence
  have frontCanonical :
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)).Canonical := by
    simpa [appendOccurrence] using frontValidity.1
  have frontExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)) := by
    intro wireSignature wire
    simpa [appendOccurrence] using frontValidity.2 wire
  have collapsedEq :
      Vacuity.Pin.front state.locals baseItems signature survivor =
        (exposureData state selected).collapsedRegion := by
    rw [exposureData_collapsedRegion]
    rfl
  have collapsedCanonical :
      (occurrence.context.fill
        (exposureData state selected).collapsedRegion).Canonical := by
    simpa only [← collapsedEq] using frontCanonical
  have collapsedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposureData state selected).collapsedRegion) := by
    intro wireSignature wire
    simpa only [← collapsedEq] using frontExternalTwoEnded wire
  have appendFrontIso : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.context.fill
        (Vacuity.Pin.present state.locals baseItems signature survivor))
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)) :=
    DiagramContext.fillIso occurrence.context
      (RegionIso.appendSingletonFront state.locals baseItems
        (.identity signature 1 (fun _ => survivor)))
  have equalityCollapsedIso : OpenDiagramIso equalityEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposureData state selected).collapsedRegion)
        collapsedCanonical collapsedExternalTwoEnded) := by
    simpa only [equalityEndpoint, ← collapsedEq] using
      OpenDiagram.withBody_iso equalityCanonical frontCanonical
        equalityExternalTwoEnded frontExternalTwoEnded appendFrontIso
  let collapsedOccurrence : Occurrence
      (exposureData state selected).collapsedRegion equalityEndpoint := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := collapsedCanonical
    sourceExternalTwoEnded := collapsedExternalTwoEnded
    host_iso := equalityCollapsedIso
  }
  have exposedValidity := Identification.Local.exposedValidity
    (exposureData state selected) applicability collapsedOccurrence
    (by simpa only [exposureData_exposedRegion] using targetCanonical)
  dsimp only [collapsedOccurrence] at exposedValidity
  let identificationTarget := occurrence.interface.withBody
    (occurrence.context.fill
      (exposureData state selected).exposedRegion)
    exposedValidity.1 exposedValidity.2
  have identificationRule : Identification equalityEndpoint
      identificationTarget := by
    exact Or.inl ⟨outer, (exposureData state selected).collapsedRegion,
      (exposureData state selected).exposedRegion, collapsedOccurrence,
      exposedValidity.1, exposedValidity.2, OpenDiagramIso.refl _,
      atPolarity_symmetric_of occurrence.context.polarity
        (.expose (exposureData state selected) applicability)⟩
  have identificationStep : Step equalityEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposureData state selected).exposedRegion)
        exposedValidity.1 exposedValidity.2) := by
    exact Step.identification identificationRule
  have identificationReverse : Step
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposureData state selected).exposedRegion)
        exposedValidity.1 exposedValidity.2) equalityEndpoint := by
    exact Step.identification identificationRule.symm
  have filledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (state.advance selected).region) := by
    intro wireSignature wire
    simpa only [exposureData_exposedRegion] using exposedValidity.2 wire
  refine ⟨?_, filledExternalTwoEnded, ?_⟩
  · simpa only [exposureData_exposedRegion] using exposedValidity.1
  · have equalityTail : Relation.ReflTransGen Step source equalityEndpoint :=
      by simpa [equalityEndpoint] using equalitySteps.1
    have exposedTail := Relation.ReflTransGen.tail equalityTail identificationStep
    have reverseTail : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (exposureData state selected).exposedRegion)
          exposedValidity.1 exposedValidity.2) source :=
      (Relation.ReflTransGen.tail .refl identificationReverse).trans (by
        simpa [equalityEndpoint] using equalitySteps.2)
    exact ⟨by simpa only [exposureData_exposedRegion] using exposedTail,
      by simpa only [exposureData_exposedRegion] using reverseTail⟩

theorem advanceAllDerives
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (injective : VariablesIndexInjective variables)
    (supported : state.Supports variables)
    (canonical : state.region.Canonical)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (sourceCanonical : (context.fill state.region).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill state.region)) :
    ∃ targetCanonical :
        (context.fill (state.advanceAll variables).region).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire
          (context.fill (state.advanceAll variables).region),
        Relation.ReflTransGen Step
            (interface.withBody (context.fill state.region)
              sourceCanonical sourceExternalTwoEnded)
            (interface.withBody
              (context.fill (state.advanceAll variables).region)
              targetCanonical targetExternalTwoEnded) ∧
          Relation.ReflTransGen Step
            (interface.withBody
              (context.fill (state.advanceAll variables).region)
              targetCanonical targetExternalTwoEnded)
            (interface.withBody (context.fill state.region)
              sourceCanonical sourceExternalTwoEnded) := by
  induction variables generalizing state with
  | nil =>
      exact ⟨sourceCanonical, sourceExternalTwoEnded, .refl, .refl⟩
  | @cons signature signatures selected tail induction =>
      let source := interface.withBody (context.fill state.region)
        sourceCanonical sourceExternalTwoEnded
      let occurrence : Occurrence state.region source :=
        exactOccurrence interface context state.region sourceCanonical
          sourceExternalTwoEnded
      have selectedSupported : ∀ localIndex : Fin state.locals.length,
          (state.materialMap
            (selected.appendLeft material.locals)).index.val =
              outer.length + localIndex.val →
          RegionPath.RootedTwo
            (state.before.incidencePaths
              (outer.length + localIndex.val) 0) := by
        intro localIndex equality
        exact supported 0 localIndex equality
      have nextCanonical := State.advance_canonical state selected canonical
        selectedSupported
      obtain ⟨filledCanonical, filledExternalTwoEnded, firstSteps⟩ :=
        oneWire state selected occurrence nextCanonical
          (exposureData_applicability state selected)
      let nextSource := occurrence.interface.withBody
        (occurrence.context.fill (state.advance selected).region)
        filledCanonical filledExternalTwoEnded
      have tailInjective : VariablesIndexInjective tail := by
        intro first second equality
        have positions := injective (Fin.succ first) (Fin.succ second) (by
          simpa using equality)
        apply Fin.ext
        have values := congrArg Fin.val positions
        simp only [Fin.val_succ] at values
        omega
      have tailSupported := State.supports_advance_tail state selected tail
        injective supported
      obtain ⟨targetCanonical, targetExternalTwoEnded, restSteps⟩ :=
        induction (state := state.advance selected) tailInjective tailSupported
          nextCanonical filledCanonical filledExternalTwoEnded
      refine ⟨?_, ?_, ?_⟩
      · simpa only [State.advanceAll] using targetCanonical
      · intro wireSignature wire
        simpa only [State.advanceAll] using targetExternalTwoEnded wire
      · have firstSteps' : Relation.ReflTransGen Step source nextSource := by
          simpa only [nextSource] using firstSteps.1
        have firstReverse : Relation.ReflTransGen Step nextSource source := by
          simpa only [nextSource] using firstSteps.2
        have combined := firstSteps'.trans restSteps.1
        have reverseCombined := restSteps.2.trans firstReverse
        exact ⟨by
            simpa only [source, occurrence, exactOccurrence, State.advanceAll]
              using combined,
          by
            simpa only [source, occurrence, exactOccurrence, State.advanceAll]
              using reverseCombined⟩

def applicationPorts (description : Rule.Erasure.Description outer) :
    Vars (outer ++ description.hostLocals) description.materialWires :=
  (identityBoundary description.materialWires).map
    (fun wire => description.wireMap wire)

def exposedRegion (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) : Region outer :=
  Region.adjoinAt description.hostLocals description.hostItems
    (Comprehension.Instantiation.instantiate
      (supportPattern description.material materialCanonical)
      (applicationPorts description))

def endpointHostWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming (outer ++ description.hostLocals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  Region.adjoinHostWire outer description.hostLocals
    (description.materialWires ++ description.material.locals)

def endpointMaterialWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      (description.materialWires ++ description.material.locals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  ⟨fun wire => Var.appendRight outer
    (Var.appendRight description.hostLocals wire)⟩

def endpointEqualityWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      ((outer ++ description.hostLocals) ++ description.materialWires)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  ⟨Var.appendMap
    (fun wire => endpointHostWire description wire)
    (fun wire => endpointMaterialWire description
      (wire.appendLeft description.material.locals))⟩

def endpointEqualityItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals))) :=
  (Comprehension.Instantiation.equalityItems
    ((applicationPorts description).map
      (fun wire => wire.appendLeft description.materialWires))
    ((identityBoundary description.materialWires).map
      (fun wire => Var.appendRight
        (outer ++ description.hostLocals) wire))).renameWires
    (endpointEqualityWire description)

def endpointLeft
    (description : Rule.Erasure.Description outer) :
    Vars (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals)))
      description.materialWires :=
  (applicationPorts description).map
    (fun wire => endpointHostWire description wire)

def endpointRight
    (description : Rule.Erasure.Description outer) :
    Vars (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals)))
      description.materialWires :=
  (identityBoundary description.materialWires).map
    (fun wire => endpointMaterialWire description
      (wire.appendLeft description.material.locals))

theorem endpointEqualityItems_eq
    (description : Rule.Erasure.Description outer) :
    endpointEqualityItems description =
      Comprehension.Instantiation.equalityItems
        (endpointLeft description) (endpointRight description) := by
  have leftEq :
      ((applicationPorts description).map
        (fun wire => wire.appendLeft description.materialWires)).map
          (fun wire => endpointEqualityWire description wire) =
        endpointLeft description := by
    calc
      _ = (applicationPorts description).map (fun wire =>
            endpointEqualityWire description
              (wire.appendLeft description.materialWires)) :=
        Vars.map_map _ _ _
      _ = (applicationPorts description).map (fun wire =>
            endpointHostWire description wire) := by
        apply Vars.map_congr
        intro signature wire
        simp [endpointEqualityWire]
      _ = _ := rfl
  have rightEq :
      ((identityBoundary description.materialWires).map
        (fun wire => Var.appendRight
          (outer ++ description.hostLocals) wire)).map
          (fun wire => endpointEqualityWire description wire) =
        endpointRight description := by
    calc
      _ = (identityBoundary description.materialWires).map (fun wire =>
            endpointEqualityWire description
              (Var.appendRight (outer ++ description.hostLocals) wire)) :=
        Vars.map_map _ _ _
      _ = (identityBoundary description.materialWires).map (fun wire =>
            endpointMaterialWire description
              (wire.appendLeft description.material.locals)) := by
        apply Vars.map_congr
        intro signature wire
        simp [endpointEqualityWire]
      _ = _ := rfl
  unfold endpointEqualityItems
  rw [Comprehension.Instantiation.equalityItems_renameWires]
  rw [leftEq, rightEq]

def endpointItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals))) :=
  (description.hostItems.renameWires
      (endpointHostWire description)).append
    ((description.material.items.renameWires
        (endpointMaterialWire description)).append
      (((supportPins description.material description.materialWires
          (identityBoundary description.materialWires)).renameWires
          (endpointMaterialWire description)).append
        (endpointEqualityItems description)))

def instantiatedBodyWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      (description.materialWires ++ description.material.locals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++
          (description.material.locals ++ [])))) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      (description.materialWires ++ (description.material.locals ++ [])))
    (WireRenaming.comp
      (Region.adjoinMaterialWire (outer ++ description.hostLocals)
        description.materialWires (description.material.locals ++ []))
      (WireRenaming.comp
        (Region.conjoinLeftWire
          (outer ++ description.hostLocals ++ description.materialWires)
          description.material.locals [])
        ((⟨fun wire => Var.appendRight
            (outer ++ description.hostLocals) wire⟩ :
          WireRenaming description.materialWires
            ((outer ++ description.hostLocals) ++
              description.materialWires)).appendRight
          description.material.locals)))

def instantiatedEqualityWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      ((outer ++ description.hostLocals) ++ description.materialWires)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++
          (description.material.locals ++ [])))) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      (description.materialWires ++ (description.material.locals ++ [])))
    (WireRenaming.comp
      (Region.adjoinMaterialWire (outer ++ description.hostLocals)
        description.materialWires (description.material.locals ++ []))
      (WireRenaming.comp
        (Region.conjoinRightWire
          (outer ++ description.hostLocals ++ description.materialWires)
          description.material.locals [])
        ⟨fun wire => wire.appendLeft []⟩))

noncomputable def exposedRegionEndpointIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (exposedRegion description materialCanonical)
      (.mk (description.hostLocals ++
        (description.materialWires ++ description.material.locals))
        (endpointItems description)) := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          unfold exposedRegion endpointItems endpointEqualityItems
            endpointHostWire endpointMaterialWire applicationPorts
            supportPattern supportBody
            Comprehension.Instantiation.instantiate
          rw [Comprehension.Instantiation.Equalities_eq_ofItems]
          unfold Region.adjoinAt Region.conjoin Region.renameWires
            Region.ofItems
          simp only [Region.locals, Region.items]
          simp only [ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp,
            ItemSeq.renameWires, ItemSeq.nil_append]
          let description : Rule.Erasure.Description outer := {
            materialWires := materialWires
            hostLocals := hostLocals
            hostItems := hostItems
            material := .mk materialLocals materialItems
            wireMap := wireMap
          }
          let actualLocals := hostLocals ++
            (materialWires ++ (materialLocals ++ []))
          let targetLocals := hostLocals ++
            (materialWires ++ materialLocals)
          have localsEq : actualLocals = targetLocals :=
            congrArg (fun tail => hostLocals ++ (materialWires ++ tail))
              (List.append_nil materialLocals)
          let localsIso : WireEquiv
              actualLocals targetLocals :=
            WireEquiv.ofEq localsEq
          let ambient := (WireEquiv.refl outer).append localsIso
          let actualHost := Region.adjoinHostWire outer hostLocals
            (materialWires ++ (materialLocals ++ []))
          let targetHost := endpointHostWire description
          let actualBody := instantiatedBodyWire description
          let targetBody := endpointMaterialWire description
          let actualEquality := instantiatedEqualityWire description
          let targetEquality := endpointEqualityWire description
          let baseEquality := Comprehension.Instantiation.equalityItems
            (((identityBoundary materialWires).map
              (fun wire => wireMap wire)).map
              (fun wire => wire.appendLeft materialWires))
            ((identityBoundary materialWires).map
              (fun wire => Var.appendRight (outer ++ hostLocals) wire))
          have ambientIndex : ∀ {signature}
              (wire : Var (outer ++ actualLocals) signature),
              (ambient wire).index.val = wire.index.val := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := actualLocals)
              (motive := fun wire =>
                (ambient wire).index.val = wire.index.val)
            · intro inheritedSignature inherited
              simp [ambient]
            · intro localSignature localWire
              simp [ambient, localsIso]
          have hostCommutes : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              ambient (actualHost wire) = targetHost wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            simp [actualHost, targetHost, endpointHostWire, description,
              Region.locals]
          have bodyCommutes : ∀ {signature}
              (wire : Var (materialWires ++ materialLocals) signature),
              ambient (actualBody wire) = targetBody wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            apply Var.appendCases (left := materialWires)
              (right := materialLocals)
              (motive := fun wire =>
                (actualBody wire).index.val = (targetBody wire).index.val)
            · intro inheritedSignature inherited
              simp [actualBody, targetBody, instantiatedBodyWire,
                endpointMaterialWire, WireRenaming.comp,
                WireRenaming.appendRight, description, Region.locals]
              omega
            · intro localSignature localWire
              simp [actualBody, targetBody, instantiatedBodyWire,
                endpointMaterialWire, WireRenaming.comp,
                WireRenaming.appendRight, description, Region.locals]
              omega
          have equalityCommutes : ∀ {signature}
              (wire : Var ((outer ++ hostLocals) ++ materialWires) signature),
              ambient (actualEquality wire) = targetEquality wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            apply Var.appendCases (left := outer ++ hostLocals)
              (right := materialWires)
              (motive := fun wire =>
                (actualEquality wire).index.val =
                  (targetEquality wire).index.val)
            · intro inheritedSignature inherited
              simp [actualEquality, targetEquality,
                instantiatedEqualityWire, endpointEqualityWire,
                endpointHostWire, endpointMaterialWire,
                WireRenaming.comp, Region.conjoinRightWire,
                Region.locals, description]
            · intro localSignature localWire
              simp [actualEquality, targetEquality,
                instantiatedEqualityWire, endpointEqualityWire,
                endpointHostWire, endpointMaterialWire,
                WireRenaming.comp, Region.conjoinRightWire,
                Region.locals, description]
              omega
          refine .mk localsIso ?_
          let hostIso := ItemSeqIso.renameWires hostItems
            actualHost targetHost ambient hostCommutes
          let materialIso := ItemSeqIso.renameWires materialItems
            actualBody targetBody ambient bodyCommutes
          let supportIso := ItemSeqIso.renameWires
            (supportPins (Region.mk materialLocals materialItems)
              materialWires (identityBoundary materialWires))
            actualBody targetBody ambient bodyCommutes
          let equalityIso := ItemSeqIso.renameWires baseEquality
            actualEquality targetEquality ambient equalityCommutes
          let combined := ItemSeqIso.append hostIso
            (ItemSeqIso.append materialIso
              (ItemSeqIso.append supportIso equalityIso))
          simpa [description, actualLocals, targetLocals, actualHost,
            targetHost, actualBody, targetBody, actualEquality,
            targetEquality, baseEquality, endpointHostWire,
            endpointMaterialWire, instantiatedBodyWire,
            endpointEqualityWire, instantiatedEqualityWire,
            ItemSeq.append_assoc] using combined

def initialState
    (description : Rule.Erasure.Description outer) :
    State outer description.materialWires description.material where
  locals := description.hostLocals ++ description.material.locals
  before := description.hostItems.renameWires
    (Region.adjoinHostWire outer description.hostLocals
      description.material.locals)
  after := .nil
  materialMap := WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      description.material.locals)
    (description.wireMap.appendRight description.material.locals)

theorem initialState_region
    (description : Rule.Erasure.Description outer) :
    (initialState description).region = description.source := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          simp [initialState, State.region, State.items,
            Rule.Erasure.Description.source, Region.spliceAt, Region.adjoinAt,
            Region.renameWires, Region.locals, Region.items,
            ItemSeq.renameWires_comp]

theorem initialState_materialMap_external_index
    (description : Rule.Erasure.Description outer)
    (external : Var description.materialWires signature) :
    ((initialState description).materialMap
      (external.appendLeft description.material.locals)).index.val =
        (description.wireMap external).index.val := by
  let mapped := description.wireMap external
  change
    (Region.adjoinMaterialWire outer description.hostLocals
      description.material.locals
      ((description.wireMap.appendRight description.material.locals)
        (external.appendLeft description.material.locals))).index.val =
      mapped.index.val
  have inherited :
      (description.wireMap.appendRight description.material.locals)
          (external.appendLeft description.material.locals) =
        mapped.appendLeft description.material.locals := by
    simp [mapped, WireRenaming.appendRight]
  rw [inherited]
  apply Var.appendCases (left := outer) (right := description.hostLocals)
    (motive := fun mapped =>
      (Region.adjoinMaterialWire outer description.hostLocals
        description.material.locals
        (mapped.appendLeft description.material.locals)).index.val =
          mapped.index.val)
  · intro mappedSignature inheritedWire
    simp [Region.adjoinMaterialWire]
  · intro mappedSignature localWire
    simp [Region.adjoinMaterialWire]

theorem initialState_supports
    (description : Rule.Erasure.Description outer)
    (targetCanonical : description.target.Canonical) :
    (initialState description).Supports
      (identityBoundary description.materialWires) := by
  intro position localIndex targetIndex
  let external := (identityBoundary description.materialWires).get position
  let mapped := description.wireMap external
  have materialMapIndex :=
    initialState_materialMap_external_index description external
  have mappedTarget : mapped.index.val = outer.length + localIndex.val :=
    materialMapIndex.symm.trans targetIndex
  have hostBound : localIndex.val < description.hostLocals.length := by
    have mappedBound := mapped.index.isLt
    simp only [List.length_append] at mappedBound
    omega
  let hostIndex : Fin description.hostLocals.length :=
    ⟨localIndex.val, hostBound⟩
  have hostRoot : RegionPath.RootedTwo
      (description.hostItems.incidencePaths
        (outer.length + hostIndex.val) 0) := by
    simpa only [Rule.Erasure.Description.target, Region.Canonical] using
      targetCanonical.1 hostIndex
  have renamedPaths :=
    ItemSeq.incidencePaths_renameWires_adjoinHost
      (addedLocals := description.material.locals)
      description.hostItems mapped 0
  rw [mappedTarget] at renamedPaths
  change RegionPath.RootedTwo
    ((description.hostItems.renameWires
      (Region.adjoinHostWire outer description.hostLocals
        description.material.locals)).incidencePaths
      (outer.length + localIndex.val) 0)
  rw [renamedPaths]
  simpa [hostIndex] using hostRoot

theorem materialCanonical_of_source
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source) :
    description.material.Canonical := by
  have sourceCanonical := occurrence.context.holeCanonical
    description.source occurrence.sourceCanonical
  have renamedCanonical :
      (description.material.renameWires description.wireMap).Canonical := by
    apply Region.Canonical.material_of_adjoinAt
      description.hostLocals description.hostItems
    simpa only [Rule.Erasure.Description.source, Region.spliceAt] using
      sourceCanonical
  exact (Region.Canonical.renameWires_iff
    description.material description.wireMap).mp renamedCanonical

noncomputable def endpointRegionIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      ((initialState description).advanceAll
        (identityBoundary description.materialWires)).region
      (exposedRegion description materialCanonical) := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          let description : Rule.Erasure.Description outer := {
            materialWires := materialWires
            hostLocals := hostLocals
            hostItems := hostItems
            material := .mk materialLocals materialItems
            wireMap := wireMap
          }
          let state := initialState description
          let variables := identityBoundary materialWires
          let finalState := state.advanceAll variables
          have localsEq : finalState.locals =
              (hostLocals ++ materialLocals) ++ materialWires := by
            simpa [finalState, state, description, initialState] using
              State.advanceAll_locals state variables
          let normalizeLocals := WireEquiv.ofEq localsEq
          let rotation := WireEquiv.rotate
            hostLocals materialLocals materialWires
          let localsIso := normalizeLocals.trans rotation
          let ambient := (WireEquiv.refl outer).append localsIso
          let normalizeAmbient :=
            (WireEquiv.refl outer).append normalizeLocals
          let rotateAmbient := (WireEquiv.refl outer).append rotation
          have ambientFactor : ambient =
              normalizeAmbient.trans rotateAmbient := by
            have factor := WireEquiv.append_trans
              (WireEquiv.refl outer) (WireEquiv.refl outer)
              normalizeLocals rotation
            simpa [ambient, normalizeAmbient, rotateAmbient, localsIso] using
              factor.symm
          let initialHost := Region.adjoinHostWire outer hostLocals
            materialLocals
          let rawHost := WireRenaming.comp (state.retainAll variables)
            initialHost
          let rawMaterial := finalState.materialMap
          let targetHost := endpointHostWire description
          let targetMaterial := endpointMaterialWire description
          let canonicalHost := WireRenaming.comp
            (Region.adjoinHostWire outer
              (hostLocals ++ materialLocals) materialWires)
            initialHost
          have normalizeIndex : ∀ {signature}
              (wire : Var (outer ++ finalState.locals) signature),
              (normalizeAmbient wire).index.val = wire.index.val := by
            intro signature wire
            apply Var.appendCases (left := outer)
              (right := finalState.locals)
              (motive := fun wire =>
                (normalizeAmbient wire).index.val = wire.index.val)
            · intro inheritedSignature inherited
              simp [normalizeAmbient]
            · intro localSignature localWire
              simp [normalizeAmbient, normalizeLocals]
          have initialMaterialExternal : ∀ {signature}
              (wire : Var materialWires signature),
              state.materialMap (wire.appendLeft materialLocals) =
                initialHost (wireMap wire) := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (state.materialMap
                    (wire.appendLeft materialLocals)).index.val =
                  (wireMap wire).index.val := by
                simp [state, description, initialState,
                  WireRenaming.comp, WireRenaming.appendRight,
                  Region.locals]
              _ = (initialHost (wireMap wire)).index.val :=
                (Region.adjoinHostWire_index_val (wireMap wire)).symm
          have normalizedHost : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              normalizeAmbient (rawHost wire) = canonicalHost wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient (rawHost wire)).index.val =
                  (rawHost wire).index.val := normalizeIndex _
              _ = (initialHost wire).index.val :=
                State.retainAll_index state variables _
              _ = wire.index.val :=
                Region.adjoinHostWire_index_val wire
              _ = (canonicalHost wire).index.val := by
                simp [canonicalHost, initialHost, WireRenaming.comp]
          have hostRotates : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              rotateAmbient (canonicalHost wire) = targetHost wire := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := hostLocals)
              (motive := fun wire =>
                rotateAmbient (canonicalHost wire) = targetHost wire)
            · intro inheritedSignature inherited
              simp [rotateAmbient, rotation, canonicalHost, initialHost,
                targetHost, endpointHostWire, WireRenaming.comp,
                Region.adjoinHostWire, Region.conjoinLeftWire,
                description, Region.locals]
            · intro localSignature localWire
              simp [rotateAmbient, rotation, canonicalHost, initialHost,
                targetHost, endpointHostWire, WireRenaming.comp,
                Region.adjoinHostWire, Region.conjoinLeftWire,
                description, Region.locals]
          have hostCommutes : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              ambient (rawHost wire) = targetHost wire := by
            intro signature wire
            rw [ambientFactor]
            change rotateAmbient (normalizeAmbient (rawHost wire)) = _
            rw [normalizedHost wire]
            exact hostRotates wire
          have normalizedExternal : ∀ {signature}
              (wire : Var materialWires signature),
              normalizeAmbient
                  (rawMaterial (wire.appendLeft materialLocals)) =
                Var.appendRight outer
                  (Var.appendRight (hostLocals ++ materialLocals) wire) := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient
                  (rawMaterial (wire.appendLeft materialLocals))).index.val =
                  (rawMaterial
                    (wire.appendLeft materialLocals)).index.val :=
                normalizeIndex _
              _ = (outer ++ state.locals).length + wire.index.val :=
                State.advanceAll_materialMap_get_index state variables
                  identityBoundary_indexInjective wire wire.index (by
                    have indexEq := identityBoundary_get_index
                      (wires := materialWires) wire.index
                    exact congrArg Fin.val indexEq.symm)
              _ = (Var.appendRight outer
                    (Var.appendRight (hostLocals ++ materialLocals)
                      wire)).index.val := by
                simp [state, description, initialState, Region.locals]
                omega
          have normalizedLocal : ∀ {signature}
              (wire : Var materialLocals signature),
              normalizeAmbient
                  (rawMaterial (Var.appendRight materialWires wire)) =
                Var.appendRight outer
                  ((Var.appendRight hostLocals wire).appendLeft
                    materialWires) := by
            intro signature wire
            have different : ∀ position : Fin materialWires.length,
                (Var.appendRight materialWires wire).index.val ≠
                  ((variables.get position).appendLeft
                    materialLocals).index.val := by
              intro position equality
              have bound := (variables.get position).index.isLt
              simp only [Var.index_appendRight, Var.index_appendLeft] at equality
              omega
            have retained := State.advanceAll_materialMap_other state
              variables (Var.appendRight materialWires wire) different
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient
                  (rawMaterial
                    (Var.appendRight materialWires wire))).index.val =
                  (rawMaterial
                    (Var.appendRight materialWires wire)).index.val :=
                normalizeIndex _
              _ = (state.retainAll variables
                    (state.materialMap
                      (Var.appendRight materialWires wire))).index.val :=
                congrArg (fun mapped => mapped.index.val) retained
              _ = (state.materialMap
                    (Var.appendRight materialWires wire)).index.val :=
                State.retainAll_index state variables _
              _ = (Var.appendRight outer
                    ((Var.appendRight hostLocals wire).appendLeft
                      materialWires)).index.val := by
                simp [state, description, initialState,
                  WireRenaming.comp, WireRenaming.appendRight,
                  Region.locals]
                omega
          have materialCommutes : ∀ {signature}
              (wire : Var (materialWires ++ materialLocals) signature),
              ambient (rawMaterial wire) = targetMaterial wire := by
            intro signature wire
            apply Var.appendCases (left := materialWires)
              (right := materialLocals)
              (motive := fun wire =>
                ambient (rawMaterial wire) = targetMaterial wire)
            · intro inheritedSignature inherited
              rw [ambientFactor]
              change rotateAmbient
                (normalizeAmbient
                  (rawMaterial (inherited.appendLeft materialLocals))) = _
              rw [normalizedExternal inherited]
              simp [rotateAmbient, rotation, targetMaterial,
                endpointMaterialWire, description, Region.locals]
            · intro localSignature localWire
              rw [ambientFactor]
              change rotateAmbient
                (normalizeAmbient
                  (rawMaterial
                    (Var.appendRight materialWires localWire))) = _
              rw [normalizedLocal localWire]
              simp [rotateAmbient, rotation, targetMaterial,
                endpointMaterialWire, description, Region.locals]
          have leftCommutes :
              (state.batchLeft variables).map
                  (fun wire => ambient wire) =
                endpointLeft description := by
            unfold State.batchLeft endpointLeft applicationPorts
            rw [Vars.map_map, Vars.map_map]
            apply Vars.map_congr
            intro signature wire
            change ambient
                (state.retainAll variables
                  (state.materialMap
                    (wire.appendLeft materialLocals))) =
              targetHost (wireMap wire)
            rw [initialMaterialExternal wire]
            exact hostCommutes (wireMap wire)
          have rightCommutes :
              (state.batchRight variables).map
                  (fun wire => ambient wire) =
                endpointRight description := by
            unfold State.batchRight endpointRight
            rw [Vars.map_map]
            apply Vars.map_congr
            intro signature wire
            exact materialCommutes (wire.appendLeft materialLocals)
          have supportEq := State.batchSupports_eq state variables
            identityBoundary_indexInjective
          have equalitiesEq := State.batchEqualities_eq state variables
            identityBoundary_indexInjective
          have rawPresentation : ItemSeqIso
              (WireEquiv.refl (outer ++ finalState.locals))
              finalState.items
              ((hostItems.renameWires rawHost).append
                ((materialItems.renameWires rawMaterial).append
                  (((supportPins (Region.mk materialLocals materialItems)
                      materialWires variables).renameWires rawMaterial).append
                    (Comprehension.Instantiation.equalityItems
                      (state.batchLeft variables)
                      (state.batchRight variables))))) := by
            have presentation := State.advanceAll_itemsIso state variables rfl
            rw [supportEq, equalitiesEq] at presentation
            simpa [finalState, rawMaterial, state, description, initialState,
              rawHost, initialHost, ItemSeq.renameWires_comp,
              ItemSeq.append_assoc] using presentation
          let hostIso := ItemSeqIso.renameWires hostItems
            rawHost targetHost ambient hostCommutes
          let materialIso := ItemSeqIso.renameWires materialItems
            rawMaterial targetMaterial ambient materialCommutes
          let supportIso := ItemSeqIso.renameWires
            (supportPins (Region.mk materialLocals materialItems)
              materialWires variables)
            rawMaterial targetMaterial ambient materialCommutes
          let equalityIso :=
            Comprehension.Instantiation.equalityItemsIso ambient
            (state.batchLeft variables) (state.batchRight variables)
            (endpointLeft description) (endpointRight description)
            leftCommutes rightCommutes
          have blocks : ItemSeqIso ambient
              ((hostItems.renameWires rawHost).append
                ((materialItems.renameWires rawMaterial).append
                  (((supportPins (Region.mk materialLocals materialItems)
                      materialWires variables).renameWires rawMaterial).append
                    (Comprehension.Instantiation.equalityItems
                      (state.batchLeft variables)
                      (state.batchRight variables)))))
              (endpointItems description) := by
            let combined := ItemSeqIso.append hostIso
              (ItemSeqIso.append materialIso
                (ItemSeqIso.append supportIso equalityIso))
            simpa [endpointItems, endpointEqualityItems_eq,
              ItemSeq.append_assoc] using combined
          have itemIso := rawPresentation.trans blocks
          have itemIso' := itemIso.castAmbient
            (WireEquiv.refl_trans ambient)
          let directIso : RegionIso (WireEquiv.refl outer)
              finalState.region
              (.mk (hostLocals ++ (materialWires ++ materialLocals))
                (endpointItems description)) :=
            .mk localsIso itemIso'
          let exposedIso := exposedRegionEndpointIso description
            materialCanonical
          have composed := directIso.trans exposedIso.symm
          have composed' : RegionIso (WireEquiv.refl outer)
              finalState.region
              (exposedRegion description materialCanonical) :=
            RegionIso.castAmbient (by rfl) composed
          simpa [description, state, variables, finalState] using composed'

theorem equatesCore
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (materialCanonical : description.material.Canonical)
    (supported : (initialState description).Supports
      (identityBoundary description.materialWires))
    (exposedCanonical :
      (occurrence.context.fill
        (exposedRegion description materialCanonical)).Canonical)
    (exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposedRegion description materialCanonical))) :
    Equates occurrence (exposedRegion description materialCanonical)
      exposedCanonical exposedExternalTwoEnded := by
  let state := initialState description
  let variables := identityBoundary description.materialWires
  have stateRegionEq : state.region = description.source := by
    simpa only [state] using initialState_region description
  have initialFilledCanonical :
      (occurrence.context.fill state.region).Canonical := by
    rw [stateRegionEq]
    exact occurrence.sourceCanonical
  have initialFilledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill state.region) := by
    rw [stateRegionEq]
    exact occurrence.sourceExternalTwoEnded
  have initialHostIso : OpenDiagramIso source
      (occurrence.interface.withBody
        (occurrence.context.fill state.region)
        initialFilledCanonical initialFilledExternalTwoEnded) := by
    simpa only [stateRegionEq] using occurrence.host_iso
  let initialOccurrence : Occurrence state.region source := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := initialFilledCanonical
    sourceExternalTwoEnded := initialFilledExternalTwoEnded
    host_iso := initialHostIso
  }
  have stateCanonical : state.region.Canonical :=
    initialOccurrence.context.holeCanonical state.region
      initialOccurrence.sourceCanonical
  have supported' : state.Supports variables := by
    simpa only [state, variables] using supported
  have regionEta :
      Vacuity.Point.plain state.region.locals state.region.items =
        state.region := by
    cases state.region
    rfl
  let pointOccurrence : Occurrence
      (Vacuity.Point.plain state.region.locals state.region.items) source := by
    rw [regionEta]
    exact initialOccurrence
  have pointValidity :=
    Vacuity.Point.introduceValidity pointOccurrence Sig.iota
  let pointEndpoint := pointOccurrence.interface.withBody
    (pointOccurrence.context.fill
      (Vacuity.Point.present state.region.locals state.region.items Sig.iota))
    pointValidity.1 pointValidity.2
  have pointIntroduction : Vacuity source pointEndpoint := by
    exact ⟨outer, Vacuity.Point.plain state.region.locals state.region.items,
      Vacuity.Point.present state.region.locals state.region.items Sig.iota,
      pointOccurrence, pointValidity.1, pointValidity.2,
      OpenDiagramIso.refl _,
      atPolarity_symmetric_of pointOccurrence.context.polarity
        (.mk (.point state.region.locals state.region.items Sig.iota))⟩
  let initialExact := initialOccurrence.interface.withBody
    (initialOccurrence.context.fill state.region)
    initialOccurrence.sourceCanonical initialOccurrence.sourceExternalTwoEnded
  have exactIntroduction : Vacuity initialExact pointEndpoint := by
    exact Vacuity.iso initialOccurrence.host_iso pointIntroduction
      (OpenDiagramIso.refl pointEndpoint)
  have bridge : Relation.TransGen Step source initialExact := by
    exact (Relation.TransGen.single
      (Step.vacuity pointIntroduction)).tail
      (Step.vacuity exactIntroduction.symm)
  have bridgeReverse : Relation.TransGen Step initialExact source := by
    exact (Relation.TransGen.single
      (Step.vacuity exactIntroduction)).tail
      (Step.vacuity pointIntroduction.symm)
  obtain ⟨foldCanonical, foldExternalTwoEnded, rawFoldSteps⟩ :=
    advanceAllDerives state variables identityBoundary_indexInjective
      supported' stateCanonical initialOccurrence.interface
      initialOccurrence.context initialOccurrence.sourceCanonical
      initialOccurrence.sourceExternalTwoEnded
  have foldSteps : Relation.ReflTransGen Step initialExact
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded) := by
    simpa only [initialExact] using rawFoldSteps.1
  have foldReverse : Relation.ReflTransGen Step
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded) initialExact := by
    simpa only [initialExact] using rawFoldSteps.2
  have exactExposedCanonical :
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)).Canonical := by
    simpa only [initialOccurrence] using exposedCanonical
  have exactExposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      initialOccurrence.interface.boundaryWire
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    intro signature wire
    simpa only [initialOccurrence] using exposedExternalTwoEnded wire
  let endpointBodyIso : RegionIso
      (WireEquiv.refl initialOccurrence.interface.external)
      (initialOccurrence.context.fill
        (state.advanceAll variables).region)
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    simpa only [state, variables] using
      DiagramContext.fillIso initialOccurrence.context
        (endpointRegionIso description materialCanonical)
  let endpointIso : OpenDiagramIso
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded)
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill
          (exposedRegion description materialCanonical))
        exactExposedCanonical exactExposedExternalTwoEnded) :=
    OpenDiagram.withBody_iso foldCanonical exactExposedCanonical
      foldExternalTwoEnded exactExposedExternalTwoEnded endpointBodyIso
  have foldCore : Relation.TransGen Step source
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded) :=
    bridge.reflTransGen foldSteps
  have exposedCore : Relation.TransGen Step source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposedRegion description materialCanonical))
        exposedCanonical exposedExternalTwoEnded) := by
    have transported := transGen_iso (OpenDiagramIso.refl source)
      foldCore endpointIso
    simpa only [initialOccurrence] using transported
  have reverseCore : Relation.TransGen Step
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill
          (exposedRegion description materialCanonical))
        exactExposedCanonical exactExposedExternalTwoEnded)
      source := by
    have fromFold : Relation.TransGen Step
        (initialOccurrence.interface.withBody
          (initialOccurrence.context.fill (state.advanceAll variables).region)
          foldCanonical foldExternalTwoEnded) source :=
      foldReverse.transGen bridgeReverse
    exact transGen_iso endpointIso fromFold (OpenDiagramIso.refl source)
  have reverseExposedCore : Relation.TransGen Step
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposedRegion description materialCanonical))
        exposedCanonical exposedExternalTwoEnded) source := by
    simpa only [initialOccurrence] using reverseCore
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail steps step induction => exact .tail induction step
  exact ⟨optional exposedCore, optional reverseExposedCore⟩

/-- Erasure material is bidirectionally equivalent to one exact
comprehension-instantiation block. Every generated step is Vacuity or
Identification, so the exposure remains symmetric beneath arbitrary cuts.
The original erased-target validity premises also determine the material and
the exact exposed-endpoint validity returned to the caller. -/
theorem equates
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    ∃ materialCanonical : description.material.Canonical,
      ∃ exposedCanonical :
          (occurrence.context.fill
            (exposedRegion description materialCanonical)).Canonical,
        ∃ exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (exposedRegion description materialCanonical)),
          Equates occurrence (exposedRegion description materialCanonical)
            exposedCanonical exposedExternalTwoEnded := by
  let materialCanonical := materialCanonical_of_source description occurrence
  refine ⟨materialCanonical, ?_⟩
  have targetCanonical : description.target.Canonical := by
    exact occurrence.context.holeCanonical description.target erasedCanonical
  have instantiatedCanonical :
      (Comprehension.Instantiation.instantiate
        (supportPattern description.material materialCanonical)
        (applicationPorts description)).Canonical :=
    Comprehension.Instantiation.instantiate_canonical
      (supportPattern description.material materialCanonical)
      (applicationPorts description)
  have exposedLocalCanonical :
      (exposedRegion description materialCanonical).Canonical := by
    simpa only [exposedRegion] using
      Region.Canonical.adjoinAt description.hostLocals description.hostItems
        (Comprehension.Instantiation.instantiate
          (supportPattern description.material materialCanonical)
          (applicationPorts description))
        targetCanonical instantiatedCanonical
  have extension := occurrence.context.extendCanonical description.target
    (exposedRegion description materialCanonical) erasedCanonical
    exposedLocalCanonical (by
      intro signature wire
      simpa only [Rule.Erasure.Description.target, exposedRegion] using
        Region.incidencePaths_adjoinAt_host_sublist
          description.hostLocals description.hostItems
          (Comprehension.Instantiation.instantiate
            (supportPattern description.material materialCanonical)
            (applicationPorts description)) wire)
  let exposedCanonical := extension.1
  have exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    intro signature wire
    have sourceFloor := erasedExternalTwoEnded wire
    have pathSublist := extension.2 wire
    exact Nat.le_trans sourceFloor
      (Nat.add_le_add_left pathSublist.length_le _)
  have supported := initialState_supports description targetCanonical
  exact ⟨exposedCanonical, exposedExternalTwoEnded,
    equatesCore description occurrence materialCanonical supported
      exposedCanonical exposedExternalTwoEnded⟩


end VisualProof.Rule.Completeness.Erasure.Exposure
