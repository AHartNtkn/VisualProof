import VisualProof.Diagram.Concrete.Subgraph.FactorizationStructure
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction

namespace VisualProof

namespace RemovalFactorization

private def appendRenaming
    (prefixSigs : List Sig) (rho : WireRenaming source target) :
    WireRenaming (prefixSigs ++ source) (prefixSigs ++ target) :=
  match prefixSigs with
  | [] => rho
  | sig :: rest => WireRenaming.lift (appendRenaming rest rho) sig

theorem fragmentWire_signature
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (wire : fragment.val.diagram.WireId) :
    (attachment.diagram.wires (attachment.fragmentWire wire)).sig =
      (fragment.val.diagram.wires wire).sig := by
  unfold ConcreteSpliceAttachment.fragmentWire
  split
  · rename_i boundary
    rw [ConcreteSpliceAttachment.diagram_wire_hostWire]
    let position := attachment.representativePosition wire boundary
    have retrieved :
        fragment.val.boundary.get position = wire := by
      exact DenseList.get_index _ _ _
    change
      (removed.complement.val.wires
          (attachment.target position)).sig =
        (fragment.val.diagram.wires wire).sig
    exact (attachment.signature position).trans
      (congrArg (fun source =>
        (fragment.val.diagram.wires source).sig) retrieved)
  · rename_i internal
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
    rw [DenseList.get_index]

private theorem openRootContext_sigs_eq
    (fragment : CheckedOpenDiagram definitions) :
    (⟨ConcreteElaboration.openRootLocalWires fragment.val ++
        ConcreteElaboration.openBoundaryWires fragment.val⟩ :
      ConcreteElaboration.WireContext fragment.val.diagram).sigs =
      (ConcreteElaboration.openRootLocalWires fragment.val).map
          (fun wire => (fragment.val.diagram.wires wire).sig) ++
        ConcreteElaboration.openBoundaryClassSigs fragment.val := by
  simp [ConcreteElaboration.WireContext.sigs,
    ConcreteElaboration.openBoundaryClassSigs]

private theorem candidateSiteContext_sigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site)).sigs =
      (ConcreteElaboration.openRootLocalWires fragment.val).map
          (fun wire => (fragment.val.diagram.wires wire).sig) ++
        compiled.factor.frame.visible.sigs := by
  rw [ConcreteElaboration.WireContext.sigs_extend,
    candidate_wiresAt_site_eq]
  apply congrArg (fun values =>
    values ++ compiled.factor.frame.visible.sigs)
  generalize
    ConcreteElaboration.openRootLocalWires fragment.val = localWires
  induction localWires with
  | nil => rfl
  | cons wire tail induction =>
      simp only [List.map_cons]
      change
        (attachment.diagram.wires
            (attachment.fragmentWire wire)).sig ::
              List.map (fun candidate =>
                (attachment.diagram.wires candidate).sig)
                (List.map attachment.fragmentWire tail) =
          (fragment.val.diagram.wires wire).sig ::
            List.map (fun source =>
              (fragment.val.diagram.wires source).sig) tail
      rw [fragmentWire_signature attachment wire]
      exact congrArg
        (List.cons (fragment.val.diagram.wires wire).sig) induction

private theorem candidateSiteContext_ids_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site)).ids =
      List.append
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          attachment.fragmentWire)
        compiled.factor.frame.visible.ids := by
  change
    attachment.diagram.wiresAt
          (attachment.hostRegion removed.site) ++
        compiled.factor.frame.visible.ids =
      List.append
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          attachment.fragmentWire)
        compiled.factor.frame.visible.ids
  have allocation := candidate_wiresAt_site_eq attachment
  exact congrArg
    (fun wires =>
      List.append wires compiled.factor.frame.visible.ids)
    allocation

private theorem mappedRootLocalSigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    ((ConcreteElaboration.openRootLocalWires fragment.val).map
        attachment.fragmentWire).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (ConcreteElaboration.openRootLocalWires fragment.val).map
          (fun wire => (fragment.val.diagram.wires wire).sig) := by
  generalize
    ConcreteElaboration.openRootLocalWires fragment.val = localWires
  induction localWires with
  | nil => rfl
  | cons wire tail induction =>
      simp only [List.map_cons]
      change
        (attachment.diagram.wires
            (attachment.fragmentWire wire)).sig ::
              List.map (fun candidate =>
                (attachment.diagram.wires candidate).sig)
                (List.map attachment.fragmentWire tail) =
          (fragment.val.diagram.wires wire).sig ::
            List.map (fun source =>
              (fragment.val.diagram.wires source).sig) tail
      rw [fragmentWire_signature attachment wire]
      exact congrArg
        (List.cons (fragment.val.diagram.wires wire).sig) induction

def renamePacked
    (rho : WireRenaming source target) :
    PackedVar source → PackedVar target
  | ⟨sig, value⟩ => ⟨sig, rho value⟩

def castPacked
    (equality : source = target) :
    PackedVar source → PackedVar target
  | ⟨sig, value⟩ => ⟨sig, equality ▸ value⟩

private def packedOrigin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) :
    PackedVar
        (ids.map (fun wire => (diagram.wires wire).sig)) →
      diagram.WireId
  | ⟨_, value⟩ =>
      ConcreteElaboration.WireContext.origin diagram ids value

private theorem renamePacked_transport
    {source source' target target' : List Sig}
    (sourceEquality : source = source')
    (targetEquality : target = target')
    (rho : WireRenaming source' target')
    (value : PackedVar source') :
    renamePacked
        (fun sourceVar =>
          targetEquality.symm ▸
            rho (sourceEquality ▸ sourceVar))
        (castPacked sourceEquality.symm value) =
      castPacked targetEquality.symm
        (renamePacked rho value) := by
  cases sourceEquality
  cases targetEquality
  rfl

theorem cast_var_there_context
    (equality : source = target)
    (value : Var target sig) :
    (congrArg (List.cons head) equality).symm ▸
        (Var.there value : Var (head :: target) sig) =
      (Var.there (equality.symm ▸ value) :
        Var (head :: source) sig) := by
  cases equality
  rfl

theorem cast_var_here_context
    (equality : source = target) :
    (congrArg (List.cons head) equality).symm ▸
        (Var.here : Var (head :: target) head) =
      (Var.here : Var (head :: source) head) := by
  cases equality
  rfl

private def fragmentMappedSigsEq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    (ids : List fragment.val.diagram.WireId) →
      (ids.map attachment.fragmentWire).map
          (fun wire => (attachment.diagram.wires wire).sig) =
        ids.map
          (fun wire => (fragment.val.diagram.wires wire).sig)
  | [] => rfl
  | wire :: tail =>
      let mappedTail :=
        (tail.map attachment.fragmentWire).map
          (fun target => (attachment.diagram.wires target).sig)
      let sourceHead :=
        (fragment.val.diagram.wires wire).sig
      Eq.trans
        (congrArg (fun headSig => headSig :: mappedTail)
          (fragmentWire_signature attachment wire))
        (congrArg (List.cons sourceHead)
          (fragmentMappedSigsEq attachment tail))

private def varOffset : Var context sig → Nat
  | .here => 0
  | .there value => varOffset value + 1

private def packedOffset : PackedVar context → Nat
  | ⟨_, value⟩ => varOffset value

private theorem packedOffset_castPacked
    (equality : source = target)
    (value : PackedVar source) :
    packedOffset (castPacked equality value) =
      packedOffset value := by
  cases equality
  rfl

private theorem packedOrigin_get?
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (value :
      PackedVar
        (ids.map (fun wire => (diagram.wires wire).sig))) :
    ids[packedOffset value]? =
      some (packedOrigin diagram ids value) := by
  rcases value with ⟨sig, value⟩
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there tailValue =>
          simpa [packedOffset, varOffset, packedOrigin,
            ConcreteElaboration.WireContext.origin] using
              induction tailValue

private theorem fragmentMapped_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (ids : List fragment.val.diagram.WireId)
    (value :
      PackedVar
        (ids.map
          (fun wire => (fragment.val.diagram.wires wire).sig))) :
    packedOrigin attachment.diagram
        (ids.map attachment.fragmentWire)
        (castPacked (fragmentMappedSigsEq attachment ids).symm
          value) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram ids value) := by
  let mapped :=
    castPacked (fragmentMappedSigsEq attachment ids).symm value
  have mappedOffset :
      packedOffset mapped = packedOffset value := by
    exact packedOffset_castPacked
      (fragmentMappedSigsEq attachment ids).symm value
  have targetLookup :=
    packedOrigin_get? attachment.diagram
      (ids.map attachment.fragmentWire) mapped
  have sourceLookup :=
    packedOrigin_get? fragment.val.diagram ids value
  have mapLookup :
      (ids.map attachment.fragmentWire)[packedOffset value]? =
        ids[packedOffset value]?.map
          attachment.fragmentWire := by
    simp
  have lookupIndex :=
    congrArg
      (fun offset =>
        (ids.map attachment.fragmentWire)[offset]?)
      mappedOffset
  have targetAtValue :
      (ids.map attachment.fragmentWire)[packedOffset value]? =
        some
          (packedOrigin attachment.diagram
            (ids.map attachment.fragmentWire) mapped) :=
    lookupIndex.symm.trans targetLookup
  have mappedSource :=
    congrArg (Option.map attachment.fragmentWire) sourceLookup
  exact Option.some.inj
    (targetAtValue.symm.trans
      (mapLookup.trans mappedSource))

private theorem candidateSiteLocalSigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    (attachment.diagram.wiresAt
        (attachment.hostRegion removed.site)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (ConcreteElaboration.openRootLocalWires fragment.val).map
        (fun wire => (fragment.val.diagram.wires wire).sig) := by
  rw [candidate_wiresAt_site_eq]
  exact mappedRootLocalSigs_eq attachment

private theorem candidateSiteLocal_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (value :
      PackedVar
        ((ConcreteElaboration.openRootLocalWires fragment.val).map
          (fun wire => (fragment.val.diagram.wires wire).sig))) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))
        (castPacked
          (candidateSiteLocalSigs_eq attachment).symm value) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram
          (ConcreteElaboration.openRootLocalWires fragment.val)
          value) := by
  let mapped :=
    castPacked (candidateSiteLocalSigs_eq attachment).symm value
  have mappedOffset :
      packedOffset mapped = packedOffset value :=
    packedOffset_castPacked
      (candidateSiteLocalSigs_eq attachment).symm value
  have targetLookup :=
    packedOrigin_get? attachment.diagram
      (attachment.diagram.wiresAt
        (attachment.hostRegion removed.site)) mapped
  have sourceLookup :=
    packedOrigin_get? fragment.val.diagram
      (ConcreteElaboration.openRootLocalWires fragment.val) value
  have allocation :=
    congrArg
      (fun ids => ids[packedOffset value]?)
      (candidate_wiresAt_site_eq attachment)
  have mapLookup :
      ((ConcreteElaboration.openRootLocalWires fragment.val).map
          attachment.fragmentWire)[packedOffset value]? =
        (ConcreteElaboration.openRootLocalWires
          fragment.val)[packedOffset value]?.map
            attachment.fragmentWire := by
    simp
  have lookupIndex :=
    congrArg
      (fun offset =>
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))[offset]?)
      mappedOffset
  have targetAtValue :
      (attachment.diagram.wiresAt
        (attachment.hostRegion removed.site))[packedOffset value]? =
          some
            (packedOrigin attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.hostRegion removed.site)) mapped) :=
    lookupIndex.symm.trans targetLookup
  have mappedSource :=
    congrArg (Option.map attachment.fragmentWire) sourceLookup
  exact Option.some.inj
    (targetAtValue.symm.trans
      (allocation.trans (mapLookup.trans mappedSource)))

theorem fragmentRegionLocalSigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    (attachment.diagram.wiresAt
        (attachment.fragmentRegion region)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (fragment.val.diagram.wiresAt region).map
        (fun wire => (fragment.val.diagram.wires wire).sig) := by
  rw [candidate_wiresAt_fragmentRegion_eq attachment region nonroot]
  exact
    fragmentMappedSigsEq attachment
      (fragment.val.diagram.wiresAt region)

private theorem fragmentRegionLocal_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (value :
      PackedVar
        ((fragment.val.diagram.wiresAt region).map
          (fun wire => (fragment.val.diagram.wires wire).sig))) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        (castPacked
          (fragmentRegionLocalSigs_eq attachment region nonroot).symm
          value) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram
          (fragment.val.diagram.wiresAt region) value) := by
  let mapped :=
    castPacked
      (fragmentRegionLocalSigs_eq attachment region nonroot).symm
      value
  have mappedOffset :
      packedOffset mapped = packedOffset value :=
    packedOffset_castPacked
      (fragmentRegionLocalSigs_eq attachment region nonroot).symm
      value
  have targetLookup :=
    packedOrigin_get? attachment.diagram
      (attachment.diagram.wiresAt
        (attachment.fragmentRegion region)) mapped
  have sourceLookup :=
    packedOrigin_get? fragment.val.diagram
      (fragment.val.diagram.wiresAt region) value
  have allocation :=
    congrArg
      (fun ids => ids[packedOffset value]?)
      (candidate_wiresAt_fragmentRegion_eq
        attachment region nonroot)
  have mapLookup :
      ((fragment.val.diagram.wiresAt region).map
          attachment.fragmentWire)[packedOffset value]? =
        (fragment.val.diagram.wiresAt region)[
          packedOffset value]?.map attachment.fragmentWire := by
    simp
  have lookupIndex :=
    congrArg
      (fun offset =>
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))[offset]?)
      mappedOffset
  have targetAtValue :
      (attachment.diagram.wiresAt
        (attachment.fragmentRegion region))[packedOffset value]? =
          some
            (packedOrigin attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.fragmentRegion region)) mapped) :=
    lookupIndex.symm.trans targetLookup
  have mappedSource :=
    congrArg (Option.map attachment.fragmentWire) sourceLookup
  exact Option.some.inj
    (targetAtValue.symm.trans
      (allocation.trans (mapLookup.trans mappedSource)))

theorem sourceExtendedSigs_eq
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId) :
    (context.extend region).sigs =
      (diagram.wiresAt region).map
          (fun wire => (diagram.wires wire).sig) ++
        context.sigs :=
  ConcreteElaboration.WireContext.sigs_extend context region

theorem fragmentTargetExtendedSigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    (targetContext.extend
        (attachment.fragmentRegion region)).sigs =
      (fragment.val.diagram.wiresAt region).map
          (fun wire => (fragment.val.diagram.wires wire).sig) ++
        targetContext.sigs := by
  rw [ConcreteElaboration.WireContext.sigs_extend,
    fragmentRegionLocalSigs_eq attachment region nonroot]

def fragmentExtendedRenaming
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs) :
    WireRenaming
      (sourceContext.extend region).sigs
      (targetContext.extend
        (attachment.fragmentRegion region)).sigs :=
  fun {sig} value =>
    (fragmentTargetExtendedSigs_eq attachment targetContext
      region nonroot).symm ▸
      appendRenaming
        ((fragment.val.diagram.wiresAt region).map
          fun wire => (fragment.val.diagram.wires wire).sig)
        rho
        (sourceExtendedSigs_eq fragment.val.diagram
          sourceContext region ▸ value)

theorem fragmentExtendedRenaming_packed_action
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
    (value :
      PackedVar
        ((fragment.val.diagram.wiresAt region).map
            (fun wire =>
              (fragment.val.diagram.wires wire).sig) ++
          sourceContext.sigs)) :
    renamePacked
        (fragmentExtendedRenaming attachment region nonroot
          sourceContext targetContext rho)
        (castPacked
          (sourceExtendedSigs_eq fragment.val.diagram
            sourceContext region).symm value) =
      castPacked
        (fragmentTargetExtendedSigs_eq attachment
          targetContext region nonroot).symm
        (renamePacked
          (appendRenaming
            ((fragment.val.diagram.wiresAt region).map
              fun wire =>
                (fragment.val.diagram.wires wire).sig)
            rho)
          value) := by
  unfold fragmentExtendedRenaming
  exact renamePacked_transport
    (sourceExtendedSigs_eq fragment.val.diagram
      sourceContext region)
    (fragmentTargetExtendedSigs_eq attachment
      targetContext region nonroot)
    (appendRenaming
      ((fragment.val.diagram.wiresAt region).map
        fun wire => (fragment.val.diagram.wires wire).sig)
      rho)
    value

def rootFragmentRenaming
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment : ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment) :
    WireRenaming
      (⟨ConcreteElaboration.openRootLocalWires extracted.checked.val ++
          ConcreteElaboration.openBoundaryWires extracted.checked.val⟩ :
        ConcreteElaboration.WireContext
          extracted.checked.val.diagram).sigs
      (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site)).sigs :=
  fun {sig} value =>
    (candidateSiteContext_sigs_eq compiled).symm ▸
      appendRenaming
        ((ConcreteElaboration.openRootLocalWires
          extracted.checked.val).map fun wire =>
            (extracted.checked.val.diagram.wires wire).sig)
        (compiled.intrinsicAttachment extracted).classMap
        (openRootContext_sigs_eq extracted.checked ▸ value)

theorem castPacked_cancel
    (equality : source = target)
    (value : PackedVar source) :
    castPacked equality.symm (castPacked equality value) =
      value := by
  cases equality
  rfl

def appendRightPacked
    (prefixSigs : List Sig) :
    PackedVar suffix → PackedVar (prefixSigs ++ suffix)
  | ⟨sig, value⟩ => ⟨sig, Var.appendRight prefixSigs value⟩

def appendLeftPacked
    (suffixSigs : List Sig) :
    PackedVar prefixContext →
      PackedVar (prefixContext ++ suffixSigs)
  | ⟨sig, value⟩ => ⟨sig, Var.appendLeft value suffixSigs⟩

def liftPacked
    (headSig : Sig) :
    PackedVar context → PackedVar (headSig :: context)
  | ⟨sig, value⟩ => ⟨sig, Var.there value⟩

theorem packedVar_append_cases
    (value : PackedVar (left ++ right)) :
    (∃ localValue : PackedVar left,
      value = appendLeftPacked right localValue) ∨
    (∃ outer : PackedVar right,
      value = appendRightPacked left outer) := by
  induction left with
  | nil =>
      exact Or.inr ⟨value, rfl⟩
  | cons head tail induction =>
      rcases value with ⟨sig, value⟩
      cases value with
      | here =>
          exact Or.inl
            ⟨⟨head, Var.here⟩, rfl⟩
      | there tailValue =>
          rcases induction (⟨sig, tailValue⟩ :
              PackedVar (tail ++ right)) with
            ⟨localValue, same⟩ | ⟨outer, same⟩
          · exact Or.inl
              ⟨liftPacked head localValue, by
                simpa [liftPacked, appendLeftPacked] using
                  congrArg (liftPacked head) same⟩
          · exact Or.inr
              ⟨outer, by
                simpa [liftPacked, appendRightPacked] using
                  congrArg (liftPacked head) same⟩

theorem appendRenaming_appendLeftPacked
    (prefixSigs : List Sig)
    (rho : WireRenaming source target)
    (value : PackedVar prefixSigs) :
    renamePacked (appendRenaming prefixSigs rho)
        (appendLeftPacked source value) =
      appendLeftPacked target value := by
  induction prefixSigs with
  | nil =>
      cases value with
      | mk sig value => nomatch value
  | cons head tail induction =>
      rcases value with ⟨sig, value⟩
      cases value with
      | here => rfl
      | there tailValue =>
          have mapped :=
            induction (⟨sig, tailValue⟩ :
              PackedVar tail)
          change
            liftPacked head
                (renamePacked (appendRenaming tail rho)
                  (appendLeftPacked source
                    (⟨sig, tailValue⟩ : PackedVar tail))) =
              liftPacked head
                (appendLeftPacked target
                  (⟨sig, tailValue⟩ : PackedVar tail))
          exact congrArg (liftPacked head) mapped

private theorem origin_cast_appendLeftPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value : PackedVar prefixSigs) :
    packedOrigin diagram (leftIds ++ rightIds)
        (castPacked wholeEquality.symm
          (appendLeftPacked
            (rightIds.map
              (fun wire => (diagram.wires wire).sig))
            value)) =
      packedOrigin diagram leftIds
        (castPacked prefixEquality.symm value) := by
  cases prefixEquality
  induction leftIds with
  | nil =>
      rcases value with ⟨sig, value⟩
      nomatch value
  | cons head tail induction =>
      rcases value with ⟨sig, value⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      cases value with
      | here =>
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨(diagram.wires head).sig, Var.here⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨(diagram.wires head).sig, Var.here⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨(diagram.wires head).sig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_here_context tailCanonical)
          have originEquality :=
            congrArg
              (packedOrigin diagram (head :: tail ++ rightIds))
              castedPacked
          simpa [packedOrigin, castPacked] using originEquality
      | there tailValue =>
          let appendedTail :=
            Var.appendLeft tailValue
              (rightIds.map
                (fun wire => (diagram.wires wire).sig))
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨sig, Var.there tailValue⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨sig,
                  Var.there
                    (tailCanonical.symm ▸ appendedTail)⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨sig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_there_context tailCanonical appendedTail)
          have originEquality :=
            congrArg
              (packedOrigin diagram (head :: tail ++ rightIds))
              castedPacked
          have tailOrigin :=
            induction tailCanonical
              (⟨sig, tailValue⟩ :
                PackedVar
                  (tail.map
                    (fun wire => (diagram.wires wire).sig)))
          exact originEquality.trans (by
            simpa [packedOrigin, castPacked, appendedTail] using
              tailOrigin)

private theorem origin_cast_appendRightPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value :
      PackedVar
        (rightIds.map (fun wire => (diagram.wires wire).sig))) :
      (match
        castPacked wholeEquality.symm
          (appendRightPacked prefixSigs value) with
      | ⟨_, valueVar⟩ =>
          ConcreteElaboration.WireContext.origin diagram
            (leftIds ++ rightIds) valueVar) =
      (match value with
      | ⟨_, valueVar⟩ =>
          ConcreteElaboration.WireContext.origin diagram
            rightIds valueVar) := by
  subst prefixSigs
  induction leftIds with
  | nil =>
      have wholeRefl :
          wholeEquality = Eq.refl _ :=
        Subsingleton.elim _ _
      rw [wholeRefl]
      cases value
      rfl
  | cons head tail induction =>
      rcases value with ⟨valueSig, valueVar⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      let tailValue :=
        Var.appendRight
          (tail.map (fun wire => (diagram.wires wire).sig)) valueVar
      have castedPacked :
          castPacked wholeEquality.symm
              (⟨valueSig, Var.there tailValue⟩ :
                PackedVar
                  ((head :: tail).map
                      (fun wire => (diagram.wires wire).sig) ++
                    rightIds.map
                      (fun wire => (diagram.wires wire).sig))) =
            (⟨valueSig,
              Var.there (tailCanonical.symm ▸ tailValue)⟩ :
                PackedVar
                  ((head :: tail ++ rightIds).map
                    (fun wire => (diagram.wires wire).sig))) := by
        rw [wholeCanonical]
        unfold castPacked
        exact congrArg
          (fun casted =>
            (⟨valueSig, casted⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))))
          (cast_var_there_context tailCanonical tailValue)
      dsimp [tailValue] at castedPacked
      have castedOrigin :=
        congrArg
          (packedOrigin diagram (head :: tail ++ rightIds))
          castedPacked
      have tailOrigin := induction tailCanonical
      exact castedOrigin.trans (by
        simpa [packedOrigin, castPacked] using tailOrigin)

private theorem boundary_origin_eq_wireOfPacked
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (value :
      PackedVar
        (ids.map (fun wire => (diagram.wires wire).sig))) :
    packedOrigin diagram ids value =
      ExtractedBoundaryCompiler.wireOfPacked diagram ids value := by
  rcases value with ⟨sig, value⟩
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there tailValue =>
          exact induction tailValue

theorem denseIndex_value_congr
    [DecidableEq α]
    (values : List α)
    {left right : α}
    (same : left = right)
    (leftMember : left ∈ values)
    (rightMember : right ∈ values) :
    DenseList.index values left leftMember =
      DenseList.index values right rightMember := by
  subst right
  rfl

theorem appendRenaming_appendRightPacked
    (prefixSigs : List Sig)
    (rho : WireRenaming source target)
    (value : PackedVar source) :
    renamePacked (appendRenaming prefixSigs rho)
        (appendRightPacked prefixSigs value) =
      appendRightPacked prefixSigs (renamePacked rho value) := by
  induction prefixSigs with
  | nil => rfl
  | cons head tail induction =>
      cases value with
      | mk sig value =>
          change
            (⟨sig, Var.there
              (appendRenaming tail rho
                (Var.appendRight tail value))⟩ :
              PackedVar (head :: (tail ++ target))) =
            ⟨sig, Var.there
              (Var.appendRight tail (rho value))⟩
          exact congrArg
            (fun packed =>
              match packed with
              | ⟨packedSig, packedValue⟩ =>
                  (⟨packedSig, Var.there packedValue⟩ :
                    PackedVar (head :: (tail ++ target))))
            induction

private theorem rootFragmentRenaming_packed_action
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (value :
      PackedVar
        ((ConcreteElaboration.openRootLocalWires
          extracted.checked.val).map (fun wire =>
            (extracted.checked.val.diagram.wires wire).sig) ++
          extracted.openDiagram.classes)) :
    renamePacked (rootFragmentRenaming extracted compiled)
        (castPacked
          (openRootContext_sigs_eq extracted.checked).symm value) =
      castPacked (candidateSiteContext_sigs_eq compiled).symm
        (renamePacked
          (appendRenaming
            ((ConcreteElaboration.openRootLocalWires
              extracted.checked.val).map fun wire =>
                (extracted.checked.val.diagram.wires wire).sig)
            (compiled.intrinsicAttachment extracted).classMap)
          value) := by
  unfold rootFragmentRenaming
  exact renamePacked_transport
    (openRootContext_sigs_eq extracted.checked)
    (candidateSiteContext_sigs_eq compiled)
    (appendRenaming
      ((ConcreteElaboration.openRootLocalWires
        extracted.checked.val).map fun wire =>
          (extracted.checked.val.diagram.wires wire).sig)
      (compiled.intrinsicAttachment extracted).classMap)
    value

/--
The boundary part of the root renaming lands on the candidate variable at the
first concrete occurrence of the extracted boundary class.  Both context
transports and the root-local prefix are explicit, so this equality also
accounts for resolver signature casts.
-/
private theorem rootFragmentRenaming_boundary_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    {sig : Sig}
    (fiber : Var extracted.openDiagram.classes sig) :
    let source :=
      ExtractedBoundaryCompiler.wireOfPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires
          extracted.checked.val)
        (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes)
    let member :=
      SpliceCompilation.intrinsicClassWire_mem_boundary extracted fiber
    let representative :=
      attachment.representativePosition source member
    renamePacked (rootFragmentRenaming extracted compiled)
        (castPacked
          (openRootContext_sigs_eq extracted.checked).symm
          (appendRightPacked
            ((ConcreteElaboration.openRootLocalWires
              extracted.checked.val).map fun wire =>
                (extracted.checked.val.diagram.wires wire).sig)
            (⟨sig, fiber⟩ :
              PackedVar extracted.openDiagram.classes))) =
      castPacked (candidateSiteContext_sigs_eq compiled).symm
        (appendRightPacked
          ((ConcreteElaboration.openRootLocalWires
            extracted.checked.val).map fun wire =>
              (extracted.checked.val.diagram.wires wire).sig)
          (compiled.positionPackedAt representative)) := by
  dsimp only
  rw [rootFragmentRenaming_packed_action]
  let localSigs :=
    (ConcreteElaboration.openRootLocalWires
      extracted.checked.val).map fun wire =>
        (extracted.checked.val.diagram.wires wire).sig
  have appended :=
    appendRenaming_appendRightPacked localSigs
      (compiled.intrinsicAttachment extracted).classMap
      (⟨sig, fiber⟩ :
        PackedVar extracted.openDiagram.classes)
  have classOrigin :=
    compiled.intrinsicAttachment_classMap_eq_positionPackedAt
      extracted fiber
  calc
    _ = castPacked (candidateSiteContext_sigs_eq compiled).symm
          (appendRightPacked localSigs
            (renamePacked
              (compiled.intrinsicAttachment extracted).classMap
              (⟨sig, fiber⟩ :
                PackedVar extracted.openDiagram.classes))) :=
      congrArg
        (castPacked
          (candidateSiteContext_sigs_eq compiled).symm)
        appended
    _ = _ :=
      congrArg
        (castPacked
          (candidateSiteContext_sigs_eq compiled).symm)
        (congrArg (appendRightPacked localSigs) classOrigin)

private theorem positionPackedAt_public_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (position : Fin fragment.val.boundary.length) :
    (match compiled.positionPackedAt position with
      | ⟨_, value⟩ =>
          ConcreteElaboration.WireContext.origin attachment.diagram
            compiled.factor.frame.visible.ids value) =
      attachment.hostWire (attachment.target position) := by
  exact compiled.positionPackedAt_origin position

theorem rootFragmentRenaming_contextAction
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    {sig : Sig}
    (value :
      Var
        (⟨ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val⟩ :
          ConcreteElaboration.WireContext
            extracted.checked.val.diagram).sigs
        sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (rootFragmentRenaming extracted compiled value) =
      attachment.fragmentWire
        (ConcreteElaboration.WireContext.origin
          extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val)
          value) := by
  let sourcePacked :=
    (⟨sig, value⟩ :
      PackedVar
        (⟨ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val⟩ :
          ConcreteElaboration.WireContext
            extracted.checked.val.diagram).sigs)
  let normalized :=
    castPacked
      (openRootContext_sigs_eq extracted.checked)
      sourcePacked
  have sourceRoundTrip :
      castPacked
          (openRootContext_sigs_eq extracted.checked).symm
          normalized =
        sourcePacked := by
    unfold normalized
    exact castPacked_cancel
      (openRootContext_sigs_eq extracted.checked) sourcePacked
  have action :=
    rootFragmentRenaming_packed_action
      extracted compiled normalized
  rw [sourceRoundTrip] at action
  change
    packedOrigin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (renamePacked
          (rootFragmentRenaming extracted compiled)
          sourcePacked) =
      attachment.fragmentWire
        (packedOrigin extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val)
          sourcePacked)
  have targetOrigin :=
    congrArg
      (packedOrigin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids)
      action
  refine targetOrigin.trans ?_
  rcases packedVar_append_cases normalized with
    ⟨localValue, normalizedEquality⟩ |
      ⟨boundaryValue, normalizedEquality⟩
  · rw [normalizedEquality]
    let localSigs :=
      (ConcreteElaboration.openRootLocalWires
        extracted.checked.val).map fun wire =>
          (extracted.checked.val.diagram.wires wire).sig
    have renamedLocal :
        renamePacked
            (appendRenaming localSigs
              (compiled.intrinsicAttachment extracted).classMap)
            (appendLeftPacked
              extracted.openDiagram.classes localValue) =
          appendLeftPacked
            compiled.factor.frame.visible.sigs localValue :=
      appendRenaming_appendLeftPacked localSigs
        (compiled.intrinsicAttachment extracted).classMap
        localValue
    have targetLocalPacked :=
      congrArg
        (castPacked
          (candidateSiteContext_sigs_eq compiled).symm)
        renamedLocal
    have targetPackedOrigin :=
      congrArg
        (packedOrigin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids)
        targetLocalPacked
    have sourceLocalPacked :
        castPacked
            (openRootContext_sigs_eq extracted.checked).symm
            (appendLeftPacked
              extracted.openDiagram.classes localValue) =
          sourcePacked := by
      calc
        _ = castPacked
              (openRootContext_sigs_eq extracted.checked).symm
              normalized :=
          congrArg
            (castPacked
              (openRootContext_sigs_eq extracted.checked).symm)
            normalizedEquality.symm
        _ = sourcePacked := sourceRoundTrip
    have sourcePackedOrigin :=
      congrArg
        (packedOrigin extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val))
        sourceLocalPacked
    have targetWholeEquality :
        (attachment.diagram.wiresAt
              (attachment.hostRegion removed.site) ++
            compiled.factor.frame.visible.ids).map
            (fun wire => (attachment.diagram.wires wire).sig) =
          localSigs ++
            compiled.factor.frame.visible.ids.map
              (fun wire => (attachment.diagram.wires wire).sig) := by
      exact candidateSiteContext_sigs_eq compiled
    have targetLocalOrigin :=
      origin_cast_appendLeftPacked attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))
        compiled.factor.frame.visible.ids localSigs
        (candidateSiteLocalSigs_eq attachment)
        targetWholeEquality localValue
    have sourceLocalOrigin :=
      origin_cast_appendLeftPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openRootLocalWires
          extracted.checked.val)
        (ConcreteElaboration.openBoundaryWires
          extracted.checked.val)
        localSigs rfl
        (openRootContext_sigs_eq extracted.checked)
        localValue
    calc
      _ = packedOrigin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (castPacked
              (candidateSiteContext_sigs_eq compiled).symm
              (appendLeftPacked
                compiled.factor.frame.visible.sigs
                localValue)) := targetPackedOrigin
      _ = packedOrigin attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.hostRegion removed.site))
            (castPacked
              (candidateSiteLocalSigs_eq attachment).symm
              localValue) := targetLocalOrigin
      _ = attachment.fragmentWire
            (packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                extracted.checked.val)
              localValue) :=
        candidateSiteLocal_origin attachment localValue
      _ = attachment.fragmentWire
            (packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
              (castPacked
                (openRootContext_sigs_eq
                  extracted.checked).symm
                (appendLeftPacked
                  extracted.openDiagram.classes
                  localValue))) :=
        congrArg attachment.fragmentWire sourceLocalOrigin.symm
      _ = attachment.fragmentWire
            (packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
              sourcePacked) :=
        congrArg attachment.fragmentWire sourcePackedOrigin
  · rcases boundaryValue with ⟨boundarySig, boundaryVar⟩
    rw [normalizedEquality]
    let localSigs :=
      (ConcreteElaboration.openRootLocalWires
        extracted.checked.val).map fun wire =>
          (extracted.checked.val.diagram.wires wire).sig
    let boundaryPacked :=
      (⟨boundarySig, boundaryVar⟩ :
        PackedVar extracted.openDiagram.classes)
    let source :=
      ExtractedBoundaryCompiler.wireOfPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires
          extracted.checked.val)
        boundaryPacked
    let member :=
      SpliceCompilation.intrinsicClassWire_mem_boundary
        extracted boundaryVar
    let representative :=
      attachment.representativePosition source member
    have appended :=
      appendRenaming_appendRightPacked localSigs
        (compiled.intrinsicAttachment extracted).classMap
        boundaryPacked
    have classOrigin :=
      compiled.intrinsicAttachment_classMap_eq_positionPackedAt
        extracted boundaryVar
    have renamedBoundary :
        renamePacked
            (appendRenaming localSigs
              (compiled.intrinsicAttachment extracted).classMap)
            (appendRightPacked localSigs boundaryPacked) =
          appendRightPacked localSigs
            (compiled.positionPackedAt representative) := by
      exact appended.trans
        (congrArg (appendRightPacked localSigs) classOrigin)
    have targetBoundaryPacked :=
      congrArg
        (castPacked
          (candidateSiteContext_sigs_eq compiled).symm)
        renamedBoundary
    have targetPackedOrigin :=
      congrArg
        (packedOrigin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids)
        targetBoundaryPacked
    have sourceBoundaryPacked :
        castPacked
            (openRootContext_sigs_eq extracted.checked).symm
            (appendRightPacked localSigs boundaryPacked) =
          sourcePacked := by
      calc
        _ = castPacked
              (openRootContext_sigs_eq extracted.checked).symm
              normalized :=
          congrArg
            (castPacked
              (openRootContext_sigs_eq extracted.checked).symm)
            normalizedEquality.symm
        _ = sourcePacked := sourceRoundTrip
    have sourcePackedOrigin :=
      congrArg
        (packedOrigin extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val))
        sourceBoundaryPacked
    have targetWholeEquality :
        (attachment.diagram.wiresAt
              (attachment.hostRegion removed.site) ++
            compiled.factor.frame.visible.ids).map
            (fun wire => (attachment.diagram.wires wire).sig) =
          localSigs ++
            compiled.factor.frame.visible.ids.map
              (fun wire => (attachment.diagram.wires wire).sig) := by
      exact candidateSiteContext_sigs_eq compiled
    have targetBoundaryOrigin :=
      origin_cast_appendRightPacked attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))
        compiled.factor.frame.visible.ids localSigs
        (candidateSiteLocalSigs_eq attachment)
        targetWholeEquality
        (compiled.positionPackedAt representative)
    have sourceBoundaryOrigin :=
      origin_cast_appendRightPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openRootLocalWires
          extracted.checked.val)
        (ConcreteElaboration.openBoundaryWires
          extracted.checked.val)
        localSigs rfl
        (openRootContext_sigs_eq extracted.checked)
        boundaryPacked
    have sourceWholeOrigin :
        packedOrigin extracted.checked.val.diagram
            (ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val)
            sourcePacked =
          source := by
      calc
        _ = packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
              (castPacked
                (openRootContext_sigs_eq
                  extracted.checked).symm
                (appendRightPacked localSigs
                  boundaryPacked)) :=
          sourcePackedOrigin.symm
        _ = packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openBoundaryWires
                extracted.checked.val)
              boundaryPacked :=
          sourceBoundaryOrigin
        _ = source :=
          boundary_origin_eq_wireOfPacked
            extracted.checked.val.diagram
            (ConcreteElaboration.openBoundaryWires
              extracted.checked.val)
            boundaryPacked
    have fragmentWireSource :
        attachment.fragmentWire source =
          attachment.hostWire
            (attachment.target representative) := by
      unfold ConcreteSpliceAttachment.fragmentWire
      split
      · unfold ConcreteSpliceAttachment.representativeTarget
          representative source
        congr
      · rename_i notBoundary
        exact (notBoundary member).elim
    calc
      _ = packedOrigin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (castPacked
              (candidateSiteContext_sigs_eq compiled).symm
              (appendRightPacked localSigs
                (compiled.positionPackedAt representative))) :=
        targetPackedOrigin
      _ = packedOrigin attachment.diagram
            compiled.factor.frame.visible.ids
            (compiled.positionPackedAt representative) :=
        targetBoundaryOrigin
      _ = attachment.hostWire
            (attachment.target representative) :=
        positionPackedAt_public_origin compiled representative
      _ = attachment.fragmentWire source :=
        fragmentWireSource.symm
      _ = attachment.fragmentWire
            (packedOrigin extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
              sourcePacked) :=
        congrArg attachment.fragmentWire sourceWholeOrigin.symm

theorem fragmentExtendedRenaming_contextAction
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho :
      WireRenaming sourceContext.sigs targetContext.sigs)
    (outerAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    {sig : Sig}
    (value : Var (sourceContext.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids
        (fragmentExtendedRenaming attachment region nonroot
          sourceContext targetContext rho value) =
      attachment.fragmentWire
        (ConcreteElaboration.WireContext.origin
          fragment.val.diagram
          (sourceContext.extend region).ids value) := by
  let localSigs :=
    (fragment.val.diagram.wiresAt region).map fun wire =>
      (fragment.val.diagram.wires wire).sig
  let sourcePacked :=
    (⟨sig, value⟩ :
      PackedVar (sourceContext.extend region).sigs)
  let normalized :=
    castPacked
      (sourceExtendedSigs_eq fragment.val.diagram
        sourceContext region)
      sourcePacked
  have sourceRoundTrip :
      castPacked
          (sourceExtendedSigs_eq fragment.val.diagram
            sourceContext region).symm
          normalized =
        sourcePacked := by
    unfold normalized
    exact castPacked_cancel
      (sourceExtendedSigs_eq fragment.val.diagram
        sourceContext region)
      sourcePacked
  have action :=
    fragmentExtendedRenaming_packed_action attachment
      region nonroot sourceContext targetContext rho normalized
  rw [sourceRoundTrip] at action
  change
    packedOrigin attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids
        (renamePacked
          (fragmentExtendedRenaming attachment region nonroot
            sourceContext targetContext rho)
          sourcePacked) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram
          (sourceContext.extend region).ids sourcePacked)
  have targetOrigin :=
    congrArg
      (packedOrigin attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids)
      action
  refine targetOrigin.trans ?_
  rcases packedVar_append_cases normalized with
    ⟨localValue, normalizedEquality⟩ |
      ⟨outerValue, normalizedEquality⟩
  · rw [normalizedEquality]
    have renamedLocal :
        renamePacked (appendRenaming localSigs rho)
            (appendLeftPacked sourceContext.sigs localValue) =
          appendLeftPacked targetContext.sigs localValue :=
      appendRenaming_appendLeftPacked localSigs rho localValue
    have targetLocalPacked :=
      congrArg
        (castPacked
          (fragmentTargetExtendedSigs_eq attachment
            targetContext region nonroot).symm)
        renamedLocal
    have targetPackedOrigin :=
      congrArg
        (packedOrigin attachment.diagram
          (targetContext.extend
            (attachment.fragmentRegion region)).ids)
        targetLocalPacked
    have sourceLocalPacked :
        castPacked
            (sourceExtendedSigs_eq fragment.val.diagram
              sourceContext region).symm
            (appendLeftPacked sourceContext.sigs localValue) =
          sourcePacked := by
      calc
        _ = castPacked
              (sourceExtendedSigs_eq fragment.val.diagram
                sourceContext region).symm
              normalized :=
          congrArg
            (castPacked
              (sourceExtendedSigs_eq fragment.val.diagram
                sourceContext region).symm)
            normalizedEquality.symm
        _ = sourcePacked := sourceRoundTrip
    have sourcePackedOrigin :=
      congrArg
        (packedOrigin fragment.val.diagram
          (sourceContext.extend region).ids)
        sourceLocalPacked
    have targetLocalOrigin :=
      origin_cast_appendLeftPacked attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        targetContext.ids localSigs
        (fragmentRegionLocalSigs_eq attachment region nonroot)
        (fragmentTargetExtendedSigs_eq attachment
          targetContext region nonroot)
        localValue
    have sourceLocalOrigin :=
      origin_cast_appendLeftPacked fragment.val.diagram
        (fragment.val.diagram.wiresAt region)
        sourceContext.ids localSigs rfl
        (sourceExtendedSigs_eq fragment.val.diagram
          sourceContext region)
        localValue
    calc
      _ = packedOrigin attachment.diagram
            (targetContext.extend
              (attachment.fragmentRegion region)).ids
            (castPacked
              (fragmentTargetExtendedSigs_eq attachment
                targetContext region nonroot).symm
              (appendLeftPacked targetContext.sigs
                localValue)) :=
        targetPackedOrigin
      _ = packedOrigin attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.fragmentRegion region))
            (castPacked
              (fragmentRegionLocalSigs_eq
                attachment region nonroot).symm
              localValue) :=
        targetLocalOrigin
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (fragment.val.diagram.wiresAt region)
              localValue) :=
        fragmentRegionLocal_origin
          attachment region nonroot localValue
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (sourceContext.extend region).ids
              (castPacked
                (sourceExtendedSigs_eq fragment.val.diagram
                  sourceContext region).symm
                (appendLeftPacked sourceContext.sigs
                  localValue))) :=
        congrArg attachment.fragmentWire sourceLocalOrigin.symm
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (sourceContext.extend region).ids
              sourcePacked) :=
        congrArg attachment.fragmentWire sourcePackedOrigin
  · rw [normalizedEquality]
    have renamedOuter :=
      appendRenaming_appendRightPacked localSigs rho outerValue
    have targetOuterPacked :=
      congrArg
        (castPacked
          (fragmentTargetExtendedSigs_eq attachment
            targetContext region nonroot).symm)
        renamedOuter
    have targetPackedOrigin :=
      congrArg
        (packedOrigin attachment.diagram
          (targetContext.extend
            (attachment.fragmentRegion region)).ids)
        targetOuterPacked
    have sourceOuterPacked :
        castPacked
            (sourceExtendedSigs_eq fragment.val.diagram
              sourceContext region).symm
            (appendRightPacked localSigs outerValue) =
          sourcePacked := by
      calc
        _ = castPacked
              (sourceExtendedSigs_eq fragment.val.diagram
                sourceContext region).symm
              normalized :=
          congrArg
            (castPacked
              (sourceExtendedSigs_eq fragment.val.diagram
                sourceContext region).symm)
            normalizedEquality.symm
        _ = sourcePacked := sourceRoundTrip
    have sourcePackedOrigin :=
      congrArg
        (packedOrigin fragment.val.diagram
          (sourceContext.extend region).ids)
        sourceOuterPacked
    have targetOuterOrigin :=
      origin_cast_appendRightPacked attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        targetContext.ids localSigs
        (fragmentRegionLocalSigs_eq attachment region nonroot)
        (fragmentTargetExtendedSigs_eq attachment
          targetContext region nonroot)
        (renamePacked rho outerValue)
    have sourceOuterOrigin :=
      origin_cast_appendRightPacked fragment.val.diagram
        (fragment.val.diagram.wiresAt region)
        sourceContext.ids localSigs rfl
        (sourceExtendedSigs_eq fragment.val.diagram
          sourceContext region)
        outerValue
    have outerOrigin :
        packedOrigin attachment.diagram targetContext.ids
            (renamePacked rho outerValue) =
          attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              sourceContext.ids outerValue) := by
      rcases outerValue with ⟨outerSig, outerVar⟩
      exact outerAction outerVar
    calc
      _ = packedOrigin attachment.diagram
            (targetContext.extend
              (attachment.fragmentRegion region)).ids
            (castPacked
              (fragmentTargetExtendedSigs_eq attachment
                targetContext region nonroot).symm
              (appendRightPacked localSigs
                (renamePacked rho outerValue))) :=
        targetPackedOrigin
      _ = packedOrigin attachment.diagram
            targetContext.ids
            (renamePacked rho outerValue) :=
        targetOuterOrigin
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              sourceContext.ids outerValue) :=
        outerOrigin
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (sourceContext.extend region).ids
              (castPacked
                (sourceExtendedSigs_eq fragment.val.diagram
                  sourceContext region).symm
                (appendRightPacked localSigs outerValue))) :=
        congrArg attachment.fragmentWire sourceOuterOrigin.symm
      _ = attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (sourceContext.extend region).ids
              sourcePacked) :=
        congrArg attachment.fragmentWire sourcePackedOrigin


private def appendRightIds
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId) :
    {rightIds : List diagram.WireId} → {sig : Sig} →
      Var (rightIds.map fun wire => (diagram.wires wire).sig) sig →
        Var ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig) sig
  | _, _, value =>
      match leftIds with
      | [] => value
      | _ :: tail => .there (appendRightIds diagram tail value)

private def appendLeftIds
    (diagram : ConcreteDiagram definitionCount)
    (rightIds : List diagram.WireId) :
    {leftIds : List diagram.WireId} → {sig : Sig} →
      Var (leftIds.map fun wire => (diagram.wires wire).sig) sig →
        Var ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig) sig
  | [], _, value => nomatch value
  | _ :: _, _, .here => .here
  | _ :: tail, _, .there value =>
      .there (appendLeftIds diagram rightIds (leftIds := tail) value)

private def appendRightIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId)
    {rightIds : List diagram.WireId} :
    PackedVar
        (rightIds.map fun wire => (diagram.wires wire).sig) →
      PackedVar
        ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig)
  | ⟨sig, value⟩ => ⟨sig, appendRightIds diagram leftIds value⟩

private def appendLeftIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (rightIds : List diagram.WireId)
    {leftIds : List diagram.WireId} :
    PackedVar
        (leftIds.map fun wire => (diagram.wires wire).sig) →
      PackedVar
        ((leftIds ++ rightIds).map
          fun wire => (diagram.wires wire).sig)
  | ⟨sig, value⟩ => ⟨sig, appendLeftIds diagram rightIds value⟩

private theorem cast_appendRightPacked_eq_appendRightIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value :
      PackedVar
        (rightIds.map fun wire => (diagram.wires wire).sig)) :
    castPacked wholeEquality.symm
        (appendRightPacked prefixSigs value) =
      appendRightIdsPacked diagram leftIds value := by
  subst prefixSigs
  induction leftIds with
  | nil =>
      have wholeRefl : wholeEquality = Eq.refl _ :=
        Subsingleton.elim _ _
      rw [wholeRefl]
      rfl
  | cons head tail induction =>
      rcases value with ⟨valueSig, valueVar⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      let tailValue :=
        Var.appendRight
          (tail.map fun wire => (diagram.wires wire).sig)
          valueVar
      have castedPacked :
          castPacked wholeEquality.symm
              (appendRightPacked
                ((head :: tail).map
                  (fun wire => (diagram.wires wire).sig))
                (⟨valueSig, valueVar⟩ :
                  PackedVar
                    (rightIds.map fun wire =>
                      (diagram.wires wire).sig))) =
            (⟨valueSig,
              Var.there (tailCanonical.symm ▸ tailValue)⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))) := by
        rw [wholeCanonical]
        unfold appendRightPacked castPacked
        exact congrArg
          (fun casted =>
            (⟨valueSig, casted⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))))
          (cast_var_there_context tailCanonical tailValue)
      have tailResult :=
        induction tailCanonical
      have liftedTail :=
        congrArg (liftPacked (diagram.wires head).sig) tailResult
      change
        (⟨valueSig,
          Var.there (tailCanonical.symm ▸ tailValue)⟩ :
          PackedVar
            ((head :: tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig))) =
        appendRightIdsPacked diagram (head :: tail)
          (⟨valueSig, valueVar⟩ :
            PackedVar
              (rightIds.map fun wire =>
                (diagram.wires wire).sig)) at liftedTail
      exact castedPacked.trans liftedTail

private theorem cast_appendLeftPacked_eq_appendLeftIdsPacked
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    (prefixSigs : List Sig)
    (prefixEquality :
      leftIds.map (fun wire => (diagram.wires wire).sig) =
        prefixSigs)
    (wholeEquality :
      (leftIds ++ rightIds).map
          (fun wire => (diagram.wires wire).sig) =
        prefixSigs ++
          rightIds.map (fun wire => (diagram.wires wire).sig))
    (value : PackedVar prefixSigs) :
    castPacked wholeEquality.symm
        (appendLeftPacked
          (rightIds.map fun wire => (diagram.wires wire).sig)
          value) =
      appendLeftIdsPacked diagram rightIds
        (castPacked prefixEquality.symm value) := by
  cases prefixEquality
  induction leftIds with
  | nil =>
      rcases value with ⟨sig, value⟩
      nomatch value
  | cons head tail induction =>
      rcases value with ⟨valueSig, valueVar⟩
      let tailCanonical :
          (tail ++ rightIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              rightIds.map
                (fun wire => (diagram.wires wire).sig) := by
        simp
      have wholeCanonical :
          wholeEquality =
            congrArg
              (List.cons (diagram.wires head).sig)
              tailCanonical :=
        Subsingleton.elim _ _
      cases valueVar with
      | here =>
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨(diagram.wires head).sig, Var.here⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨(diagram.wires head).sig, Var.here⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨(diagram.wires head).sig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_here_context tailCanonical)
          exact castedPacked
      | there tailValue =>
          let appendedTail :=
            Var.appendLeft tailValue
              (rightIds.map
                (fun wire => (diagram.wires wire).sig))
          have castedPacked :
              castPacked wholeEquality.symm
                  (appendLeftPacked
                    (rightIds.map
                      (fun wire => (diagram.wires wire).sig))
                    (⟨valueSig, Var.there tailValue⟩ :
                      PackedVar
                        ((head :: tail).map
                          (fun wire =>
                            (diagram.wires wire).sig)))) =
                (⟨valueSig,
                  Var.there
                    (tailCanonical.symm ▸ appendedTail)⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))) := by
            rw [wholeCanonical]
            unfold appendLeftPacked castPacked
            exact congrArg
              (fun casted =>
                (⟨valueSig, casted⟩ :
                  PackedVar
                    ((head :: tail ++ rightIds).map
                      (fun wire => (diagram.wires wire).sig))))
              (cast_var_there_context tailCanonical appendedTail)
          have tailResult :=
            induction tailCanonical
              (⟨valueSig, tailValue⟩ :
                PackedVar
                  (tail.map fun wire =>
                    (diagram.wires wire).sig))
          have liftedTail :=
            congrArg (liftPacked (diagram.wires head).sig) tailResult
          change
            (⟨valueSig,
              Var.there (tailCanonical.symm ▸ appendedTail)⟩ :
              PackedVar
                ((head :: tail ++ rightIds).map
                  (fun wire => (diagram.wires wire).sig))) =
            appendLeftIdsPacked diagram rightIds
              (⟨valueSig, Var.there tailValue⟩ :
                PackedVar
                  ((head :: tail).map fun wire =>
                    (diagram.wires wire).sig)) at liftedTail
          exact castedPacked.trans liftedTail

private def wireValue
    (values : ConcreteElaboration.WireValues pre sigs) :
    {sig : Sig} → Var sigs sig → pre.Domain sig
  | _, value =>
      match values, value with
      | .cons head _, .here => head
      | .cons _ tail, .there rest => wireValue tail rest

private theorem wireValues_cast_cancel
    (equality : source = target)
    (values : ConcreteElaboration.WireValues pre source) :
    equality.symm ▸ (equality ▸ values) = values := by
  cases equality
  rfl

private theorem wireValue_cast
    (equality : source = target)
    (values : ConcreteElaboration.WireValues pre source)
    {sig : Sig}
    (value : Var source sig) :
    wireValue (equality ▸ values) (equality ▸ value) =
      wireValue values value := by
  cases equality
  rfl

private theorem extendEnvironment_outer
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value : Var context.sigs sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (appendRightIds diagram (diagram.wiresAt region) value) =
      outerEnv sig value := by
  unfold ConcreteElaboration.extendEnvironment
  revert values
  generalize localIdsEquation :
      diagram.wiresAt region = localIds
  clear localIdsEquation
  induction localIds with
  | nil =>
      intro values
      cases values
      rfl
  | cons head tail induction =>
      intro values
      cases values with
      | cons headValue tailValues =>
          exact induction tailValues

private theorem extendEnvironment_local
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig}
    (value :
      Var
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig)
        sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (appendLeftIds diagram context.ids value) =
      wireValue values value := by
  unfold ConcreteElaboration.extendEnvironment
  revert values sig value
  generalize localIdsEquation :
      diagram.wiresAt region = localIds
  clear localIdsEquation
  induction localIds with
  | nil =>
      intro values sig value
      nomatch value
  | cons head tail induction =>
      intro values sig value
      cases values with
      | cons headValue tailValues =>
          cases value with
          | here => rfl
          | there rest =>
              exact induction tailValues rest

private def evaluatePacked
    {pre : PreModel}
    (env : Env pre sigs) :
    PackedVar sigs → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private theorem sigmaValue_inj
    {pre : PreModel}
    {left right : pre.Domain sig}
    (same :
      (⟨sig, left⟩ : Sigma pre.Domain) =
        ⟨sig, right⟩) :
    left = right := by
  exact eq_of_heq (Sigma.mk.inj same).2


private theorem extendOpenRootEnvironment_local
    (openDiagram : OpenConcreteDiagram definitionCount)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig))
    (boundaryEnv :
      Env pre
        ((ConcreteElaboration.openBoundaryWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((ConcreteElaboration.openRootLocalWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig)
        sig) :
    ConcreteElaboration.extendOpenRootEnvironment openDiagram values
        boundaryEnv sig
        (appendLeftIds openDiagram.diagram
          (ConcreteElaboration.openBoundaryWires openDiagram) value) =
      wireValue values value := by
  unfold ConcreteElaboration.extendOpenRootEnvironment
  revert values sig value
  generalize
    ConcreteElaboration.openRootLocalWires openDiagram = localIds
  induction localIds with
  | nil =>
      intro values sig value
      nomatch value
  | cons _ tail induction =>
      intro values sig value
      cases values with
      | cons headValue tailValues =>
          cases value with
          | here => rfl
          | there rest =>
              exact induction tailValues rest

private theorem extendOpenRootEnvironment_outer
    (openDiagram : OpenConcreteDiagram definitionCount)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig))
    (boundaryEnv :
      Env pre
        ((ConcreteElaboration.openBoundaryWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        ((ConcreteElaboration.openBoundaryWires openDiagram).map
          fun wire => (openDiagram.diagram.wires wire).sig)
        sig) :
    ConcreteElaboration.extendOpenRootEnvironment openDiagram values
        boundaryEnv sig
        (appendRightIds openDiagram.diagram
          (ConcreteElaboration.openRootLocalWires openDiagram) value) =
      boundaryEnv sig value := by
  unfold ConcreteElaboration.extendOpenRootEnvironment
  revert values
  generalize
    ConcreteElaboration.openRootLocalWires openDiagram = localIds
  induction localIds with
  | nil =>
      intro values
      cases values
      rfl
  | cons _ tail induction =>
      intro values
      cases values with
      | cons _ tailValues =>
          exact induction tailValues

private theorem extractedOpenRootContext_sigs_eq
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence) :
    (⟨ConcreteElaboration.openRootLocalWires extracted.checked.val ++
        ConcreteElaboration.openBoundaryWires extracted.checked.val⟩ :
      ConcreteElaboration.WireContext
        extracted.checked.val.diagram).sigs =
      (ConcreteElaboration.openRootLocalWires
        extracted.checked.val).map
          (fun wire =>
            (extracted.checked.val.diagram.wires wire).sig) ++
        extracted.openDiagram.classes := by
  simpa [ExtractionCompilation.openDiagram,
    ExtractionCompilation.checked] using
      (openRootContext_sigs_eq extracted.checked)

/--
Transporting root-local values to the splice site makes the root fragment
renaming commute exactly with environment extension.
-/
theorem rootFragmentRenaming_extendEnvironment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((ConcreteElaboration.openRootLocalWires
          extracted.checked.val).map
            fun wire =>
              (extracted.checked.val.diagram.wires wire).sig))
    (env : Env pre compiled.factor.frame.visible.sigs)
    (siteLocalSigsEquality :
      (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site)).map
            (fun wire => (attachment.diagram.wires wire).sig) =
        (ConcreteElaboration.openRootLocalWires
          extracted.checked.val).map
            (fun wire =>
              (extracted.checked.val.diagram.wires wire).sig)) :
    Env.comp
        (ConcreteElaboration.extendEnvironment attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          (siteLocalSigsEquality.symm ▸ sourceValues) env)
        (rootFragmentRenaming extracted compiled) =
      ConcreteElaboration.extendOpenRootEnvironment
        extracted.checked.val sourceValues
        (Env.comp env
          (compiled.intrinsicAttachment extracted).classMap) := by
  funext sig value
  let localSigs :=
    (ConcreteElaboration.openRootLocalWires
      extracted.checked.val).map fun wire =>
        (extracted.checked.val.diagram.wires wire).sig
  let sourcePacked :=
    (⟨sig, value⟩ :
      PackedVar
        (⟨ConcreteElaboration.openRootLocalWires
              extracted.checked.val ++
            ConcreteElaboration.openBoundaryWires
              extracted.checked.val⟩ :
          ConcreteElaboration.WireContext
            extracted.checked.val.diagram).sigs)
  let normalized :=
    castPacked (extractedOpenRootContext_sigs_eq extracted)
      sourcePacked
  have sourceRoundTrip :
      castPacked
          (extractedOpenRootContext_sigs_eq extracted).symm normalized =
        sourcePacked := by
    unfold normalized
    exact castPacked_cancel
      (extractedOpenRootContext_sigs_eq extracted) sourcePacked
  have action :=
    rootFragmentRenaming_packed_action extracted compiled normalized
  have actionSourceRoundTrip :
      castPacked
          (openRootContext_sigs_eq extracted.checked).symm normalized =
        sourcePacked := by
    exact sourceRoundTrip
  rw [actionSourceRoundTrip] at action
  apply sigmaValue_inj
  change
    evaluatePacked
        (ConcreteElaboration.extendEnvironment attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          (siteLocalSigsEquality.symm ▸ sourceValues) env)
        (renamePacked (rootFragmentRenaming extracted compiled)
          sourcePacked) =
      evaluatePacked
        (ConcreteElaboration.extendOpenRootEnvironment
          extracted.checked.val sourceValues
          (Env.comp env
            (compiled.intrinsicAttachment extracted).classMap))
        sourcePacked
  rcases packedVar_append_cases normalized with
    ⟨localValue, normalizedEquality⟩ |
      ⟨boundaryValue, normalizedEquality⟩
  · have sourceAtLocal :
        castPacked
            (extractedOpenRootContext_sigs_eq extracted).symm
            (appendLeftPacked extracted.openDiagram.classes localValue) =
          sourcePacked := by
      rw [← normalizedEquality]
      exact sourceRoundTrip
    have sourceExact :=
      cast_appendLeftPacked_eq_appendLeftIdsPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openRootLocalWires extracted.checked.val)
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        localSigs rfl
        (extractedOpenRootContext_sigs_eq extracted)
        localValue
    have sourceExactEquality :
        sourcePacked =
          appendLeftIdsPacked extracted.checked.val.diagram
            (ConcreteElaboration.openBoundaryWires extracted.checked.val)
            localValue :=
      sourceAtLocal.symm.trans sourceExact
    rw [normalizedEquality,
      appendRenaming_appendLeftPacked] at action
    have targetExact :=
      cast_appendLeftPacked_eq_appendLeftIdsPacked
        attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))
        compiled.factor.frame.visible.ids localSigs
        siteLocalSigsEquality
        (candidateSiteContext_sigs_eq compiled)
        localValue
    let targetValues := siteLocalSigsEquality.symm ▸ sourceValues
    calc
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env)
            (castPacked
              (candidateSiteContext_sigs_eq compiled).symm
              (appendLeftPacked
                compiled.factor.frame.visible.sigs localValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env))
          action
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env)
            (appendLeftIdsPacked attachment.diagram
              compiled.factor.frame.visible.ids
              (castPacked siteLocalSigsEquality.symm localValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env))
          targetExact
      _ = evaluatePacked
            (ConcreteElaboration.extendOpenRootEnvironment
              extracted.checked.val sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap))
            (appendLeftIdsPacked extracted.checked.val.diagram
              (ConcreteElaboration.openBoundaryWires
                extracted.checked.val)
              localValue) := by
        rcases localValue with ⟨localSig, localVar⟩
        apply congrArg (Sigma.mk localSig)
        calc
          _ = wireValue targetValues
                (siteLocalSigsEquality.symm ▸ localVar) :=
            extendEnvironment_local attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              pre targetValues env _
          _ = wireValue sourceValues localVar := by
            unfold targetValues
            exact wireValue_cast siteLocalSigsEquality.symm
              sourceValues localVar
          _ = _ :=
            (extendOpenRootEnvironment_local extracted.checked.val pre
              sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap)
              localVar).symm
      _ = _ :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendOpenRootEnvironment
              extracted.checked.val sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap)))
          sourceExactEquality.symm
  · have sourceAtBoundary :
        castPacked
            (extractedOpenRootContext_sigs_eq extracted).symm
            (appendRightPacked localSigs boundaryValue) =
          sourcePacked := by
      rw [← normalizedEquality]
      exact sourceRoundTrip
    have sourceExact :=
      cast_appendRightPacked_eq_appendRightIdsPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openRootLocalWires extracted.checked.val)
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        localSigs rfl
        (extractedOpenRootContext_sigs_eq extracted)
        boundaryValue
    have sourceExactEquality :
        sourcePacked =
          appendRightIdsPacked extracted.checked.val.diagram
            (ConcreteElaboration.openRootLocalWires extracted.checked.val)
            boundaryValue :=
      sourceAtBoundary.symm.trans sourceExact
    rw [normalizedEquality,
      appendRenaming_appendRightPacked] at action
    have targetExact :=
      cast_appendRightPacked_eq_appendRightIdsPacked
        attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.hostRegion removed.site))
        compiled.factor.frame.visible.ids localSigs
        siteLocalSigsEquality
        (candidateSiteContext_sigs_eq compiled)
        (renamePacked
          (compiled.intrinsicAttachment extracted).classMap
          boundaryValue)
    let targetValues := siteLocalSigsEquality.symm ▸ sourceValues
    calc
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env)
            (castPacked
              (candidateSiteContext_sigs_eq compiled).symm
              (appendRightPacked localSigs
                (renamePacked
                  (compiled.intrinsicAttachment extracted).classMap
                  boundaryValue))) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env))
          action
      _ = evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env)
            (appendRightIdsPacked attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.hostRegion removed.site))
              (renamePacked
                (compiled.intrinsicAttachment extracted).classMap
                boundaryValue)) :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              targetValues env))
          targetExact
      _ = evaluatePacked
            (ConcreteElaboration.extendOpenRootEnvironment
              extracted.checked.val sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap))
            (appendRightIdsPacked extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                extracted.checked.val)
              boundaryValue) := by
        rcases boundaryValue with ⟨boundarySig, boundaryVar⟩
        apply congrArg (Sigma.mk boundarySig)
        calc
          _ = env boundarySig
                ((compiled.intrinsicAttachment extracted).classMap
                  boundaryVar) :=
            extendEnvironment_outer attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              pre targetValues env _
          _ = Env.comp env
                (compiled.intrinsicAttachment extracted).classMap
                boundarySig boundaryVar := rfl
          _ = _ :=
            (extendOpenRootEnvironment_outer extracted.checked.val pre
              sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap)
              boundaryVar).symm
      _ = _ :=
        congrArg
          (evaluatePacked
            (ConcreteElaboration.extendOpenRootEnvironment
              extracted.checked.val sourceValues
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap)))
          sourceExactEquality.symm


end RemovalFactorization

end VisualProof
