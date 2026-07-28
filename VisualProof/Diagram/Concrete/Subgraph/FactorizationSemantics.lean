import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturality

namespace VisualProof

namespace RemovalFactorization

private theorem reconstruction_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (extracted : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment removed extracted.checked)
    (accepted :
      reconstructionAttachment? occurrence extracted removed =
        some attachment)
    (result : ConcreteSpliceResult attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv result.checked ↔
      denoteChecked pre definitionEnv host :=
  iso_denotation
    (Reconstruction.extract_splice_iso occurrence extracted removed
      attachment accepted)
    pre definitionEnv

/--
Expose the three compiler products owned by the concrete splice site.  This is
the proof boundary used by the semantic bridge: subsequent reasoning can use
the exact wire/node/child allocation theorems without reopening frame
generation.
-/
private theorem site_compilation_components
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    ∃ (childFuel : Nat)
      (nodes :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs)
      (children :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs),
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          (attachment.diagram.nodesAt
            (attachment.hostRegion removed.site)) =
        some nodes ∧
      ConcreteElaboration.compileChildrenWith? definitions attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram childFuel)
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          (attachment.diagram.childrenOf
            (attachment.hostRegion removed.site)) =
        some children ∧
      compiled.factor.frame.siteBody =
        ConcreteElaboration.finishRegion attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          (.mk (nodes.append children)) := by
  obtain ⟨siteFuel, siteCompiled⟩ := compiled.site_compiles
  cases siteFuel with
  | zero =>
      simp [ConcreteElaboration.compileRegion?] at siteCompiled
  | succ childFuel =>
      simp only [ConcreteElaboration.compileRegion?] at siteCompiled
      cases nodesEquation :
          ConcreteElaboration.compileNodes? definitions attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site))
            (attachment.diagram.nodesAt
              (attachment.hostRegion removed.site)) with
      | none =>
          simp [nodesEquation] at siteCompiled
      | some nodes =>
          cases childrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions
                attachment.diagram
                (ConcreteElaboration.compileRegion? definitions
                  attachment.diagram childFuel)
                (compiled.factor.frame.visible.extend
                  (attachment.hostRegion removed.site))
                (attachment.diagram.childrenOf
                  (attachment.hostRegion removed.site)) with
          | none =>
              simp [nodesEquation, childrenEquation] at siteCompiled
          | some children =>
              refine ⟨childFuel, nodes, children,
                rfl, childrenEquation, ?_⟩
              exact (Option.some.inj
                (by simpa [nodesEquation, childrenEquation] using
                  siteCompiled)).symm

/--
The concrete site body denotes exactly when its freshly allocated local wires
can be valued so that the compiled node/child conjunction denotes.  This is the
fresh-binder extrusion half of the concrete-to-intrinsic bridge.
-/
private theorem siteBody_denote_iff_compiled_components
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.factor.frame.visible.sigs) :
    ∃ (childFuel : Nat)
      (nodes :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs)
      (children :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs),
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          (attachment.diagram.nodesAt
            (attachment.hostRegion removed.site)) =
        some nodes ∧
      ConcreteElaboration.compileChildrenWith? definitions attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram childFuel)
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          (attachment.diagram.childrenOf
            (attachment.hostRegion removed.site)) =
        some children ∧
      (denoteRegion pre definitionEnv env
          compiled.factor.frame.siteBody ↔
        ∃ values : ConcreteElaboration.WireValues pre
            ((attachment.diagram.wiresAt
              (attachment.hostRegion removed.site)).map
                fun wire => (attachment.diagram.wires wire).sig),
          denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site) values env)
            (.mk (nodes.append children))) := by
  obtain ⟨childFuel, nodes, children, nodesCompiled,
      childrenCompiled, bodyEquality⟩ :=
    site_compilation_components compiled
  refine ⟨childFuel, nodes, children, nodesCompiled,
    childrenCompiled, ?_⟩
  rw [bodyEquality,
    ConcreteElaboration.denote_finishRegion]

/--
The site compiler sees precisely the copied fragment root content followed by
the canonical concrete identity nodes, and precisely the copied fragment root
children.  This rules out host residue at the semantic hole.
-/
private theorem siteBody_denote_iff_split_components
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.factor.frame.visible.sigs) :
    ∃ (childFuel : Nat)
      (nodes :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs)
      (children :
        ItemSeq definitions
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs),
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          ((fragment.val.diagram.nodesAt
              fragment.val.diagram.root).map
              attachment.fragmentNode ++
            (Data.Finite.allFin
              attachment.identityRequests.length).map
              attachment.identityNode) =
        some nodes ∧
      ConcreteElaboration.compileChildrenWith? definitions attachment.diagram
          (ConcreteElaboration.compileRegion? definitions
            attachment.diagram childFuel)
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          ((fragment.val.diagram.childrenOf
              fragment.val.diagram.root).map
              attachment.fragmentRegion) =
        some children ∧
      (denoteRegion pre definitionEnv env
          compiled.factor.frame.siteBody ↔
        ∃ values : ConcreteElaboration.WireValues pre
            ((attachment.diagram.wiresAt
              (attachment.hostRegion removed.site)).map
                fun wire => (attachment.diagram.wires wire).sig),
          denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironment attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site) values env)
            (.mk (nodes.append children))) := by
  obtain ⟨childFuel, nodes, children, nodesCompiled,
      childrenCompiled, semanticCharacterization⟩ :=
    siteBody_denote_iff_compiled_components compiled pre definitionEnv env
  rw [candidate_nodesAt_site_eq attachment] at nodesCompiled
  rw [candidate_childrenOf_site_eq attachment] at childrenCompiled
  exact ⟨childFuel, nodes, children, nodesCompiled,
    childrenCompiled, semanticCharacterization⟩


/--
Canonical concrete identities are exactly the mismatching ordered boundary
positions; `eraseDups` changes multiplicity only, never membership.
-/
private theorem identityRequest_mem_iff_position
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (request : ConcreteIdentityRequest removed.complement.val) :
    request ∈ attachment.identityRequests ↔
      ∃ position : Fin fragment.val.boundary.length,
        let source := fragment.val.boundary.get position
        let representative :=
          concreteRepresentativeTarget removed fragment attachment.target
            source (List.get_mem fragment.val.boundary position)
        representative ≠ attachment.target position ∧
          request =
            { sig := (fragment.val.diagram.wires source).sig
              representative := representative
              target := attachment.target position } := by
  rw [ConcreteSpliceAttachment.identityRequests_mem_iff]
  unfold computedIdentityRequests
  simp only [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨position, _, accepted⟩
    dsimp at accepted
    split at accepted
    · contradiction
    · rename_i different
      exact ⟨position, different, Option.some.inj accepted |>.symm⟩
  · rintro ⟨position, different, rfl⟩
    refine ⟨position, Data.Finite.mem_allFin position, ?_⟩
    dsimp
    split
    · rename_i equal
      exact (different (by simpa [List.get_eq_getElem] using equal)).elim
    · rfl

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

private def restrictOuterEnvironmentFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
      Env pre
        ((localIds ++ outerIds).map
          fun wire => (diagram.wires wire).sig) →
      Env pre
        (outerIds.map fun wire => (diagram.wires wire).sig)
  | [], env => env
  | _ :: tail, env =>
      restrictOuterEnvironmentFor diagram outerIds tail
        (fun sig value => env sig (.there value))

private theorem restrictOuterEnvironmentFor_apply
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (env :
      Env pre
        ((localIds ++ outerIds).map
          fun wire => (diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var
        (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    restrictOuterEnvironmentFor diagram outerIds localIds env sig value =
      env sig (appendRightIds diagram localIds value) := by
  induction localIds with
  | nil => rfl
  | cons _ tail induction =>
      exact induction (fun sig value => env sig (.there value))

private theorem appendRightIds_origin
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {sig : Sig}
    (value :
      Var
        (rightIds.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram
        (leftIds ++ rightIds)
        (appendRightIds diagram leftIds value) =
      ConcreteElaboration.WireContext.origin diagram rightIds value := by
  induction leftIds with
  | nil => rfl
  | cons _ tail induction =>
      exact induction

private theorem extractedWireOfVar_eq_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ExtractedBoundaryCompiler.wireOfVar diagram value =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  induction ids with
  | nil => exact nomatch value
  | cons _ tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

private theorem extendOpenRootEnvironment_from_environment
    (openDiagram : OpenConcreteDiagram definitionCount)
    (env :
      Env pre
        (((ConcreteElaboration.openRootLocalWires openDiagram) ++
          ConcreteElaboration.openBoundaryWires openDiagram).map
            fun wire => (openDiagram.diagram.wires wire).sig)) :
    ConcreteElaboration.extendOpenRootEnvironment openDiagram
        (ConcreteElaboration.valuesFromEnvironmentFor
          openDiagram.diagram
          (ConcreteElaboration.openBoundaryWires openDiagram)
          (ConcreteElaboration.openRootLocalWires openDiagram) env)
        (restrictOuterEnvironmentFor openDiagram.diagram
          (ConcreteElaboration.openBoundaryWires openDiagram)
          (ConcreteElaboration.openRootLocalWires openDiagram) env) =
      env := by
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig fiber
  generalize
    ConcreteElaboration.openRootLocalWires openDiagram = localIds at env ⊢
  induction localIds with
  | nil => rfl
  | cons _ tail induction =>
      exact induction (fun sig value => env sig (.there value))

private theorem extendOpenRootEnvironment_outerValue
    (openDiagram : OpenConcreteDiagram definitionCount)
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

private def liftOuterVar
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {sig : Sig} (value : Var context.sigs sig) :
    Var (context.extend region).sigs sig :=
  appendRightIds diagram (diagram.wiresAt region) value

private theorem liftOuterVar_origin
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {sig : Sig} (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram
        (context.extend region).ids
        (liftOuterVar diagram context region value) =
      ConcreteElaboration.WireContext.origin diagram context.ids value := by
  unfold liftOuterVar ConcreteElaboration.WireContext.extend
  induction diagram.wiresAt region with
  | nil => rfl
  | cons _ tail induction =>
      simp only [appendRightIds, List.cons_append]
      exact induction

private theorem extendEnvironment_liftOuterVar
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (values :
      ConcreteElaboration.WireValues pre
        ((diagram.wiresAt region).map
          fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig} (value : Var context.sigs sig) :
    ConcreteElaboration.extendEnvironment diagram context region values
        outerEnv sig
        (liftOuterVar diagram context region value) =
      outerEnv sig value := by
  unfold ConcreteElaboration.extendEnvironment liftOuterVar
  revert values
  generalize localIdsEquation : diagram.wiresAt region = localIds
  clear localIdsEquation
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

private def liftOuterPacked
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId) :
    PackedVar context.sigs → PackedVar (context.extend region).sigs
  | ⟨sig, value⟩ =>
      ⟨sig, liftOuterVar diagram context region value⟩

private theorem liftOuterPacked_origin
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (packed : PackedVar context.sigs) :
    ConcreteElaboration.WireContext.origin diagram
        (context.extend region).ids
        (liftOuterPacked diagram context region packed).snd =
      ConcreteElaboration.WireContext.origin diagram context.ids
        packed.snd := by
  rcases packed with ⟨sig, value⟩
  exact liftOuterVar_origin diagram context region value

private theorem origin_signature_cast
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {source target : Sig} (same : source = target)
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) source) :
    ConcreteElaboration.WireContext.origin diagram ids (same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases same
  rfl

private theorem positionPackedAt_signature
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    (compiled.positionPackedAt position).fst =
      (extracted.checked.val.diagram.wires
        (extracted.checked.val.boundary.get position)).sig := by
  rcases packedEquation :
      compiled.positionPackedAt position with ⟨positionSig, positionVar⟩
  change positionSig =
    (extracted.checked.val.diagram.wires
      (extracted.checked.val.boundary.get position)).sig
  have origin := compiled.positionPackedAt_origin position
  rw [packedEquation] at origin
  change
    ConcreteElaboration.WireContext.origin attachment.diagram
        compiled.factor.frame.visible.ids positionVar =
      attachment.hostWire (attachment.target position) at origin
  have originSignature :=
    ConcreteElaboration.WireContext.origin_signature
      attachment.diagram compiled.factor.frame.visible.ids positionVar
  rw [origin, ConcreteSpliceAttachment.diagram_wire_hostWire] at originSignature
  exact originSignature.symm.trans (attachment.signature position)

private def sitePositionVar
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    Var
      (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site)).sigs
      (extracted.checked.val.diagram.wires
        (extracted.checked.val.boundary.get position)).sig :=
  let packed :=
    liftOuterPacked attachment.diagram compiled.factor.frame.visible
      (attachment.hostRegion removed.site)
      (compiled.positionPackedAt position)
  positionPackedAt_signature extracted compiled position ▸ packed.snd

private theorem sitePositionVar_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (sitePositionVar extracted compiled position) =
      attachment.hostWire (attachment.target position) := by
  unfold sitePositionVar
  change
    ConcreteElaboration.WireContext.origin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (positionPackedAt_signature extracted compiled position ▸
          (liftOuterPacked attachment.diagram
            compiled.factor.frame.visible
            (attachment.hostRegion removed.site)
            (compiled.positionPackedAt position)).snd) =
      attachment.hostWire (attachment.target position)
  calc
    _ = ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids
          (liftOuterPacked attachment.diagram
            compiled.factor.frame.visible
            (attachment.hostRegion removed.site)
            (compiled.positionPackedAt position)).snd :=
      origin_signature_cast attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (positionPackedAt_signature extracted compiled position)
        (liftOuterPacked attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          (compiled.positionPackedAt position)).snd
    _ = _ :=
      (liftOuterPacked_origin attachment.diagram
        compiled.factor.frame.visible
        (attachment.hostRegion removed.site)
        (compiled.positionPackedAt position)).trans
          (compiled.positionPackedAt_origin position)

private def representativeSiteVar
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    Var
      (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site)).sigs
      (extracted.checked.val.diagram.wires
        (extracted.checked.val.boundary.get position)).sig :=
  let source := extracted.checked.val.boundary.get position
  let member := List.get_mem extracted.checked.val.boundary position
  let representative := attachment.representativePosition source member
  let sourceEquality :
      extracted.checked.val.boundary.get representative = source :=
    DenseList.get_index extracted.checked.val.boundary source member
  congrArg
      (fun wire => (extracted.checked.val.diagram.wires wire).sig)
      sourceEquality ▸
    sitePositionVar extracted compiled representative

private theorem representativeSiteVar_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (position : Fin extracted.checked.val.boundary.length) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (representativeSiteVar extracted compiled position) =
      attachment.hostWire
        (concreteRepresentativeTarget removed extracted.checked
          attachment.target
          (extracted.checked.val.boundary.get position)
          (List.get_mem extracted.checked.val.boundary position)) := by
  unfold representativeSiteVar
  let source := extracted.checked.val.boundary.get position
  let member := List.get_mem extracted.checked.val.boundary position
  let representative := attachment.representativePosition source member
  let sourceEquality :
      extracted.checked.val.boundary.get representative = source :=
    DenseList.get_index extracted.checked.val.boundary source member
  change
    ConcreteElaboration.WireContext.origin attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (congrArg
            (fun wire => (extracted.checked.val.diagram.wires wire).sig)
            sourceEquality ▸
          sitePositionVar extracted compiled representative) =
      _
  calc
    _ = ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids
          (sitePositionVar extracted compiled representative) :=
      origin_signature_cast attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).ids
        (congrArg
          (fun wire => (extracted.checked.val.diagram.wires wire).sig)
          sourceEquality)
        (sitePositionVar extracted compiled representative)
    _ = attachment.hostWire (attachment.target representative) :=
      sitePositionVar_origin extracted compiled representative
    _ = _ := rfl

private theorem identityNode_first_incident
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (identity : Fin attachment.identityRequests.length) :
    (⟨attachment.identityNode identity, .identity 0⟩ :
        CEndpoint attachment.diagram.nodeCount) ∈
      (attachment.diagram.wires
        (attachment.hostWire
          (attachment.identityRequests.get identity).representative)).endpoints := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left, List.mem_append]
  right
  unfold ConcreteSpliceAttachment.generatedEndpoints
  apply List.mem_filterMap.mpr
  refine
    ⟨(attachment.hostWire
        (attachment.identityRequests.get identity).representative,
      ⟨attachment.identityNode identity, .identity 0⟩), ?_, ?_⟩
  · apply List.mem_append_right
    unfold ConcreteSpliceAttachment.identityEndpointOccurrences
    apply List.mem_flatMap.mpr
    exact ⟨identity, Data.Finite.mem_allFin identity, by simp⟩
  · simp [ConcreteSpliceAttachment.hostWire]

private theorem identityNode_second_incident
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (identity : Fin attachment.identityRequests.length) :
    (⟨attachment.identityNode identity, .identity 1⟩ :
        CEndpoint attachment.diagram.nodeCount) ∈
      (attachment.diagram.wires
        (attachment.hostWire
          (attachment.identityRequests.get identity).target)).endpoints := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left, List.mem_append]
  right
  unfold ConcreteSpliceAttachment.generatedEndpoints
  apply List.mem_filterMap.mpr
  refine
    ⟨(attachment.hostWire
        (attachment.identityRequests.get identity).target,
      ⟨attachment.identityNode identity, .identity 1⟩), ?_, ?_⟩
  · apply List.mem_append_right
    unfold ConcreteSpliceAttachment.identityEndpointOccurrences
    apply List.mem_flatMap.mpr
    exact ⟨identity, Data.Finite.mem_allFin identity, by simp⟩
  · simp [ConcreteSpliceAttachment.hostWire]

private theorem identityNode_singleton_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (identity : Fin attachment.identityRequests.length) :
    ∃ (first second :
        Var
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).sigs
          (attachment.identityRequests.get identity).sig),
      ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids first =
        attachment.hostWire
          (attachment.identityRequests.get identity).representative ∧
      ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids second =
        attachment.hostWire
          (attachment.identityRequests.get identity).target ∧
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          [attachment.identityNode identity] =
        some
          (.cons
            (Item.binaryIdentity
              (attachment.identityRequests.get identity).sig first second)
            .nil) := by
  have requestMember :
      attachment.identityRequests.get identity ∈
        attachment.identityRequests :=
    List.get_mem attachment.identityRequests identity
  obtain ⟨position, different, requestEquality⟩ :=
    (identityRequest_mem_iff_position attachment
      (attachment.identityRequests.get identity)).mp requestMember
  let first := representativeSiteVar extracted compiled position
  let second := sitePositionVar extracted compiled position
  have firstOrigin :=
    representativeSiteVar_origin extracted compiled position
  have secondOrigin := sitePositionVar_origin extracted compiled position
  have singletonCompiled :=
    ConcreteElaboration.compileNodes?_binaryIdentity_singleton
      result.wellFormed
      (candidateSiteContext_nodup result compiled)
      first second
      (attachment.hostWire
        (concreteRepresentativeTarget removed extracted.checked
          attachment.target
          (extracted.checked.val.boundary.get position)
          (List.get_mem extracted.checked.val.boundary position)))
      (attachment.hostWire (attachment.target position))
      firstOrigin secondOrigin
      (attachment.hostRegion removed.site)
      (attachment.identityNode identity)
      (by
        rw [ConcreteSpliceAttachment.diagram_node_identityNode]
        exact congrArg
          (fun request =>
            CNode.identity (attachment.hostRegion removed.site)
              request.sig 2)
          requestEquality)
      (by
        have incident := identityNode_first_incident attachment identity
        rw [requestEquality] at incident
        exact incident)
      (by
        have incident := identityNode_second_incident attachment identity
        rw [requestEquality] at incident
        exact incident)
  rw [requestEquality]
  exact ⟨first, second, firstOrigin, secondOrigin, singletonCompiled⟩

private theorem WireContext.origin_mem
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => exact nomatch value
  | cons _ tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there rest =>
          exact List.mem_cons_of_mem _ (induction rest)

private theorem WireContext.origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig} :
    Function.Injective
      (ConcreteElaboration.WireContext.origin diagram ids
        (sig := sig)) := by
  intro left right same
  induction ids with
  | nil => exact nomatch left
  | cons head tail induction =>
      have nodupParts := List.pairwise_cons.mp nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there rest =>
              change head =
                ConcreteElaboration.WireContext.origin diagram tail rest
                at same
              have member :=
                WireContext.origin_mem diagram tail rest
              exact False.elim ((nodupParts.1 _ member) same)
      | there leftRest =>
          cases right with
          | here =>
              change
                ConcreteElaboration.WireContext.origin diagram tail leftRest =
                  head at same
              have member :=
                WireContext.origin_mem diagram tail leftRest
              exact False.elim ((nodupParts.1 _ member) same.symm)
          | there rightRest =>
              exact congrArg Var.there
                (induction nodupParts.2 same)

private def packedOrigin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) :
    PackedVar
        (ids.map fun wire => (diagram.wires wire).sig) →
      diagram.WireId
  | ⟨_, value⟩ =>
      ConcreteElaboration.WireContext.origin diagram ids value

private theorem packedOrigin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup) :
    Function.Injective (packedOrigin diagram ids) := by
  intro left right same
  rcases left with ⟨leftSig, leftVar⟩
  rcases right with ⟨rightSig, rightVar⟩
  have leftSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids leftVar
  have rightSignature :=
    ConcreteElaboration.WireContext.origin_signature
      diagram ids rightVar
  change
    ConcreteElaboration.WireContext.origin diagram ids leftVar =
      ConcreteElaboration.WireContext.origin diagram ids rightVar at same
  rw [same] at leftSignature
  have signatureEquality : leftSig = rightSig :=
    leftSignature.symm.trans rightSignature
  cases signatureEquality
  have variableEquality :=
    WireContext.origin_injective diagram ids nodup same
  cases variableEquality
  rfl

private def evaluatePacked
    {pre : PreModel}
    (env : Env pre sigs) :
    PackedVar sigs → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private theorem Vars.denote_eq_of_entries
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (entriesEqual :
      ∀ position : Fin args.length,
        evaluatePacked left
            (sources.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩) =
          evaluatePacked right
            (targets.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩)) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil =>
      cases targets
      rfl
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          have headEqual :=
            entriesEqual ⟨0, by simp⟩
          simp only [Vars.entries, List.get_eq_getElem,
            List.getElem_cons_zero] at headEqual
          have tailEntriesEqual :
              ∀ position : Fin tailArgs.length,
                evaluatePacked left
                    (sourceTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) =
                  evaluatePacked right
                    (targetTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) := by
            intro position
            have atSuccessor :=
              entriesEqual
                ⟨position.val + 1, by
                  simp only [List.length_cons]
                  omega⟩
            simpa only [Vars.entries, List.get_eq_getElem,
              List.getElem_cons_succ] using atSuccessor
          have tailEqual :=
            induction targetTail tailEntriesEqual
          simp only [Vars.denote_cons]
          apply Prod.ext
          · exact eq_of_heq (Sigma.mk.inj headEqual).2
          · exact tailEqual

private theorem Vars.entries_eq_of_denote
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (valuesEqual :
      Vars.denote left sources = Vars.denote right targets)
    (position : Fin args.length) :
    evaluatePacked left
        (sources.entries.get
          ⟨position.val, by
            simpa only [ExtractedBoundaryCompiler.entries_length]
              using position.isLt⟩) =
      evaluatePacked right
        (targets.entries.get
          ⟨position.val, by
            simpa only [ExtractedBoundaryCompiler.entries_length]
              using position.isLt⟩) := by
  induction sources with
  | nil => exact nomatch position
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          rcases position with ⟨position, bound⟩
          cases position with
          | zero =>
              simp only [Vars.entries, List.get_eq_getElem,
                List.getElem_cons_zero]
              exact congrArg
                (fun value => (⟨sig, value⟩ : Sigma pre.Domain))
                (congrArg Prod.fst valuesEqual)
          | succ position =>
              have tailEqual :=
                induction targetTail (congrArg Prod.snd valuesEqual)
                  ⟨position, by
                    simp only [List.length_cons] at bound
                    omega⟩
              simpa only [Vars.entries, List.get_eq_getElem,
                List.getElem_cons_succ] using tailEqual

private def identityPositionHolds
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (env :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (position : Fin extracted.checked.val.boundary.length) : Prop :=
  env _ (representativeSiteVar extracted compiled position) =
    env _ (sitePositionVar extracted compiled position)

private def identityRequestHolds
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (env :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (request : ConcreteIdentityRequest removed.complement.val) : Prop :=
  ∀ position : Fin extracted.checked.val.boundary.length,
    let source := extracted.checked.val.boundary.get position
    let representative :=
      concreteRepresentativeTarget removed extracted.checked
        attachment.target source
        (List.get_mem extracted.checked.val.boundary position)
    representative ≠ attachment.target position →
      request =
        { sig := (extracted.checked.val.diagram.wires source).sig
          representative := representative
          target := attachment.target position } →
      identityPositionHolds extracted compiled pre env position

private theorem identityValues_eq_iff_requestHolds
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (env :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (identity : Fin attachment.identityRequests.length)
    (first second :
      Var
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs
        (attachment.identityRequests.get identity).sig)
    (firstOrigin :
      ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids first =
        attachment.hostWire
          (attachment.identityRequests.get identity).representative)
    (secondOrigin :
      ConcreteElaboration.WireContext.origin attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids second =
        attachment.hostWire
          (attachment.identityRequests.get identity).target) :
    env _ first = env _ second ↔
      identityRequestHolds extracted compiled pre env
        (attachment.identityRequests.get identity) := by
  let context :=
    compiled.factor.frame.visible.extend
      (attachment.hostRegion removed.site)
  constructor
  · intro valuesEqual position
    dsimp [identityRequestHolds]
    intro different requestEquality
    unfold identityPositionHolds
    have representativeEquality :=
      congrArg ConcreteIdentityRequest.representative requestEquality
    have targetEquality :=
      congrArg ConcreteIdentityRequest.target requestEquality
    have injective :=
      packedOrigin_injective attachment.diagram context.ids
        (candidateSiteContext_nodup result compiled)
    have firstPackedEquality :
        (⟨(attachment.identityRequests.get identity).sig, first⟩ :
            PackedVar context.sigs) =
          ⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get position)).sig,
            representativeSiteVar extracted compiled position⟩ := by
      apply injective
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids first =
          ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids
            (representativeSiteVar extracted compiled position)
      exact firstOrigin.trans
        ((congrArg attachment.hostWire representativeEquality).trans
          (representativeSiteVar_origin extracted compiled position).symm)
    have secondPackedEquality :
        (⟨(attachment.identityRequests.get identity).sig, second⟩ :
            PackedVar context.sigs) =
          ⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get position)).sig,
            sitePositionVar extracted compiled position⟩ := by
      apply injective
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids second =
          ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids (sitePositionVar extracted compiled position)
      exact secondOrigin.trans
        ((congrArg attachment.hostWire targetEquality).trans
          (sitePositionVar_origin extracted compiled position).symm)
    have evaluatedEquality :
        evaluatePacked env
            (⟨(attachment.identityRequests.get identity).sig, first⟩ :
              PackedVar context.sigs) =
          evaluatePacked env
            (⟨(attachment.identityRequests.get identity).sig, second⟩ :
              PackedVar context.sigs) :=
      congrArg
        (fun value =>
          (⟨(attachment.identityRequests.get identity).sig, value⟩ :
            Sigma pre.Domain))
        valuesEqual
    rw [firstPackedEquality, secondPackedEquality] at evaluatedEquality
    exact eq_of_heq (Sigma.mk.inj evaluatedEquality).2
  · intro requestHolds
    have requestMember :
        attachment.identityRequests.get identity ∈
          attachment.identityRequests :=
      List.get_mem attachment.identityRequests identity
    obtain ⟨position, different, requestEquality⟩ :=
      (identityRequest_mem_iff_position attachment
        (attachment.identityRequests.get identity)).mp requestMember
    have positionHolds :=
      requestHolds position different requestEquality
    have representativeEquality :=
      congrArg ConcreteIdentityRequest.representative requestEquality
    have targetEquality :=
      congrArg ConcreteIdentityRequest.target requestEquality
    have injective :=
      packedOrigin_injective attachment.diagram context.ids
        (candidateSiteContext_nodup result compiled)
    have firstPackedEquality :
        (⟨(attachment.identityRequests.get identity).sig, first⟩ :
            PackedVar context.sigs) =
          ⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get position)).sig,
            representativeSiteVar extracted compiled position⟩ := by
      apply injective
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids first =
          ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids
            (representativeSiteVar extracted compiled position)
      exact firstOrigin.trans
        ((congrArg attachment.hostWire representativeEquality).trans
          (representativeSiteVar_origin extracted compiled position).symm)
    have secondPackedEquality :
        (⟨(attachment.identityRequests.get identity).sig, second⟩ :
            PackedVar context.sigs) =
          ⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get position)).sig,
            sitePositionVar extracted compiled position⟩ := by
      apply injective
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids second =
          ConcreteElaboration.WireContext.origin attachment.diagram
            context.ids (sitePositionVar extracted compiled position)
      exact secondOrigin.trans
        ((congrArg attachment.hostWire targetEquality).trans
          (sitePositionVar_origin extracted compiled position).symm)
    have evaluatedEquality :
        evaluatePacked env
            (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get position)).sig,
              representativeSiteVar extracted compiled position⟩ :
              PackedVar context.sigs) =
          evaluatePacked env
            (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get position)).sig,
              sitePositionVar extracted compiled position⟩ :
              PackedVar context.sigs) :=
      congrArg
        (fun value =>
          (⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get position)).sig,
            value⟩ : Sigma pre.Domain))
        positionHolds
    rw [← firstPackedEquality, ← secondPackedEquality] at evaluatedEquality
    exact eq_of_heq (Sigma.mk.inj evaluatedEquality).2

private theorem compileNodes?_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes?_append
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (left right : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (left ++ right) =
      (do
        let leftItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context left
        let rightItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context right
        pure (leftItems.append rightItems)) := by
  induction left with
  | nil =>
      simp [ConcreteElaboration.compileNodes?, ItemSeq.append]
  | cons head tail induction =>
      simp only [List.cons_append,
        ConcreteElaboration.compileNodes?]
      rw [induction]
      simp [Option.bind_assoc, ItemSeq.append]

private theorem identityNodes_denote_iff_requestHolds
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (indices : List (Fin attachment.identityRequests.length))
    (items :
      ItemSeq definitions
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (itemsCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          (indices.map attachment.identityNode) =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ identity, identity ∈ indices →
        identityRequestHolds extracted compiled pre env
          (attachment.identityRequests.get identity) := by
  induction indices generalizing items with
  | nil =>
      simp [ConcreteElaboration.compileNodes?] at itemsCompiled
      subst items
      simp
  | cons identity tail induction =>
      obtain ⟨first, second, firstOrigin, secondOrigin,
          headCompiled⟩ :=
        identityNode_singleton_compiles extracted result compiled identity
      rw [List.map_cons, compileNodes?_cons_eq_singleton_bind,
        headCompiled] at itemsCompiled
      cases tailCompiled :
          ConcreteElaboration.compileNodes? definitions attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site))
            (tail.map attachment.identityNode) with
      | none =>
          simp [tailCompiled] at itemsCompiled
      | some tailItems =>
          have itemsEquality :
              (ItemSeq.cons
                  (Item.binaryIdentity
                    (attachment.identityRequests.get identity).sig
                    first second)
                  ItemSeq.nil).append tailItems =
                items :=
            Option.some.inj (by
              simpa [tailCompiled] using itemsCompiled)
          subst items
          simp only [ItemSeq.append, denoteItemSeq_cons,
            binary_identity]
          rw [
            identityValues_eq_iff_requestHolds extracted result compiled
              pre env identity first second firstOrigin secondOrigin,
            induction tailItems tailCompiled]
          simp

private theorem identityNodes_denote_iff_positions
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env :
      Env pre
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (items :
      ItemSeq definitions
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site)).sigs)
    (itemsCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site))
          ((Data.Finite.allFin
            attachment.identityRequests.length).map
              attachment.identityNode) =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ position : Fin extracted.checked.val.boundary.length,
        let source := extracted.checked.val.boundary.get position
        let representative :=
          concreteRepresentativeTarget removed extracted.checked
            attachment.target source
            (List.get_mem extracted.checked.val.boundary position)
        representative ≠ attachment.target position →
          identityPositionHolds extracted compiled pre env position := by
  have allRequests :=
    identityNodes_denote_iff_requestHolds extracted result compiled pre
      definitionEnv env
      (Data.Finite.allFin attachment.identityRequests.length)
      items itemsCompiled
  constructor
  · intro itemsDenote position
    dsimp
    intro different
    let source := extracted.checked.val.boundary.get position
    let representative :=
      concreteRepresentativeTarget removed extracted.checked
        attachment.target source
        (List.get_mem extracted.checked.val.boundary position)
    let request : ConcreteIdentityRequest removed.complement.val :=
      { sig := (extracted.checked.val.diagram.wires source).sig
        representative := representative
        target := attachment.target position }
    have requestMember : request ∈ attachment.identityRequests :=
      (identityRequest_mem_iff_position attachment request).mpr
        ⟨position, different, rfl⟩
    let identity :=
      DenseList.index attachment.identityRequests request requestMember
    have requestAt :
        attachment.identityRequests.get identity = request :=
      DenseList.get_index attachment.identityRequests request requestMember
    have requestHolds :=
      allRequests.mp itemsDenote identity
        (Data.Finite.mem_allFin identity)
    rw [requestAt] at requestHolds
    exact requestHolds position different rfl
  · intro positionsHold
    apply allRequests.mpr
    intro identity _
    intro position
    dsimp
    intro different _
    exact positionsHold position different

private theorem siteBody_denote_iff_intrinsic
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (compiled : SpliceCompilation attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.factor.frame.visible.sigs) :
    denoteRegion pre definitionEnv env compiled.factor.frame.siteBody ↔
      denoteRegion pre definitionEnv env
        (intrinsicSplice extracted.openDiagram
          (compiled.intrinsicAttachment extracted)) := by
  obtain ⟨childFuel, targetNodes, targetChildren,
      targetNodesCompiled, targetChildrenCompiled, siteSemantics⟩ :=
    siteBody_denote_iff_split_components compiled pre definitionEnv env
  rw [siteSemantics]
  rw [denote_intrinsicSplice pre definitionEnv env
    extracted.openDiagram (compiled.intrinsicAttachment extracted)]
  have sourceComponents :
      ∃ (sourceNodes sourceChildren :
          ItemSeq definitions
            (⟨ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val⟩ :
              ConcreteElaboration.WireContext
                extracted.checked.val.diagram).sigs),
        ConcreteElaboration.compileNodes? definitions
            extracted.checked.val.diagram
            (⟨ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val⟩ :
              ConcreteElaboration.WireContext
                extracted.checked.val.diagram)
            (extracted.checked.val.diagram.nodesAt
              extracted.checked.val.diagram.root) =
          some sourceNodes ∧
        ConcreteElaboration.compileChildrenWith? definitions
            extracted.checked.val.diagram
            (ConcreteElaboration.compileRegion? definitions
              extracted.checked.val.diagram
              extracted.checked.val.diagram.regionCount)
            (⟨ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val⟩ :
              ConcreteElaboration.WireContext
                extracted.checked.val.diagram)
            (extracted.checked.val.diagram.childrenOf
              extracted.checked.val.diagram.root) =
          some sourceChildren := by
    have bodyCompiled := extracted.body_compiles
    unfold ConcreteElaboration.compileOpenRoot? at bodyCompiled
    obtain ⟨sourceNodes, sourceNodesCompiled, remainderCompiled⟩ :=
      Option.bind_eq_some_iff.mp bodyCompiled
    obtain ⟨sourceChildren, sourceChildrenCompiled, _⟩ :=
      Option.bind_eq_some_iff.mp remainderCompiled
    exact
      ⟨sourceNodes, sourceChildren,
        sourceNodesCompiled, sourceChildrenCompiled⟩
  obtain ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled⟩ := sourceComponents
  obtain ⟨copiedNodes, copiedNodesCompiled, copiedNodesEquality⟩ :=
    copiedRootNodes_natural extracted result compiled
      (extracted.checked.val.diagram.nodesAt
        extracted.checked.val.diagram.root)
      sourceNodesCompiled
  have targetNodesSplit :=
    compileNodes?_append definitions attachment.diagram
      (compiled.factor.frame.visible.extend
        (attachment.hostRegion removed.site))
      ((extracted.checked.val.diagram.nodesAt
        extracted.checked.val.diagram.root).map attachment.fragmentNode)
      ((Data.Finite.allFin
        attachment.identityRequests.length).map attachment.identityNode)
  have targetNodesCombined :=
    targetNodesSplit.symm.trans targetNodesCompiled
  rw [copiedNodesCompiled] at targetNodesCombined
  change
    (ConcreteElaboration.compileNodes? definitions attachment.diagram
        (compiled.factor.frame.visible.extend
          (attachment.hostRegion removed.site))
        ((Data.Finite.allFin
          attachment.identityRequests.length).map
            attachment.identityNode)).bind
      (fun identityItems =>
        some (copiedNodes.append identityItems)) =
      some targetNodes at targetNodesCombined
  obtain ⟨identityItems, identityItemsCompiled, combinedCompiled⟩ :=
    Option.bind_eq_some_iff.mp targetNodesCombined
  have targetNodesEquality :
      copiedNodes.append identityItems = targetNodes :=
    Option.some.inj combinedCompiled
  rw [← targetNodesEquality]
  constructor
  · rintro ⟨targetValues, targetCoreDenotes⟩
    let targetEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        compiled.factor.frame.visible
        (attachment.hostRegion removed.site) targetValues env
    change
      denoteItemSeq pre definitionEnv targetEnv
        ((copiedNodes.append identityItems).append targetChildren)
        at targetCoreDenotes
    rw [denoteItemSeq_append, denoteItemSeq_append] at targetCoreDenotes
    rcases targetCoreDenotes with
      ⟨⟨copiedNodesDenote, identityItemsDenote⟩,
        targetChildrenDenote⟩
    have sourceNodesDenote :
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (rootFragmentRenaming extracted compiled))
          sourceNodes := by
      rw [copiedNodesEquality,
        denoteItemSeq_renameWires] at copiedNodesDenote
      exact copiedNodesDenote
    have sourceChildrenDenote :
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (rootFragmentRenaming extracted compiled))
          sourceChildren :=
      (fragmentChildren_denotation_natural extracted result compiled
        childFuel sourceChildrenCompiled targetChildrenCompiled
        pre definitionEnv targetEnv).mp targetChildrenDenote
    have identityPositions :=
      (identityNodes_denote_iff_positions extracted result compiled pre
        definitionEnv targetEnv identityItems
        identityItemsCompiled).mp identityItemsDenote
    unfold denoteOpen
    let sourceEnv :=
      Env.comp targetEnv (rootFragmentRenaming extracted compiled)
    let classEnv : Env pre extracted.openDiagram.classes :=
      restrictOuterEnvironmentFor extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        (ConcreteElaboration.openRootLocalWires extracted.checked.val)
        sourceEnv
    let sourceValues :=
      ConcreteElaboration.valuesFromEnvironmentFor
        extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        (ConcreteElaboration.openRootLocalWires extracted.checked.val)
        sourceEnv
    have sourceEnvironmentEquality :
        ConcreteElaboration.extendOpenRootEnvironment
            extracted.checked.val sourceValues classEnv =
          sourceEnv := by
      exact
        extendOpenRootEnvironment_from_environment
          extracted.checked.val sourceEnv
    have sourceBodyDenotes :
        denoteRegion pre definitionEnv classEnv extracted.body := by
      apply
        (ConcreteElaboration.denote_compileOpenRoot_components
          definitions extracted.checked.val extracted.body
          extracted.body_compiles pre definitionEnv classEnv).mpr
      refine
        ⟨sourceNodes, sourceChildren, sourceValues,
          sourceNodesCompiled, sourceChildrenCompiled, ?_⟩
      rw [sourceEnvironmentEquality]
      change
        denoteItemSeq pre definitionEnv sourceEnv
          (sourceNodes.append sourceChildren)
      rw [denoteItemSeq_append]
      exact ⟨sourceNodesDenote, sourceChildrenDenote⟩
    refine ⟨classEnv, ?_, sourceBodyDenotes⟩
    apply Vars.denote_eq_of_entries
    intro position
    let concretePosition :
        Fin extracted.checked.val.boundary.length :=
      ⟨position.val, by
        simpa only [checkedBoundarySigs, List.length_map]
          using position.isLt⟩
    change
      evaluatePacked classEnv
          (extracted.boundaryPackedAt concretePosition) =
        evaluatePacked env
          (compiled.positionPackedAt concretePosition)
    rcases boundaryPackedEquation :
        extracted.boundaryPackedAt concretePosition with
      ⟨boundarySig, boundaryVar⟩
    let sourceBoundaryVar :=
      appendRightIds extracted.checked.val.diagram
        (ConcreteElaboration.openRootLocalWires extracted.checked.val)
        boundaryVar
    have boundaryOrigin :=
      extracted.boundaryPackedAt_origin concretePosition
    rw [boundaryPackedEquation] at boundaryOrigin
    change
      ExtractedBoundaryCompiler.wireOfVar
          extracted.checked.val.diagram boundaryVar =
        extracted.checked.val.boundary.get concretePosition
      at boundaryOrigin
    have boundaryOrigin' :
        ConcreteElaboration.WireContext.origin
            extracted.checked.val.diagram
            (ConcreteElaboration.openBoundaryWires
              extracted.checked.val)
            boundaryVar =
          extracted.checked.val.boundary.get concretePosition :=
      (extractedWireOfVar_eq_origin extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires
          extracted.checked.val)
        boundaryVar).symm.trans boundaryOrigin
    have sourceBoundaryOrigin :
        ConcreteElaboration.WireContext.origin
            extracted.checked.val.diagram
            (ConcreteElaboration.openRootLocalWires
                extracted.checked.val ++
              ConcreteElaboration.openBoundaryWires
                extracted.checked.val)
            sourceBoundaryVar =
          extracted.checked.val.boundary.get concretePosition := by
      exact
        (appendRightIds_origin extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires extracted.checked.val)
          (ConcreteElaboration.openBoundaryWires extracted.checked.val)
          boundaryVar).trans boundaryOrigin'
    have representativePackedEquality :
        (⟨boundarySig,
          rootFragmentRenaming extracted compiled sourceBoundaryVar⟩ :
            PackedVar
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).sigs) =
          ⟨(extracted.checked.val.diagram.wires
              (extracted.checked.val.boundary.get concretePosition)).sig,
            representativeSiteVar extracted compiled concretePosition⟩ := by
      apply
        packedOrigin_injective attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids
          (candidateSiteContext_nodup result compiled)
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (rootFragmentRenaming extracted compiled sourceBoundaryVar) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (representativeSiteVar extracted compiled concretePosition)
      rw [rootFragmentRenaming_contextAction,
        sourceBoundaryOrigin,
        representativeSiteVar_origin]
      simp [ConcreteSpliceAttachment.fragmentWire,
        ConcreteSpliceAttachment.representativeTarget,
        concreteRepresentativeTarget,
        ConcreteSpliceAttachment.representativePosition]
      rfl
    have positionPackedEquality :
        liftOuterPacked attachment.diagram
            compiled.factor.frame.visible
            (attachment.hostRegion removed.site)
            (compiled.positionPackedAt concretePosition) =
          (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              sitePositionVar extracted compiled concretePosition⟩ :
            PackedVar
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).sigs) := by
      apply
        packedOrigin_injective attachment.diagram
          (compiled.factor.frame.visible.extend
            (attachment.hostRegion removed.site)).ids
          (candidateSiteContext_nodup result compiled)
      change
        ConcreteElaboration.WireContext.origin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (liftOuterPacked attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              (compiled.positionPackedAt concretePosition)).snd =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (sitePositionVar extracted compiled concretePosition)
      exact
        (liftOuterPacked_origin attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          (compiled.positionPackedAt concretePosition)).trans
          ((compiled.positionPackedAt_origin concretePosition).trans
            (sitePositionVar_origin extracted compiled
              concretePosition).symm)
    have leftValue :
        evaluatePacked classEnv
            (extracted.boundaryPackedAt concretePosition) =
          evaluatePacked targetEnv
            (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              representativeSiteVar extracted compiled concretePosition⟩ :
              PackedVar
                (compiled.factor.frame.visible.extend
                  (attachment.hostRegion removed.site)).sigs) := by
      rw [boundaryPackedEquation]
      change
        (⟨boundarySig, classEnv boundarySig boundaryVar⟩ :
            Sigma pre.Domain) =
          _
      unfold classEnv sourceEnv
      rw [restrictOuterEnvironmentFor_apply]
      exact congrArg (evaluatePacked targetEnv)
        representativePackedEquality
    have rightValue :
        evaluatePacked targetEnv
            (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              sitePositionVar extracted compiled concretePosition⟩ :
              PackedVar
                (compiled.factor.frame.visible.extend
                  (attachment.hostRegion removed.site)).sigs) =
          evaluatePacked env
            (compiled.positionPackedAt concretePosition) := by
      rw [← positionPackedEquality]
      rcases compiled.positionPackedAt concretePosition with
        ⟨positionSig, positionVar⟩
      exact congrArg
        (fun value => (⟨positionSig, value⟩ : Sigma pre.Domain))
        (extendEnvironment_liftOuterVar attachment.diagram
          compiled.factor.frame.visible
          (attachment.hostRegion removed.site)
          pre targetValues env positionVar)
    by_cases different :
        concreteRepresentativeTarget removed extracted.checked
            attachment.target
            (extracted.checked.val.boundary.get concretePosition)
            (List.get_mem extracted.checked.val.boundary concretePosition) ≠
          attachment.target concretePosition
    · have sameValue :=
        identityPositions concretePosition different
      rw [← boundaryPackedEquation]
      exact leftValue.trans
        ((congrArg
          (fun value =>
            (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              value⟩ : Sigma pre.Domain))
          sameValue).trans rightValue)
    · have sameTarget := Classical.not_not.mp different
      have sitePackedSame :
          (⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              representativeSiteVar extracted compiled concretePosition⟩ :
            PackedVar
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).sigs) =
            ⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get concretePosition)).sig,
              sitePositionVar extracted compiled concretePosition⟩ := by
        apply
          packedOrigin_injective attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (candidateSiteContext_nodup result compiled)
        change
          ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (representativeSiteVar extracted compiled
                concretePosition) =
            ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (sitePositionVar extracted compiled concretePosition)
        rw [representativeSiteVar_origin,
          sitePositionVar_origin, sameTarget]
      rw [← boundaryPackedEquation]
      exact leftValue.trans
        ((congrArg (evaluatePacked targetEnv) sitePackedSame).trans
          rightValue)
  · rintro ⟨classEnv, boundaryValues, sourceBodyDenotes⟩
    have canonicalClassEnv :
        classEnv =
          Env.comp env
            (compiled.intrinsicAttachment extracted).classMap := by
      funext sig fiber
      exact Vars.value_eq_of_paired
        ((compiled.intrinsicAttachment extracted).representative_position
          fiber)
        classEnv env boundaryValues
    subst classEnv
    have sourceComponentsDenote :=
      (ConcreteElaboration.denote_compileOpenRoot_components
        definitions extracted.checked.val extracted.body
        extracted.body_compiles pre definitionEnv
        (Env.comp env
          (compiled.intrinsicAttachment extracted).classMap)).mp
        sourceBodyDenotes
    obtain ⟨otherSourceNodes, otherSourceChildren, sourceValues,
        otherSourceNodesCompiled, otherSourceChildrenCompiled,
        sourceCoreDenotes⟩ := sourceComponentsDenote
    have sourceNodesEquality : otherSourceNodes = sourceNodes :=
      Option.some.inj
        (otherSourceNodesCompiled.symm.trans sourceNodesCompiled)
    have sourceChildrenEquality : otherSourceChildren = sourceChildren :=
      Option.some.inj
        (otherSourceChildrenCompiled.symm.trans sourceChildrenCompiled)
    subst otherSourceNodes
    subst otherSourceChildren
    have siteLocalSigsEquality :
        (attachment.diagram.wiresAt
            (attachment.hostRegion removed.site)).map
              (fun wire => (attachment.diagram.wires wire).sig) =
          (ConcreteElaboration.openRootLocalWires
            extracted.checked.val).map
              (fun wire =>
                (extracted.checked.val.diagram.wires wire).sig) := by
      rw [candidate_wiresAt_site_eq]
      calc
        _ = List.map
              (fun wire =>
                (attachment.diagram.wires
                  (attachment.fragmentWire wire)).sig)
              (ConcreteElaboration.openRootLocalWires
                extracted.checked.val) := by
            exact List.map_map
        _ = _ :=
          List.map_congr_left fun wire _ =>
            fragmentWire_signature attachment wire
    let targetValues :
        ConcreteElaboration.WireValues pre
          ((attachment.diagram.wiresAt
            (attachment.hostRegion removed.site)).map
              fun wire => (attachment.diagram.wires wire).sig) :=
      siteLocalSigsEquality.symm ▸ sourceValues
    let targetEnv :=
      ConcreteElaboration.extendEnvironment attachment.diagram
        compiled.factor.frame.visible
        (attachment.hostRegion removed.site) targetValues env
    have environmentsEqual :
        Env.comp targetEnv (rootFragmentRenaming extracted compiled) =
          ConcreteElaboration.extendOpenRootEnvironment
            extracted.checked.val sourceValues
            (Env.comp env
              (compiled.intrinsicAttachment extracted).classMap) := by
      exact
        rootFragmentRenaming_extendEnvironment extracted compiled pre
          sourceValues env siteLocalSigsEquality
    change
      denoteItemSeq pre definitionEnv
        (ConcreteElaboration.extendOpenRootEnvironment
          extracted.checked.val sourceValues
          (Env.comp env
            (compiled.intrinsicAttachment extracted).classMap))
        (sourceNodes.append sourceChildren) at sourceCoreDenotes
    rcases
        (denoteItemSeq_append pre definitionEnv
          (ConcreteElaboration.extendOpenRootEnvironment
            extracted.checked.val sourceValues
            (Env.comp env
              (compiled.intrinsicAttachment extracted).classMap))
          sourceNodes sourceChildren).mp sourceCoreDenotes with
      ⟨sourceNodesDenote, sourceChildrenDenote⟩
    have copiedNodesDenote :
        denoteItemSeq pre definitionEnv targetEnv copiedNodes := by
      rw [copiedNodesEquality, denoteItemSeq_renameWires,
        environmentsEqual]
      exact sourceNodesDenote
    have targetChildrenDenote :
        denoteItemSeq pre definitionEnv targetEnv targetChildren := by
      apply
        (fragmentChildren_denotation_natural extracted result compiled
          childFuel sourceChildrenCompiled targetChildrenCompiled
          pre definitionEnv targetEnv).mpr
      rw [environmentsEqual]
      exact sourceChildrenDenote
    have identityItemsDenote :
        denoteItemSeq pre definitionEnv targetEnv identityItems := by
      apply
        (identityNodes_denote_iff_positions extracted result compiled pre
          definitionEnv targetEnv identityItems
          identityItemsCompiled).mpr
      intro position
      dsimp
      intro _
      unfold identityPositionHolds
      let tuplePosition :
          Fin (checkedBoundarySigs extracted.checked).length :=
        ⟨position.val, by
          simpa only [checkedBoundarySigs, List.length_map]
            using position.isLt⟩
      have boundaryAtPosition :=
        Vars.entries_eq_of_denote
          (Env.comp env
            (compiled.intrinsicAttachment extracted).classMap)
          env extracted.openDiagram.boundary
          (compiled.intrinsicAttachment extracted).positions
          boundaryValues tuplePosition
      change
        evaluatePacked
            (Env.comp env
              (compiled.intrinsicAttachment extracted).classMap)
            (extracted.boundaryPackedAt position) =
          evaluatePacked env
            (compiled.positionPackedAt position)
        at boundaryAtPosition
      rcases boundaryPackedEquation :
          extracted.boundaryPackedAt position with
        ⟨boundarySig, boundaryVar⟩
      let sourceBoundaryVar :=
        appendRightIds extracted.checked.val.diagram
          (ConcreteElaboration.openRootLocalWires
            extracted.checked.val)
          boundaryVar
      have boundaryOrigin :=
        extracted.boundaryPackedAt_origin position
      rw [boundaryPackedEquation] at boundaryOrigin
      change
        ExtractedBoundaryCompiler.wireOfVar
            extracted.checked.val.diagram boundaryVar =
          extracted.checked.val.boundary.get position
        at boundaryOrigin
      have boundaryOrigin' :
          ConcreteElaboration.WireContext.origin
              extracted.checked.val.diagram
              (ConcreteElaboration.openBoundaryWires
                extracted.checked.val)
              boundaryVar =
            extracted.checked.val.boundary.get position :=
        (extractedWireOfVar_eq_origin extracted.checked.val.diagram
          (ConcreteElaboration.openBoundaryWires
            extracted.checked.val)
          boundaryVar).symm.trans boundaryOrigin
      have sourceBoundaryOrigin :
          ConcreteElaboration.WireContext.origin
              extracted.checked.val.diagram
              (ConcreteElaboration.openRootLocalWires
                  extracted.checked.val ++
                ConcreteElaboration.openBoundaryWires
                  extracted.checked.val)
              sourceBoundaryVar =
            extracted.checked.val.boundary.get position := by
        exact
          (appendRightIds_origin extracted.checked.val.diagram
            (ConcreteElaboration.openRootLocalWires
              extracted.checked.val)
            (ConcreteElaboration.openBoundaryWires
              extracted.checked.val)
            boundaryVar).trans boundaryOrigin'
      have representativePackedEquality :
          (⟨boundarySig,
            rootFragmentRenaming extracted compiled sourceBoundaryVar⟩ :
              PackedVar
                (compiled.factor.frame.visible.extend
                  (attachment.hostRegion removed.site)).sigs) =
            ⟨(extracted.checked.val.diagram.wires
                (extracted.checked.val.boundary.get position)).sig,
              representativeSiteVar extracted compiled position⟩ := by
        apply
          packedOrigin_injective attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (candidateSiteContext_nodup result compiled)
        change
          ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (rootFragmentRenaming extracted compiled
                sourceBoundaryVar) =
            ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (representativeSiteVar extracted compiled position)
        rw [rootFragmentRenaming_contextAction,
          sourceBoundaryOrigin,
          representativeSiteVar_origin]
        simp [ConcreteSpliceAttachment.fragmentWire,
          ConcreteSpliceAttachment.representativeTarget,
          concreteRepresentativeTarget,
          ConcreteSpliceAttachment.representativePosition]
        rfl
      have positionPackedEquality :
          liftOuterPacked attachment.diagram
              compiled.factor.frame.visible
              (attachment.hostRegion removed.site)
              (compiled.positionPackedAt position) =
            (⟨(extracted.checked.val.diagram.wires
                  (extracted.checked.val.boundary.get position)).sig,
                sitePositionVar extracted compiled position⟩ :
              PackedVar
                (compiled.factor.frame.visible.extend
                  (attachment.hostRegion removed.site)).sigs) := by
        apply
          packedOrigin_injective attachment.diagram
            (compiled.factor.frame.visible.extend
              (attachment.hostRegion removed.site)).ids
            (candidateSiteContext_nodup result compiled)
        change
          ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (liftOuterPacked attachment.diagram
                compiled.factor.frame.visible
                (attachment.hostRegion removed.site)
                (compiled.positionPackedAt position)).snd =
            ConcreteElaboration.WireContext.origin attachment.diagram
              (compiled.factor.frame.visible.extend
                (attachment.hostRegion removed.site)).ids
              (sitePositionVar extracted compiled position)
        exact
          (liftOuterPacked_origin attachment.diagram
            compiled.factor.frame.visible
            (attachment.hostRegion removed.site)
            (compiled.positionPackedAt position)).trans
            ((compiled.positionPackedAt_origin position).trans
              (sitePositionVar_origin extracted compiled position).symm)
      have leftValue :
          evaluatePacked targetEnv
              (⟨(extracted.checked.val.diagram.wires
                  (extracted.checked.val.boundary.get position)).sig,
                representativeSiteVar extracted compiled position⟩ :
                PackedVar
                  (compiled.factor.frame.visible.extend
                    (attachment.hostRegion removed.site)).sigs) =
            evaluatePacked
              (Env.comp env
                (compiled.intrinsicAttachment extracted).classMap)
              (extracted.boundaryPackedAt position) := by
        rw [boundaryPackedEquation]
        have atSource :=
          congrFun (congrFun environmentsEqual boundarySig)
            sourceBoundaryVar
        have atBoundary :=
          extendOpenRootEnvironment_outerValue
            extracted.checked.val sourceValues
            (Env.comp env
              (compiled.intrinsicAttachment extracted).classMap)
            boundaryVar
        exact
          (congrArg (evaluatePacked targetEnv)
              representativePackedEquality).symm.trans
            (congrArg
              (fun value =>
                (⟨boundarySig, value⟩ : Sigma pre.Domain))
              (atSource.trans atBoundary))
      have rightValue :
          evaluatePacked targetEnv
              (⟨(extracted.checked.val.diagram.wires
                  (extracted.checked.val.boundary.get position)).sig,
                sitePositionVar extracted compiled position⟩ :
                PackedVar
                  (compiled.factor.frame.visible.extend
                    (attachment.hostRegion removed.site)).sigs) =
            evaluatePacked env
              (compiled.positionPackedAt position) := by
        rw [← positionPackedEquality]
        rcases compiled.positionPackedAt position with
          ⟨positionSig, positionVar⟩
        exact congrArg
          (fun value => (⟨positionSig, value⟩ : Sigma pre.Domain))
          (extendEnvironment_liftOuterVar attachment.diagram
            compiled.factor.frame.visible
            (attachment.hostRegion removed.site)
            pre targetValues env positionVar)
      have packedValuesEqual :=
        leftValue.trans (boundaryAtPosition.trans rightValue.symm)
      exact eq_of_heq (Sigma.mk.inj packedValuesEqual).2
    refine ⟨targetValues, ?_⟩
    change
      denoteItemSeq pre definitionEnv targetEnv
        ((copiedNodes.append identityItems).append targetChildren)
    rw [denoteItemSeq_append, denoteItemSeq_append]
    exact
      ⟨⟨copiedNodesDenote, identityItemsDenote⟩,
        targetChildrenDenote⟩

/--
A checked concrete splice denotes exactly when the intrinsic splice denotes in
the one executable frame computed from that result.
-/
theorem denote_splice
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment :
      ConcreteSpliceAttachment removed extracted.checked}
    (result : ConcreteSpliceResult attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ compiled : SpliceCompilation attachment,
      denoteChecked pre definitionEnv result.checked ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.factor.frame.context.fill
            (intrinsicSplice extracted.openDiagram
              (compiled.intrinsicAttachment extracted))) := by
  obtain ⟨factor, factorCompiled⟩ :=
    compileSpliceFactor?_complete result
  let compiled : SpliceCompilation attachment :=
    ⟨factor, factorCompiled⟩
  refine ⟨compiled, ?_⟩
  rw [elaborate_denotes_checked]
  have elaborateEquality :
      elaborate result.checked =
        compiled.factor.frame.context.fill
          compiled.factor.frame.siteBody := by
    have elaborated :=
      elaborateWith_compiles definitions attachment.diagram
        result.wellFormed
    exact Option.some.inj
      (elaborated.symm.trans compiled.root_compiles)
  rw [elaborateEquality]
  exact
    context_equiv compiled.factor.frame.context pre definitionEnv
      compiled.factor.frame.siteBody
      (intrinsicSplice extracted.openDiagram
        (compiled.intrinsicAttachment extracted))
      (siteBody_denote_iff_intrinsic extracted result compiled pre
        definitionEnv)
      Env.empty

/--
Reconstructing an exact occurrence preserves host denotation, with the host on
the left and the computed intrinsic replacement on the right.
-/
theorem exact_occurrence_denotation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (extracted : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment removed extracted.checked)
    (accepted :
      reconstructionAttachment? occurrence extracted removed =
        some attachment)
    (result : ConcreteSpliceResult attachment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ compiled : SpliceCompilation attachment,
      denoteChecked pre definitionEnv host ↔
        denoteRegion pre definitionEnv Env.empty
          (compiled.factor.frame.context.fill
            (intrinsicSplice extracted.openDiagram
              (compiled.intrinsicAttachment extracted))) := by
  obtain ⟨compiled, spliceDenotation⟩ :=
    denote_splice extracted result pre definitionEnv
  refine ⟨compiled, ?_⟩
  exact
    (reconstruction_denotation occurrence extracted removed attachment
      accepted result pre definitionEnv).symm.trans spliceDenotation

end RemovalFactorization

end VisualProof
