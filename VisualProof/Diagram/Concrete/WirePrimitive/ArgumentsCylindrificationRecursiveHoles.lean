import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem recursive_classifier_at_aligned_index
    (values : List α)
    (nodes : List β)
    (classify : β → Option α)
    (aligned : values.map some = nodes.map classify)
    (valuesLength : values.length = count)
    (nodesLength : nodes.length = count)
    (index : Fin count) :
    classify (nodes.get (Fin.cast nodesLength.symm index)) =
      some (values.get (Fin.cast valuesLength.symm index)) := by
  have selected := get_of_list_eq aligned
    (Fin.cast (by simp [nodesLength]) index)
  simpa using selected.symm

/-- Canonical signature transport from the elaborator's dependent extended
context to the explicit local-block/outer-block context required by a
`CylindricalShape.block`. -/
def recursiveRegionNormalization
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId) :
    WireRenaming (context.extend region).sigs
      ((diagram.wiresAt region).map
          (fun wire => (diagram.wires wire).sig) ++ context.sigs) :=
  fun {_} value =>
    ConcreteElaboration.WireContext.sigs_extend context region ▸ value

/-- Abstract the direct acted applications from an authoritative compiled
node sequence after putting its context in canonical local/outer order. -/
def recursiveNormalizedNodeShape
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (head : Var context.sigs (.rel arguments))
    (items : ItemSeq definitions (context.extend region).sigs) :
    UniformIntrinsicRegion definitions arguments
      ((diagram.wiresAt region).map
          (fun wire => (diagram.wires wire).sig) ++ context.sigs) :=
  UniformIntrinsicRegion.abstractAppliedItems
    (Var.appendRight
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
      head)
    (items.renameWires (recursiveRegionNormalization context region))

private theorem recursive_normalization_cast_cancel
    (same : left = right)
    (value : Var right signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem recursive_normalization_cast_cancel_reverse
    (same : left = right)
    (value : Var left signature) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem recursive_cast_appendLeft_local
    (same : left = right)
    (value : Var left signature)
    (outer : List Sig) :
    congrArg (fun localSigs => localSigs ++ outer) same ▸
        Var.appendLeft value outer =
      Var.appendLeft (same ▸ value) outer := by
  cases same
  rfl

/-- Any compiled head with the inherited head's concrete owner normalizes
to the canonical appended outer head. -/
theorem recursiveRegionNormalization_head_of_origin
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (contextNodup : (context.extend region).ids.Nodup)
    (head : Var (context.extend region).sigs (.rel arguments))
    (outerHead : Var context.sigs (.rel arguments))
    (headOrigin :
      ConcreteElaboration.WireContext.origin diagram
          (context.extend region).ids head = wire)
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin diagram context.ids outerHead =
        wire) :
    recursiveRegionNormalization context region head =
      Var.appendRight
        ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
        outerHead := by
  let canonical : Var (context.extend region).sigs (.rel arguments) :=
    (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
      Var.appendRight
        ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
        outerHead
  have canonicalOrigin :
      ConcreteElaboration.WireContext.origin diagram
          (context.extend region).ids canonical = wire := by
    unfold canonical
    rw [recursive_origin_extend_outer]
    exact outerHeadOrigin
  have headExact : head = canonical :=
    InsertionCompilation.NaturalityInternal.origin_injective diagram
      (context.extend region).ids contextNodup
      (headOrigin.trans canonicalOrigin.symm)
  subst head
  unfold recursiveRegionNormalization canonical
  exact recursive_normalization_cast_cancel _ _

private theorem recursive_argumentOrigins_get
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (start : Nat)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs)
    (origins :
      ConcreteElaboration.ArgumentOrigins diagram context node start values)
    (index : Nat)
    (bound : index < argumentSigs.length) :
    diagram.endpointOwner? ⟨node, .arg (start + index)⟩ =
      some ((ConcreteElaboration.variableOrigins diagram context values).get
        ⟨index, by
          simpa [TypedArguments.variableOrigins_length] using bound⟩) := by
  induction values generalizing start index with
  | nil => simp at bound
  | @cons signature rest head tail induction =>
      cases index with
      | zero =>
          simpa [ConcreteElaboration.ArgumentOrigins,
            ConcreteElaboration.variableOrigins] using origins.1
      | succ index =>
          have tailBound : index < rest.length := by simpa using bound
          have tailExact := induction (start := start + 1) origins.2
            index tailBound
          simpa [ConcreteElaboration.variableOrigins, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using tailExact

/-- Any checked application local to a recursively compiled region has the
same atom head and ordered concrete argument owners in that region's exact
compiler context.  Unlike the root-only frame lemma, this statement uses
the authoritative `compileNodes?` equation supplied by region recursion. -/
theorem compileAppliedSiteAt?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (source.val.nodesAt region) = some items)
    (site : AppliedSite source wire)
    (siteRegion : site.region = region) :
    ∃ (head : Var context.sigs (.rel site.argumentSignatures))
      (arguments : Vars context.sigs site.argumentSignatures),
      ConcreteElaboration.Internal.compileNode? definitions source.val
          context site.node = some (.atom head arguments) ∧
      ConcreteElaboration.WireContext.origin source.val context.ids head =
        wire ∧
      ConcreteElaboration.variableOrigins source.val context arguments =
        site.arguments := by
  have nodeMember : site.node ∈ source.val.nodesAt region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin site.node, ?_⟩
    rw [site.node_data, siteRegion]
    exact beq_iff_eq.mpr rfl
  obtain ⟨item, singletonCompiled⟩ :=
    ConcreteWireQuantifier.SingletonRemovalSemantics.compileNodes_singleton_of_member
      definitions source.val context (source.val.nodesAt region) items
      compiled site.node nodeMember
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape source.val context site.node
      site.node_data singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have nodeCompiled :
      ConcreteElaboration.Internal.compileNode? definitions source.val
          context site.node = some (.atom head arguments) := by
    cases found : ConcreteElaboration.Internal.compileNode? definitions
        source.val context site.node with
    | none =>
        simp [ConcreteElaboration.compileNodes?, found] at singletonCompiled
    | some foundItem =>
        have foundExact : foundItem = .atom head arguments := by
          simpa [ConcreteElaboration.compileNodes?, found] using
            singletonCompiled
        simpa [foundExact] using found
  have headExact :
      ConcreteElaboration.WireContext.origin source.val context.ids head =
        wire :=
    Option.some.inj (headOrigin.symm.trans site.endpoint_owner)
  have argumentsExact :
      ConcreteElaboration.variableOrigins source.val context arguments =
        site.arguments := by
    apply List.ext_get
    · simpa [TypedArguments.variableOrigins_length] using
        site.arguments_length.symm
    · intro index leftBound rightBound
      have compiledOwner := recursive_argumentOrigins_get source.val context
        site.node 0 arguments argumentOrigins index (by
          rw [← TypedArguments.variableOrigins_length source.val context
            arguments]
          exact leftBound)
      have siteOwner := site.argument_owner index rightBound
      exact Option.some.inj (compiledOwner.symm.trans (by
        simpa using siteOwner))
  exact ⟨head, arguments, nodeCompiled, headExact, argumentsExact⟩

private theorem recursiveRegionNormalization_injective
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    {signature : Sig} :
    Function.Injective
      (@recursiveRegionNormalization _ diagram context region signature) := by
  intro left right same
  unfold recursiveRegionNormalization at same
  have recovered := congrArg
    (fun value =>
      (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
        value) same
  simpa only [recursive_normalization_cast_cancel_reverse] using recovered

/-- Recognition by the canonical normalized outer-head slot implies that the
compiled head is owned by that concrete outer wire. -/
theorem recursiveRegionNormalization_origin_of_head
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (head : Var (context.extend region).sigs (.rel arguments))
    (outerHead : Var context.sigs (.rel arguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin diagram context.ids outerHead =
        wire)
    (normalized :
      recursiveRegionNormalization context region head =
        Var.appendRight
          ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
          outerHead) :
    ConcreteElaboration.WireContext.origin diagram
        (context.extend region).ids head = wire := by
  let canonical : Var (context.extend region).sigs (.rel arguments) :=
    (ConcreteElaboration.WireContext.sigs_extend context region).symm ▸
      Var.appendRight
        ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
        outerHead
  have canonicalNormalized :
      recursiveRegionNormalization context region canonical =
        Var.appendRight
          ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig)
          outerHead := by
    unfold canonical recursiveRegionNormalization
    exact recursive_normalization_cast_cancel _ _
  have headExact : head = canonical :=
    recursiveRegionNormalization_injective context region
      (normalized.trans canonicalNormalized.symm)
  subst head
  unfold canonical
  exact (recursive_origin_extend_outer diagram context region outerHead).trans
    outerHeadOrigin

/-- The normalized per-node classifier for an arbitrary recursively compiled
region. -/
def recursiveRegionClassifier
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (outerHead : Var context.sigs (.rel arguments))
    (node : source.val.NodeId) :
    Option (Vars
      ((source.val.wiresAt region).map
          (fun wire => (source.val.wires wire).sig) ++ context.sigs)
      arguments) :=
  UniformIntrinsicRegion.renamedCompiledAppliedArguments? definitions source.val
    (context.extend region) (recursiveRegionNormalization context region)
    (Var.appendRight
      ((source.val.wiresAt region).map fun wire => (source.val.wires wire).sig)
      outerHead) node

/-- Every local application of an inherited relation head is selected by the
arbitrary-region normalized classifier with its exact ordered arguments. -/
theorem recursiveRegionClassifier_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items : ItemSeq definitions (context.extend region).sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) = some items)
    (contextNodup : (context.extend region).ids.Nodup)
    (outerHead : Var context.sigs (.rel sourceArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids outerHead =
        wire)
    (site : AppliedSite source wire)
    (siteRegion : site.region = region) :
    ∃ arguments : Vars (context.extend region).sigs sourceArguments,
      recursiveRegionClassifier source context region outerHead site.node =
          some (Vars.rename (recursiveRegionNormalization context region)
            arguments) ∧
      ConcreteElaboration.variableOrigins source.val (context.extend region)
          arguments = site.arguments := by
  have argumentSignatures :=
    appliedSite_arguments_eq_relationArguments sourceArguments
      sourceSignature site
  cases argumentSignatures
  obtain ⟨head, arguments, nodeCompiled, headOrigin, argumentsOrigin⟩ :=
    compileAppliedSiteAt?_complete (context.extend region) region items compiled
      site siteRegion
  have normalizedHead := recursiveRegionNormalization_head_of_origin context
    region contextNodup head outerHead headOrigin outerHeadOrigin
  refine ⟨arguments, ?_, argumentsOrigin⟩
  simp [recursiveRegionClassifier,
    UniformIntrinsicRegion.renamedCompiledAppliedArguments?, nodeCompiled,
    UniformIntrinsicRegion.matchedHeadArguments?, normalizedHead]

/-- Conversely, classifier success is concrete evidence that the node belongs
to the exhaustive applied-site list for the inherited wire. -/
theorem recursiveRegionClassifier_site
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sourceArguments : List Sig}
    (sites : AllAppliedSites source wire)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (outerHead : Var context.sigs (.rel sourceArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids outerHead =
        wire)
    (node : source.val.NodeId)
    (values : Vars
      ((source.val.wiresAt region).map
          (fun localWire => (source.val.wires localWire).sig) ++ context.sigs)
      sourceArguments)
    (accepted :
      recursiveRegionClassifier source context region outerHead node =
        some values) :
    ∃ site, site ∈ sites.sites ∧ site.node = node := by
  unfold recursiveRegionClassifier at accepted
  unfold UniformIntrinsicRegion.renamedCompiledAppliedArguments? at accepted
  cases compiled : ConcreteElaboration.Internal.compileNode? definitions
      source.val (context.extend region) node with
  | none => simp [compiled] at accepted
  | some item =>
      cases item with
      | atom atomHead arguments =>
          have matched :
              UniformIntrinsicRegion.matchedHeadArguments?
                  (Var.appendRight
                    ((source.val.wiresAt region).map fun localWire =>
                      (source.val.wires localWire).sig)
                    outerHead)
                  (recursiveRegionNormalization context region atomHead)
                  (Vars.rename (recursiveRegionNormalization context region)
                    arguments) = some values := by
            simpa [compiled] using accepted
          obtain ⟨same, normalized⟩ :=
            UniformIntrinsicRegion.matchedHeadArguments_head_exact _ _ _
              matched
          have headOrigin :
              ConcreteElaboration.WireContext.origin source.val
                  (context.extend region).ids atomHead = wire := by
            cases same
            exact recursiveRegionNormalization_origin_of_head context region
              atomHead outerHead outerHeadOrigin normalized
          have nodeShape : ∃ nodeRegion atomArguments,
              source.val.nodes node = .atom nodeRegion atomArguments := by
            cases nodeData : source.val.nodes node with
            | atom nodeRegion atomArguments =>
                exact ⟨nodeRegion, atomArguments, rfl⟩
            | ref nodeRegion definition refArguments =>
                simp [ConcreteElaboration.Internal.compileNode?, nodeData]
                  at compiled
                cases resolved :
                    ConcreteElaboration.Internal.resolveArgs? source.val
                      (context.extend region) node refArguments 0 <;>
                  simp [resolved] at compiled
            | identity nodeRegion signature arity =>
                simp [ConcreteElaboration.Internal.compileNode?, nodeData]
                  at compiled
                cases resolved :
                    ConcreteElaboration.Internal.resolveIdentityPorts?
                      source.val (context.extend region) node signature arity 0 <;>
                  simp [resolved] at compiled
          obtain ⟨nodeRegion, atomArguments, nodeData⟩ := nodeShape
          have singletonCompiled :
              ConcreteElaboration.compileNodes? definitions source.val
                  (context.extend region) [node] =
                some (.cons (.atom atomHead arguments) .nil) := by
            simp [ConcreteElaboration.compileNodes?, compiled]
          obtain ⟨shapeHead, shapeArguments, itemExact, ownerExact,
              _argumentOrigins⟩ :=
            ConcreteElaboration.compileNodes?_atom_shape source.val
              (context.extend region) node nodeData singletonCompiled
          have atomExact :
              (.atom atomHead arguments :
                  Item definitions (context.extend region).sigs) =
                .atom shapeHead shapeArguments :=
            ItemSeq.cons.inj itemExact |>.1
          cases atomExact
          have owner : source.val.endpointOwner? ⟨node, .head⟩ =
              some wire := by simpa [headOrigin] using ownerExact
          have endpointMember :
              (⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
                (source.val.wires wire).endpoints := by
            have occurrence := ConcreteDiagram.endpointOwner?_occurs
              source.val ⟨node, .head⟩ wire owner
            simp only [ConcreteDiagram.endpointOccurrences,
              List.mem_flatMap] at occurrence
            obtain ⟨candidate, _candidateMember, endpointOccurrence⟩ :=
              occurrence
            obtain ⟨candidateEndpoint, incident, exact⟩ :=
              List.mem_map.mp endpointOccurrence
            cases exact
            exact incident
          have siteEndpointMember :
              (⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
                sites.sites.map AppliedSite.endpoint := by
            rw [sites.exhaustive]
            exact endpointMember
          obtain ⟨site, siteMember, endpointExact⟩ :=
            List.mem_map.mp siteEndpointMember
          exact ⟨site, siteMember,
            congrArg CEndpoint.node endpointExact⟩
      | named definition arguments => simp [compiled] at accepted
      | identity signature ports atLeastTwo => simp [compiled] at accepted
      | cut body => simp [compiled] at accepted
      | bind signature body => simp [compiled] at accepted

/-- On the authoritative node order of a recursive region, classifier
success is exactly membership in that region's acted application nodes. -/
theorem recursiveRegionClassifier_isSome
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items : ItemSeq definitions (context.extend region).sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) = some items)
    (contextNodup : (context.extend region).ids.Nodup)
    (outerHead : Var context.sigs (.rel sourceArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids outerHead =
        wire)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt region) :
    (recursiveRegionClassifier source context region outerHead node).isSome =
      decide (node ∈ argumentSiteNodes sites) := by
  cases classified :
      recursiveRegionClassifier source context region outerHead node with
  | none =>
      simp only [Option.isSome_none]
      symm
      apply decide_eq_false_iff_not.mpr
      intro member
      have sourceNodeMember :
          node ∈ sourceSiteNodesAt sites region := by
        apply List.mem_filter.mpr
        exact ⟨nodeAt, decide_eq_true member⟩
      have orderedMember :=
        (aritySiteNodesAt_mem_iff sites region node).mpr
          sourceNodeMember
      obtain ⟨siteIndex, siteIndexMember, nodeExact⟩ :=
        List.mem_map.mp orderedMember
      have siteRegion :
          (sites.sites.get siteIndex).region = region := by
        exact eq_of_beq (List.mem_filter.mp siteIndexMember).2
      obtain ⟨arguments, selected, _origins⟩ :=
        recursiveRegionClassifier_complete sourceArguments sourceSignature
          context region items compiled contextNodup outerHead outerHeadOrigin
          (sites.sites.get siteIndex) siteRegion
      rw [nodeExact, classified] at selected
      contradiction
  | some values =>
      simp only [Option.isSome_some]
      symm
      apply decide_eq_true
      obtain ⟨site, siteMember, nodeExact⟩ :=
        recursiveRegionClassifier_site sites context region outerHead
          outerHeadOrigin node values classified
      unfold argumentSiteNodes
      apply List.mem_map.mpr
      exact ⟨site, siteMember, nodeExact⟩

/-- The holes abstracted from an arbitrary recursively compiled node sequence
are aligned position-for-position with the source applications in concrete
node order. -/
theorem recursiveRegionHoleValues_alignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items : ItemSeq definitions (context.extend region).sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) = some items)
    (contextNodup : (context.extend region).ids.Nodup)
    (outerHead : Var context.sigs (.rel sourceArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids outerHead =
        wire) :
    (recursiveNormalizedNodeShape context region outerHead items).holeValues.map
        some =
      (sourceSiteNodesAt sites region).map
        (recursiveRegionClassifier source context region outerHead) := by
  unfold recursiveNormalizedNodeShape
  rw [UniformIntrinsicRegion.abstractAppliedItems_holeValues]
  rw [UniformIntrinsicRegion.directAppliedArguments_rename_compileNodes
    definitions source.val (context.extend region)
    (recursiveRegionNormalization context region)
    (Var.appendRight
      ((source.val.wiresAt region).map fun localWire =>
        (source.val.wires localWire).sig)
      outerHead) (source.val.nodesAt region) items compiled]
  unfold sourceSiteNodesAt
  apply UniformIntrinsicRegion.map_some_filterMap_eq_map_filter
  intro node nodeAt
  exact recursiveRegionClassifier_isSome sourceArguments sourceSignature sites
    context region items compiled contextNodup outerHead outerHeadOrigin node
    nodeAt

/-- Target holes at an image region are aligned with the generated target
applications in the source endpoint/site order. -/
theorem recursiveTargetRegionHoleValues_alignment
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (region : source.val.RegionId)
    (targetItems : ItemSeq definitions
      (targetOuter.extend (result.regionImage region)).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (targetOuter.extend (result.regionImage region))
          (result.checked.val.nodesAt (result.regionImage region)) =
        some targetItems)
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (targetHead : Var targetOuter.sigs (.rel result.targetArguments))
    (targetHeadOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val targetOuter.ids
          targetHead = result.targetWire) :
    (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
        targetHead targetItems).holeValues.map some =
      (aritySitesAt result.sites region).map fun site =>
        recursiveRegionClassifier result.checked targetOuter
          (result.regionImage region) targetHead (result.targetNode site) := by
  have aligned := recursiveRegionHoleValues_alignment
    result.targetArguments result.targetWire_signature result.targetSites
    targetOuter (result.regionImage region) targetItems targetCompiled
    targetNodup targetHead targetHeadOrigin
  rw [ArgumentResult.targetSiteNodesAt_exact result region] at aligned
  simpa [List.map_map, Function.comp_def] using aligned

/-- Source and target normalized node bodies expose exactly one hole per
construction-owned fresh wire at every below-head region. -/
theorem recursiveRegionHole_lengths
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (region : source.val.RegionId)
    (sourceItems : ItemSeq definitions (sourceOuter.extend region).sigs)
    (targetItems : ItemSeq definitions
      (targetOuter.extend (result.regionImage region)).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (targetOuter.extend (result.regionImage region))
          (result.checked.val.nodesAt (result.regionImage region)) =
        some targetItems)
    (sourceNodup : (sourceOuter.extend region).ids.Nodup)
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (sourceHead : Var sourceOuter.sigs (.rel sourceArguments))
    (targetHead : Var targetOuter.sigs (.rel result.targetArguments))
    (sourceHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val sourceOuter.ids
          sourceHead = wire)
    (targetHeadOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val targetOuter.ids
          targetHead = result.targetWire) :
    (recursiveNormalizedNodeShape sourceOuter region sourceHead
        sourceItems).holeValues.length = (arityFreshAt result region).length ∧
      (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
        targetHead targetItems).holeValues.length =
          (arityFreshAt result region).length := by
  have sourceAligned := recursiveRegionHoleValues_alignment sourceArguments
    sourceSignature result.sites sourceOuter region sourceItems sourceCompiled
    sourceNodup sourceHead sourceHeadOrigin
  have sourceLength := congrArg List.length sourceAligned
  simp only [List.length_map] at sourceLength
  have targetAligned := recursiveTargetRegionHoleValues_alignment result
    targetOuter region targetItems targetCompiled targetNodup targetHead
    targetHeadOrigin
  have targetLength := congrArg List.length targetAligned
  simp only [List.length_map] at targetLength
  constructor
  · exact sourceLength.trans
      (sourceSiteNodesAt_length_fresh source wire sourceArguments
        sourceSignature newArgument result accepted region)
  · exact targetLength.trans
      (by simpa using
        (aritySitesAt_length_fresh source wire sourceArguments sourceSignature
          newArgument result accepted region))

/-- Extending the inherited context action through a below-head region and
then normalizing is exactly the block embedding applied after source
normalization. -/
theorem recursiveRegionNormalizations_commute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    {signature : Sig}
    (value : Var (sourceOuter.extend region).sigs signature) :
    recursiveRegionNormalization targetOuter (result.regionImage region)
        (arityShift_regionEmbedding_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead
          sourceOuter targetOuter outer value) =
      (arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).embed
        outer (recursiveRegionNormalization sourceOuter region value) := by
  unfold arityShift_regionEmbedding_below recursiveRegionNormalization
  rw [recursive_normalization_cast_cancel]

/-- Pointwise origin naturality upgrades to equality of complete normalized
argument tuples in any below-head region. -/
theorem recursiveRegionNormalizations_commute_of_mapped_origins
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    {argumentSignatures : List Sig}
    (sourceValues :
      Vars (sourceOuter.extend region).sigs argumentSignatures)
    (targetValues : Vars
      (targetOuter.extend (result.regionImage region)).sigs
      argumentSignatures)
    (mappedOrigins :
      ConcreteElaboration.variableOrigins result.checked.val
          (targetOuter.extend (result.regionImage region)) targetValues =
        (ConcreteElaboration.variableOrigins source.val
          (sourceOuter.extend region) sourceValues).map
            result.contextWireMap) :
    Vars.rename
        ((arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).embed
            outer)
        (Vars.rename (recursiveRegionNormalization sourceOuter region)
          sourceValues) =
      Vars.rename
        (recursiveRegionNormalization targetOuter (result.regionImage region))
        targetValues := by
  induction sourceValues with
  | nil =>
      cases targetValues
      rfl
  | cons sourceHead sourceTail induction =>
      cases targetValues with
      | cons targetHead targetTail =>
          simp only [ConcreteElaboration.variableOrigins, List.map_cons,
            List.cons.injEq] at mappedOrigins
          have expectedOrigin := arityShift_regionEmbedding_below_origin
            source wire sourceArguments sourceSignature newArgument result
            accepted region notHead sourceOuter targetOuter outer outerOrigin
            sourceHead
          have targetHeadExact : targetHead =
              arityShift_regionEmbedding_below source wire sourceArguments
                sourceSignature newArgument result accepted region notHead
                sourceOuter targetOuter outer sourceHead :=
            InsertionCompilation.NaturalityInternal.origin_injective
              result.checked.val
              (targetOuter.extend (result.regionImage region)).ids targetNodup
              (mappedOrigins.1.trans expectedOrigin.symm)
          subst targetHead
          simp only [Vars.rename]
          rw [recursiveRegionNormalizations_commute source wire sourceArguments
            sourceSignature newArgument result accepted region notHead
            sourceOuter targetOuter outer sourceHead]
          exact congrArg (Vars.cons
            ((arityShift_regionBounds_below source wire sourceArguments
              sourceSignature newArgument result accepted region notHead).embed
                outer
                (recursiveRegionNormalization sourceOuter region sourceHead)))
            (induction targetTail mappedOrigins.2)

/-- A checked target variable owned by the construction's regional fresh wire
normalizes to the corresponding `BoundCylindrification.freshVar`. -/
theorem recursiveRegionNormalization_fresh_of_origin
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming smallerOuter targetOuter.sigs)
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (freshIndex : Fin (arityFreshAt result region).length)
    (targetValue : Var
      (targetOuter.extend (result.regionImage region)).sigs newArgument)
    (targetOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val
          (targetOuter.extend (result.regionImage region)).ids targetValue =
        result.targetLocalWire ((arityFreshAt result region).get freshIndex)) :
    recursiveRegionNormalization targetOuter (result.regionImage region)
        targetValue =
      (arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).freshVar
        outer freshIndex := by
  let rootExact := arityShift_regionBounds_below_exact source wire
    sourceArguments sourceSignature newArgument result accepted region notHead
  let localFresh : Var
      ((result.checked.val.wiresAt (result.regionImage region)).map
        fun targetWire => (result.checked.val.wires targetWire).sig)
      newArgument :=
    rootExact.symm ▸
      Var.appendRight
        ((source.val.wiresAt region).map fun sourceWire =>
          (source.val.wires sourceWire).sig)
        (BoundCylindrification.repeatedVar newArgument
          (arityFreshAt result region).length freshIndex)
  let expected : Var
      (targetOuter.extend (result.regionImage region)).sigs newArgument :=
    (ConcreteElaboration.WireContext.sigs_extend targetOuter
      (result.regionImage region)).symm ▸
      Var.appendLeft localFresh targetOuter.sigs
  have localOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val
          (result.checked.val.wiresAt (result.regionImage region)) localFresh =
        result.targetLocalWire
          ((arityFreshAt result region).get freshIndex) := by
    simpa [rootExact, localFresh] using
      arityShift_regionBounds_below_freshLocal_origin source wire
        sourceArguments sourceSignature newArgument result accepted region
        notHead freshIndex
  have expectedOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val
          (targetOuter.extend (result.regionImage region)).ids expected =
        result.targetLocalWire
          ((arityFreshAt result region).get freshIndex) := by
    unfold expected
    exact (recursive_origin_extend_local result.checked.val targetOuter
      (result.regionImage region) localFresh).trans localOrigin
  have targetExact : targetValue = expected :=
    InsertionCompilation.NaturalityInternal.origin_injective
      result.checked.val
      (targetOuter.extend (result.regionImage region)).ids targetNodup
      (targetOrigin.trans expectedOrigin.symm)
  subst targetValue
  have expectedNormalized :
      recursiveRegionNormalization targetOuter (result.regionImage region)
          expected = Var.appendLeft localFresh targetOuter.sigs := by
    unfold expected recursiveRegionNormalization
    exact recursive_normalization_cast_cancel _ _
  rw [expectedNormalized]
  rw [arityShift_regionBounds_below_freshVar source wire sourceArguments
    sourceSignature newArgument result accepted region notHead outer
    freshIndex]
  unfold localFresh rootExact
  simpa only using
    (recursive_cast_appendLeft_local
      (arityShift_regionBounds_below_exact source wire sourceArguments
        sourceSignature newArgument result accepted region notHead).symm
      (Var.appendRight
        ((source.val.wiresAt region).map fun sourceWire =>
          (source.val.wires sourceWire).sig)
        (BoundCylindrification.repeatedVar newArgument
          (arityFreshAt result region).length freshIndex))
      targetOuter.sigs).symm

/-- Normalization and typed tuple splitting agree with the canonical below-
region bound certificate once the split components have their exact concrete
origins. -/
theorem recursiveNormalizedHole_split_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (freshIndex : Fin (arityFreshAt result region).length)
    (sourceValues : Vars
      (sourceOuter.extend region).sigs sourceArguments)
    (targetValues : Vars
      (targetOuter.extend (result.regionImage region)).sigs
      result.targetArguments)
    (mappedOrigins :
      ConcreteElaboration.variableOrigins result.checked.val
          (targetOuter.extend (result.regionImage region))
          ((arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted).splitVars targetValues).2 =
        (ConcreteElaboration.variableOrigins source.val
          (sourceOuter.extend region) sourceValues).map result.contextWireMap)
    (insertedOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val
          (targetOuter.extend (result.regionImage region)).ids
          ((arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted).splitVars targetValues).1 =
        result.targetLocalWire
          ((arityFreshAt result region).get freshIndex)) :
    (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted).splitVars
        (Vars.rename
          (recursiveRegionNormalization targetOuter
            (result.regionImage region)) targetValues) =
      ⟨(arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).freshVar
          outer freshIndex,
        Vars.rename
          ((arityShift_regionBounds_below source wire sourceArguments
            sourceSignature newArgument result accepted region notHead).embed
              outer)
          (Vars.rename (recursiveRegionNormalization sourceOuter region)
            sourceValues)⟩ := by
  rw [(arityShiftInsertion source wire sourceArguments sourceSignature
    newArgument result accepted).splitVars_rename]
  apply Prod.ext
  · simp only [Prod.fst]
    exact recursiveRegionNormalization_fresh_of_origin source wire
      sourceArguments sourceSignature newArgument result accepted region
      notHead targetOuter outer targetNodup freshIndex _ insertedOrigin
  · simp only [Prod.snd]
    exact (recursiveRegionNormalizations_commute_of_mapped_origins source wire
      sourceArguments sourceSignature newArgument result accepted region
      notHead sourceOuter targetOuter outer outerOrigin targetNodup sourceValues
      _ mappedOrigins).symm

/-- The construction-owned target-site origin suffix discharges both origin
premises of `recursiveNormalizedHole_split_exact`. -/
theorem recursiveNormalizedHole_split_exact_of_origins
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (freshIndex : Fin (arityFreshAt result region).length)
    (sourceValues : Vars
      (sourceOuter.extend region).sigs sourceArguments)
    (targetValues : Vars
      (targetOuter.extend (result.regionImage region)).sigs
      result.targetArguments)
    (originsExact :
      ConcreteElaboration.variableOrigins result.checked.val
          (targetOuter.extend (result.regionImage region)) targetValues =
        (ConcreteElaboration.variableOrigins source.val
          (sourceOuter.extend region) sourceValues).map result.contextWireMap ++
          [result.targetLocalWire
            ((arityFreshAt result region).get freshIndex)]) :
    (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted).splitVars
        (Vars.rename
          (recursiveRegionNormalization targetOuter
            (result.regionImage region)) targetValues) =
      ⟨(arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).freshVar
          outer freshIndex,
        Vars.rename
          ((arityShift_regionBounds_below source wire sourceArguments
            sourceSignature newArgument result accepted region notHead).embed
              outer)
          (Vars.rename (recursiveRegionNormalization sourceOuter region)
            sourceValues)⟩ := by
  let insertion := arityShiftInsertion source wire sourceArguments
    sourceSignature newArgument result accepted
  have prefixLength :
      ((ConcreteElaboration.variableOrigins source.val
          (sourceOuter.extend region) sourceValues).map
            result.contextWireMap).length = sourceArguments.length := by
    simpa using TypedArguments.variableOrigins_length source.val
      (sourceOuter.extend region) sourceValues
  obtain ⟨mappedOrigins, insertedOrigin⟩ :=
    insertion.splitVars_origins_of_append
      (arityShiftInsertion_position source wire sourceArguments
        sourceSignature newArgument result accepted)
      result.checked.val
      (targetOuter.extend (result.regionImage region)) targetValues
      ((ConcreteElaboration.variableOrigins source.val
        (sourceOuter.extend region) sourceValues).map result.contextWireMap)
      prefixLength
      (result.targetLocalWire
        ((arityFreshAt result region).get freshIndex)) originsExact
  exact recursiveNormalizedHole_split_exact source wire sourceArguments
    sourceSignature newArgument result accepted region notHead sourceOuter
    targetOuter outer outerOrigin targetNodup freshIndex sourceValues
    targetValues mappedOrigins insertedOrigin

/-- The ordered source/target hole alignments select the exact site tuples
needed by the pointwise below-region split theorem. -/
theorem recursiveRegionHole_split_exact
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (sourceItems : ItemSeq definitions (sourceOuter.extend region).sigs)
    (targetItems : ItemSeq definitions
      (targetOuter.extend (result.regionImage region)).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (targetOuter.extend (result.regionImage region))
          (result.checked.val.nodesAt (result.regionImage region)) =
        some targetItems)
    (sourceNodup : (sourceOuter.extend region).ids.Nodup)
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (sourceHead : Var sourceOuter.sigs (.rel sourceArguments))
    (targetHead : Var targetOuter.sigs (.rel result.targetArguments))
    (sourceHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val sourceOuter.ids
          sourceHead = wire)
    (targetHeadOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val targetOuter.ids
          targetHead = result.targetWire)
    (index : Fin (arityFreshAt result region).length) :
    (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted).splitVars
        ((recursiveNormalizedNodeShape targetOuter
          (result.regionImage region) targetHead targetItems).holeValues.get
            (Fin.cast
              (recursiveRegionHole_lengths source wire sourceArguments
                sourceSignature newArgument result accepted sourceOuter
                targetOuter region sourceItems targetItems sourceCompiled
                targetCompiled sourceNodup targetNodup sourceHead targetHead
                sourceHeadOrigin targetHeadOrigin).2.symm index)) =
      ⟨(arityShift_regionBounds_below source wire sourceArguments
          sourceSignature newArgument result accepted region notHead).freshVar
          outer
          (arityFreshIndex source wire sourceArguments sourceSignature
            newArgument result accepted region index),
        Vars.rename
          ((arityShift_regionBounds_below source wire sourceArguments
            sourceSignature newArgument result accepted region notHead).embed
              outer)
          ((recursiveNormalizedNodeShape sourceOuter region sourceHead
            sourceItems).holeValues.get
              (Fin.cast
                (recursiveRegionHole_lengths source wire sourceArguments
                  sourceSignature newArgument result accepted sourceOuter
                  targetOuter region sourceItems targetItems sourceCompiled
                  targetCompiled sourceNodup targetNodup sourceHead targetHead
                  sourceHeadOrigin targetHeadOrigin).1.symm
                (aritySourceIndex source wire sourceArguments sourceSignature
                  newArgument result accepted region index)))⟩ := by
  let freshCount := (arityFreshAt result region).length
  let sitesAt := aritySitesAt result.sites region
  have sitesLength := aritySitesAt_length_fresh source wire sourceArguments
    sourceSignature newArgument result accepted region
  let sitePosition : Fin sitesAt.length := Fin.cast sitesLength.symm index
  let site := sitesAt.get sitePosition
  have siteRegion : (result.sites.sites.get site).region = region :=
    eq_of_beq (List.mem_filter.mp (List.get_mem sitesAt sitePosition)).2
  let sourceNodes := sourceSiteNodesAt result.sites region
  have sourceNodesLength := sourceSiteNodesAt_length_fresh source wire
    sourceArguments sourceSignature newArgument result accepted region
  let sourceOrder := aritySourceIndex source wire sourceArguments
    sourceSignature newArgument result accepted region
  have sourceNodeExact := aritySourceIndex_spec source wire sourceArguments
    sourceSignature newArgument result accepted region index
  have sourceAligned := recursiveRegionHoleValues_alignment sourceArguments
    sourceSignature result.sites sourceOuter region sourceItems sourceCompiled
    sourceNodup sourceHead sourceHeadOrigin
  obtain ⟨sourceValues, sourceClassified, sourceOrigins⟩ :=
    recursiveRegionClassifier_complete sourceArguments sourceSignature
      sourceOuter region sourceItems sourceCompiled sourceNodup sourceHead
      sourceHeadOrigin (result.sites.sites.get site) siteRegion
  have sourceClassifiedAt := recursive_classifier_at_aligned_index
    (recursiveNormalizedNodeShape sourceOuter region sourceHead
      sourceItems).holeValues sourceNodes
    (recursiveRegionClassifier source sourceOuter region sourceHead)
    sourceAligned
    (recursiveRegionHole_lengths source wire sourceArguments sourceSignature
      newArgument result accepted sourceOuter targetOuter region sourceItems
      targetItems sourceCompiled targetCompiled sourceNodup targetNodup
      sourceHead targetHead sourceHeadOrigin targetHeadOrigin).1
    sourceNodesLength (sourceOrder index)
  have sourceHoleExact :
      (recursiveNormalizedNodeShape sourceOuter region sourceHead
        sourceItems).holeValues.get
          (Fin.cast
            (recursiveRegionHole_lengths source wire sourceArguments
              sourceSignature newArgument result accepted sourceOuter
              targetOuter region sourceItems targetItems sourceCompiled
              targetCompiled sourceNodup targetNodup sourceHead targetHead
              sourceHeadOrigin targetHeadOrigin).1.symm
            (sourceOrder index)) =
        Vars.rename (recursiveRegionNormalization sourceOuter region)
          sourceValues := by
    rw [sourceNodeExact, sourceClassified] at sourceClassifiedAt
    exact Option.some.inj sourceClassifiedAt.symm
  have targetAligned := recursiveTargetRegionHoleValues_alignment result
    targetOuter region targetItems targetCompiled targetNodup targetHead
    targetHeadOrigin
  have targetSiteRegion :
      (targetAppliedSite result site).region = result.regionImage region := by
    rw [targetAppliedSite_region, siteRegion]
  obtain ⟨targetValues, targetClassified, targetOrigins⟩ :=
    recursiveRegionClassifier_complete result.targetArguments
      result.targetWire_signature targetOuter (result.regionImage region)
      targetItems targetCompiled targetNodup targetHead targetHeadOrigin
      (targetAppliedSite result site) targetSiteRegion
  have targetClassifiedAt := recursive_classifier_at_aligned_index
    (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
      targetHead targetItems).holeValues sitesAt
    (fun selected => recursiveRegionClassifier result.checked targetOuter
      (result.regionImage region) targetHead (result.targetNode selected))
    targetAligned
    (recursiveRegionHole_lengths source wire sourceArguments sourceSignature
      newArgument result accepted sourceOuter targetOuter region sourceItems
      targetItems sourceCompiled targetCompiled sourceNodup targetNodup
      sourceHead targetHead sourceHeadOrigin targetHeadOrigin).2
    sitesLength index
  have targetHoleExact :
      (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
        targetHead targetItems).holeValues.get
          (Fin.cast
            (recursiveRegionHole_lengths source wire sourceArguments
              sourceSignature newArgument result accepted sourceOuter
              targetOuter region sourceItems targetItems sourceCompiled
              targetCompiled sourceNodup targetNodup sourceHead targetHead
              sourceHeadOrigin targetHeadOrigin).2.symm index) =
        Vars.rename
          (recursiveRegionNormalization targetOuter
            (result.regionImage region)) targetValues := by
    change recursiveRegionClassifier result.checked targetOuter
      (result.regionImage region) targetHead (result.targetNode site) = _
      at targetClassifiedAt
    rw [← targetAppliedSite_node result site, targetClassified]
      at targetClassifiedAt
    exact Option.some.inj targetClassifiedAt.symm
  have freshPositionExact := arityFreshIndex_spec source wire sourceArguments
    sourceSignature newArgument result accepted region index
  have freshLocalExact :
      Fin.cast (arityShift_localCount_exact source wire sourceArguments
          sourceSignature result.sites newArgument result accepted).symm site =
        (arityFreshAt result region).get
          (arityFreshIndex source wire sourceArguments sourceSignature
            newArgument result accepted region index) := by
    have transported := congrArg
      (Fin.cast (arityShift_localCount_exact source wire sourceArguments
        sourceSignature result.sites newArgument result accepted).symm)
      freshPositionExact
    simpa [site, sitePosition, sitesAt] using transported.symm
  have originsExact :
      ConcreteElaboration.variableOrigins result.checked.val
          (targetOuter.extend (result.regionImage region)) targetValues =
        (ConcreteElaboration.variableOrigins source.val
          (sourceOuter.extend region) sourceValues).map result.contextWireMap ++
          [result.targetLocalWire
            ((arityFreshAt result region).get
              (arityFreshIndex source wire sourceArguments sourceSignature
                newArgument result accepted region index))] := by
    calc
      _ = (targetAppliedSite result site).arguments := targetOrigins
      _ = (result.sites.sites.get site).arguments.map
              result.contextWireMap ++
            [result.targetLocalWire
              (Fin.cast (arityShift_localCount_exact source wire
                sourceArguments sourceSignature result.sites newArgument
                result accepted).symm site)] :=
        targetAppliedSite_arguments source wire sourceArguments
          sourceSignature result.sites newArgument result accepted site
      _ = _ := by rw [sourceOrigins, freshLocalExact]
  have splitExact := recursiveNormalizedHole_split_exact_of_origins source wire
    sourceArguments sourceSignature newArgument result accepted region notHead
    sourceOuter targetOuter outer outerOrigin targetNodup
    (arityFreshIndex source wire sourceArguments sourceSignature newArgument
      result accepted region index) sourceValues targetValues originsExact
  rw [targetHoleExact, sourceHoleExact]
  exact splitExact

/-- Assemble a cylindrical-hole receipt from exact ordered lengths, the two
finite order equivalences, and one pointwise split equation.  Root and
descendant arity blocks differ only in how they prove that equation. -/
noncomputable def cylindricalHolesOfSplit
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (sourceOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (freshOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (splitExact : ∀ index : Fin freshCount,
      insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index)) =
        ⟨bounds.freshVar outer (freshOrder index),
          Vars.rename (bounds.embed outer)
            (smaller.get
              (Fin.cast smallerLength.symm (sourceOrder index)))⟩) :
    CylindricalHoles insertion bounds outer smaller larger :=
  { smaller_length := smallerLength
    larger_length := largerLength
    sourceIndex := sourceOrder
    sourceIndex_injective := sourceOrder.injective
    sourceIndex_surjective := fun target =>
      ⟨sourceOrder.invFun target, sourceOrder.right_inv target⟩
    freshIndex := freshOrder
    freshIndex_injective := freshOrder.injective
    freshIndex_surjective := fun target =>
      ⟨freshOrder.invFun target, freshOrder.right_inv target⟩
    inserted_exact := fun index => congrArg Prod.fst (splitExact index)
    retained_exact := fun index => congrArg Prod.snd (splitExact index) }

/-- Complete checker-owned cylindrical-hole receipt for any proper descendant
of the acted head region. -/
noncomputable def recursiveRegionHoles
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (region : source.val.RegionId)
    (notHead : region ≠ (source.val.wires wire).scope)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (targetOuter : ConcreteElaboration.WireContext result.checked.val)
    (outer : WireRenaming sourceOuter.sigs targetOuter.sigs)
    (outerOrigin : ∀ {signature : Sig}
      (value : Var sourceOuter.sigs signature),
      ConcreteElaboration.WireContext.origin result.checked.val
          targetOuter.ids (outer value) =
        result.contextWireMap
          (ConcreteElaboration.WireContext.origin source.val
            sourceOuter.ids value))
    (sourceItems : ItemSeq definitions (sourceOuter.extend region).sigs)
    (targetItems : ItemSeq definitions
      (targetOuter.extend (result.regionImage region)).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (targetOuter.extend (result.regionImage region))
          (result.checked.val.nodesAt (result.regionImage region)) =
        some targetItems)
    (sourceNodup : (sourceOuter.extend region).ids.Nodup)
    (targetNodup :
      (targetOuter.extend (result.regionImage region)).ids.Nodup)
    (sourceHead : Var sourceOuter.sigs (.rel sourceArguments))
    (targetHead : Var targetOuter.sigs (.rel result.targetArguments))
    (sourceHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val sourceOuter.ids
          sourceHead = wire)
    (targetHeadOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val targetOuter.ids
          targetHead = result.targetWire) :
    CylindricalHoles
      (arityShiftInsertion source wire sourceArguments sourceSignature
        newArgument result accepted)
      (arityShift_regionBounds_below source wire sourceArguments
        sourceSignature newArgument result accepted region notHead)
      outer
      (recursiveNormalizedNodeShape sourceOuter region sourceHead
        sourceItems).holeValues
      (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
        targetHead targetItems).holeValues := by
  let lengths := recursiveRegionHole_lengths source wire sourceArguments
    sourceSignature newArgument result accepted sourceOuter targetOuter region
    sourceItems targetItems sourceCompiled targetCompiled sourceNodup
    targetNodup sourceHead targetHead sourceHeadOrigin targetHeadOrigin
  exact cylindricalHolesOfSplit
    (arityShiftInsertion source wire sourceArguments sourceSignature
      newArgument result accepted)
    (arityShift_regionBounds_below source wire sourceArguments
      sourceSignature newArgument result accepted region notHead)
    outer
    (recursiveNormalizedNodeShape sourceOuter region sourceHead
      sourceItems).holeValues
    (recursiveNormalizedNodeShape targetOuter (result.regionImage region)
      targetHead targetItems).holeValues
    lengths.1 lengths.2
    (aritySourceIndex source wire sourceArguments sourceSignature newArgument
      result accepted region)
    (arityFreshIndex source wire sourceArguments sourceSignature newArgument
      result accepted region)
    (recursiveRegionHole_split_exact source wire sourceArguments
      sourceSignature newArgument result accepted region notHead sourceOuter
      targetOuter outer outerOrigin sourceItems targetItems sourceCompiled
      targetCompiled sourceNodup targetNodup sourceHead targetHead
      sourceHeadOrigin targetHeadOrigin)

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
