import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

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
    (result : ArgumentResult source wire)
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
      decide (node ∈ argumentSiteNodes result.sites) := by
  cases classified :
      recursiveRegionClassifier source context region outerHead node with
  | none =>
      simp only [Option.isSome_none]
      symm
      apply decide_eq_false_iff_not.mpr
      intro member
      have sourceNodeMember :
          node ∈ sourceSiteNodesAt result.sites region := by
        apply List.mem_filter.mpr
        exact ⟨nodeAt, decide_eq_true member⟩
      have orderedMember :=
        (aritySiteNodesAt_mem_iff result.sites region node).mpr
          sourceNodeMember
      obtain ⟨siteIndex, siteIndexMember, nodeExact⟩ :=
        List.mem_map.mp orderedMember
      have siteRegion :
          (result.sites.sites.get siteIndex).region = region := by
        exact eq_of_beq (List.mem_filter.mp siteIndexMember).2
      obtain ⟨arguments, selected, _origins⟩ :=
        recursiveRegionClassifier_complete sourceArguments sourceSignature
          context region items compiled contextNodup outerHead outerHeadOrigin
          (result.sites.sites.get siteIndex) siteRegion
      rw [nodeExact, classified] at selected
      contradiction
  | some values =>
      simp only [Option.isSome_some]
      symm
      apply decide_eq_true
      obtain ⟨site, siteMember, nodeExact⟩ :=
        recursiveRegionClassifier_site result.sites context region outerHead
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
    (result : ArgumentResult source wire)
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
      (sourceSiteNodesAt result.sites region).map
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
  exact recursiveRegionClassifier_isSome sourceArguments sourceSignature result
    context region items compiled contextNodup outerHead outerHeadOrigin node
    nodeAt

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

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
