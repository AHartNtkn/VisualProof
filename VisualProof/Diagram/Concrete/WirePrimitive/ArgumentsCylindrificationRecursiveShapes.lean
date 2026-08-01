import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveHoles

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

/-- Ordinary projection of a uniform region. -/
def recursiveOrdinary :
    UniformIntrinsicRegion definitions arguments context →
      UniformIntrinsicItemSeq definitions arguments context
  | .mk ordinary _ => ordinary

/-- Regard a compiled item sequence as a uniform sequence containing only
ordinary leaves. -/
def recursiveLeafItems :
    ItemSeq definitions context →
      UniformIntrinsicItemSeq definitions arguments context
  | .nil => .nil
  | .cons head tail => .cons (.leaf head) (recursiveLeafItems tail)

/-- The ordinary item sequence obtained by removing every direct matching
application from one compiled sequence. -/
def recursiveAbstractOrdinaryItems
    (head : Var context (.rel arguments)) :
    ItemSeq definitions context →
      UniformIntrinsicItemSeq definitions arguments context
  | .nil => .nil
  | .cons item tail =>
      let rest := recursiveAbstractOrdinaryItems head tail
      match item with
      | .atom atomHead values =>
          match UniformIntrinsicRegion.matchedHeadArguments? head atomHead values with
          | some _ => rest
          | none => .cons (.leaf (.atom atomHead values)) rest
      | .named definition values =>
          .cons (.leaf (.named definition values)) rest
      | .identity signature ports atLeastTwo =>
          .cons (.leaf (.identity signature ports atLeastTwo)) rest
      | .cut body =>
          .cons (.cut (UniformIntrinsicRegion.abstractApplied head body)) rest
      | .bind signature body =>
          .cons (.bind signature
            (UniformIntrinsicRegion.abstractApplied head.there body)) rest

/-- The explicit ordinary-item recursion is definitionally faithful to the
authoritative uniform abstraction. -/
theorem recursiveOrdinary_abstractAppliedItems
    (head : Var context (.rel arguments)) :
    ∀ items : ItemSeq definitions context,
      recursiveOrdinary
          (UniformIntrinsicRegion.abstractAppliedItems head items) =
        recursiveAbstractOrdinaryItems head items
  | .nil => rfl
  | .cons item tail => by
      have induction := recursiveOrdinary_abstractAppliedItems head tail
      cases abstracted :
          UniformIntrinsicRegion.abstractAppliedItems head tail with
      | mk ordinary holes =>
          rw [abstracted] at induction
          change ordinary = _ at induction
          cases item with
          | atom atomHead values =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              cases matched : UniformIntrinsicRegion.matchedHeadArguments?
                  head atomHead values with
              | none =>
                simp only [matched, recursiveAbstractOrdinaryItems]
                exact congrArg
                  (UniformIntrinsicItemSeq.cons (.leaf (.atom atomHead values)))
                  induction
              | some matchedValues =>
                simp only [matched, recursiveAbstractOrdinaryItems]
                exact induction
          | named definition values =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.leaf (.named definition values)) ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.leaf (.named definition values))) induction
          | identity signature ports atLeastTwo =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.leaf (.identity signature ports atLeastTwo)) ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.leaf (.identity signature ports atLeastTwo))) induction
          | cut body =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.cut (UniformIntrinsicRegion.abstractApplied head body))
                ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.cut (UniformIntrinsicRegion.abstractApplied head body)))
                  induction
          | bind signature body =>
              simp only [UniformIntrinsicRegion.abstractAppliedItems]
              rw [abstracted]
              change UniformIntrinsicItemSeq.cons
                (.bind signature
                  (UniformIntrinsicRegion.abstractApplied head.there body))
                ordinary = _
              exact congrArg (UniformIntrinsicItemSeq.cons
                (.bind signature
                  (UniformIntrinsicRegion.abstractApplied head.there body)))
                induction

/-- Concrete node compilation emits only atom, named, or identity items;
cuts and binds are owned by region/child compilation. -/
theorem compileNode?_ordinary_kind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (item : Item definitions context.sigs)
    (compiled : ConcreteElaboration.Internal.compileNode? definitions diagram
      context node = some item) :
    match item with
    | .atom .. => True
    | .named .. => True
    | .identity .. => True
    | .cut .. => False
    | .bind .. => False := by
  cases nodeData : diagram.nodes node with
  | atom region arguments =>
      simp only [ConcreteElaboration.Internal.compileNode?, nodeData] at compiled
      cases headResolved : ConcreteElaboration.Internal.resolvePort? diagram
          context node .head (.rel arguments) with
      | none => simp [headResolved] at compiled
      | some atomHead =>
          cases argumentsResolved :
              ConcreteElaboration.Internal.resolveArgs? diagram context node
                arguments 0 with
          | none => simp [headResolved, argumentsResolved] at compiled
          | some values =>
              have exact : item = .atom atomHead values := by
                exact (Option.some.inj (by
                  simpa [headResolved, argumentsResolved] using compiled)).symm
              subst item
              trivial
  | ref region definition arguments =>
      simp only [ConcreteElaboration.Internal.compileNode?, nodeData] at compiled
      split at compiled
      next signature =>
        cases argumentsResolved :
            ConcreteElaboration.Internal.resolveArgs? diagram context node
              arguments 0 with
        | none => simp [argumentsResolved] at compiled
        | some values =>
            have exact : item = .named
                (signature ▸ ConcreteElaboration.Internal.definitionVarAt
                  definitions definition) values := by
              exact (Option.some.inj (by
                simpa [argumentsResolved] using compiled)).symm
            subst item
            trivial
      next signature => simp at compiled
  | identity region signature arity =>
      simp only [ConcreteElaboration.Internal.compileNode?, nodeData] at compiled
      split at compiled
      next arityWitness =>
        cases portsResolved :
            ConcreteElaboration.Internal.resolveIdentityPorts? diagram context
              node signature arity 0 with
        | none => simp [portsResolved] at compiled
        | some ports =>
            have itemExact :
                (.identity signature ports.val (by
                  simpa only [ports.property] using arityWitness) :
                    Item definitions context.sigs) = item := by
              exact Option.some.inj (by
                simpa [portsResolved] using compiled)
            cases itemExact
            trivial
      next arityWitness => simp at compiled

/-- Filtering the concrete nodes selected by the normalized application
classifier gives exactly the ordinary leaves left by abstraction. -/
theorem recursiveAbstractOrdinaryItems_compileFilter
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (rho : WireRenaming context.sigs normalizedContext)
    (head : Var normalizedContext (.rel arguments))
    (selectedNodes : List diagram.NodeId) :
    ∀ (nodes : List diagram.NodeId)
      (items : ItemSeq definitions context.sigs)
      (retained : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
      ConcreteElaboration.compileNodes? definitions diagram context
          (nodes.filter fun node => !decide (node ∈ selectedNodes)) =
          some retained →
      (∀ node, node ∈ nodes →
        (UniformIntrinsicRegion.renamedCompiledAppliedArguments? definitions
          diagram context rho head node).isSome =
            decide (node ∈ selectedNodes)) →
      recursiveAbstractOrdinaryItems head (items.renameWires rho) =
        recursiveLeafItems (retained.renameWires rho)
  | [], items, retained, compiled, retainedCompiled, _ => by
      simp [ConcreteElaboration.compileNodes?] at compiled retainedCompiled
      subst items
      subst retained
      rfl
  | node :: tail, items, retained, compiled, retainedCompiled, classified => by
      simp only [ConcreteElaboration.compileNodes?] at compiled
      cases headCompiled :
          ConcreteElaboration.Internal.compileNode? definitions diagram
            context node with
      | none => simp [headCompiled] at compiled
      | some compiledHead =>
          cases tailCompiled :
              ConcreteElaboration.compileNodes? definitions diagram context
                tail with
          | none => simp [headCompiled, tailCompiled] at compiled
          | some compiledTail =>
              have itemsExact :
                  items = .cons compiledHead compiledTail := by
                exact (Option.some.inj (by
                  simpa [headCompiled, tailCompiled] using compiled)).symm
              subst items
              have headClassified := classified node (by simp)
              have tailClassified : ∀ candidate, candidate ∈ tail →
                  (UniformIntrinsicRegion.renamedCompiledAppliedArguments?
                    definitions diagram context rho head candidate).isSome =
                      decide (candidate ∈ selectedNodes) := by
                intro candidate member
                exact classified candidate (by simp [member])
              by_cases selected : node ∈ selectedNodes
              · have retainedTailCompiled :
                    ConcreteElaboration.compileNodes? definitions diagram
                        context
                        (tail.filter fun candidate =>
                          !decide (candidate ∈ selectedNodes)) =
                      some retained := by
                    simpa [selected] using retainedCompiled
                have induction :=
                  recursiveAbstractOrdinaryItems_compileFilter definitions
                    diagram context rho head selectedNodes tail compiledTail
                    retained tailCompiled retainedTailCompiled tailClassified
                simp [UniformIntrinsicRegion.renamedCompiledAppliedArguments?,
                  headCompiled, selected] at headClassified
                cases compiledHead with
                | atom atomHead values =>
                    cases matched :
                        UniformIntrinsicRegion.matchedHeadArguments? head
                          (rho atomHead) (Vars.rename rho values) with
                    | none => simp [matched] at headClassified
                    | some applied =>
                        simpa [ItemSeq.renameWires, Item.renameWires,
                          recursiveAbstractOrdinaryItems, matched] using induction
                | named definition values => simp at headClassified
                | identity signature ports atLeastTwo => simp at headClassified
                | cut body => simp at headClassified
                | bind signature body => simp at headClassified
              · simp [selected] at retainedCompiled
                simp only [ConcreteElaboration.compileNodes?] at retainedCompiled
                cases retainedTailCompiled :
                    ConcreteElaboration.compileNodes? definitions diagram
                      context
                      (tail.filter fun candidate =>
                        !decide (candidate ∈ selectedNodes)) with
                | none =>
                    simp [headCompiled, retainedTailCompiled] at retainedCompiled
                | some retainedTail =>
                    have retainedExact :
                        retained = .cons compiledHead retainedTail := by
                      exact (Option.some.inj (by
                        simpa [headCompiled, retainedTailCompiled] using
                          retainedCompiled)).symm
                    subst retained
                    have induction :=
                      recursiveAbstractOrdinaryItems_compileFilter definitions
                        diagram context rho head selectedNodes tail compiledTail
                        retainedTail tailCompiled retainedTailCompiled
                        tailClassified
                    simp [UniformIntrinsicRegion.renamedCompiledAppliedArguments?,
                      headCompiled, selected] at headClassified
                    cases compiledHead with
                    | atom atomHead values =>
                        cases matched :
                            UniformIntrinsicRegion.matchedHeadArguments? head
                              (rho atomHead) (Vars.rename rho values) with
                        | none =>
                            simpa [ItemSeq.renameWires, Item.renameWires,
                              recursiveAbstractOrdinaryItems,
                              recursiveLeafItems, matched] using congrArg
                                (UniformIntrinsicItemSeq.cons
                                  (.leaf (.atom (rho atomHead)
                                    (Vars.rename rho values)))) induction
                        | some applied => simp [matched] at headClassified
                    | named definition values =>
                        simpa [ItemSeq.renameWires, Item.renameWires,
                          recursiveAbstractOrdinaryItems,
                          recursiveLeafItems] using congrArg
                            (UniformIntrinsicItemSeq.cons
                              (.leaf (.named definition
                                (Vars.rename rho values)))) induction
                    | identity signature ports atLeastTwo =>
                        simpa [ItemSeq.renameWires, Item.renameWires,
                          recursiveAbstractOrdinaryItems,
                          recursiveLeafItems] using congrArg
                            (UniformIntrinsicItemSeq.cons
                              (.leaf (.identity signature
                                (ports.map (rho (sig := signature))) (by
                                  simpa using atLeastTwo)))) induction
                    | cut body =>
                        exact (compileNode?_ordinary_kind definitions diagram
                          context node (.cut body) headCompiled).elim
                    | bind signature body =>
                        exact (compileNode?_ordinary_kind definitions diagram
                          context node (.bind signature body)
                          headCompiled).elim

/-- Removing target application nodes leaves exactly the retained-node prefix
at every image region. -/
theorem ArgumentResult.targetRetainedNodesAt_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId) :
    (result.checked.val.nodesAt (result.regionImage region)).filter
        (fun node => !decide
          (node ∈ argumentSiteNodes result.targetSites)) =
      ((replacementBase result.plan).nodesAt
          (retainedRegion source region)).map (fun retained =>
        ConcreteWireQuantifier.Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length retained)) := by
  rw [result.nodesAt_decomposition region, List.filter_append]
  have retainedExact :
      (((replacementBase result.plan).nodesAt
          (retainedRegion source region)).map (fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained))).filter
        (fun node => !decide
          (node ∈ argumentSiteNodes result.targetSites)) =
      ((replacementBase result.plan).nodesAt
          (retainedRegion source region)).map (fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) := by
    apply List.filter_eq_self.mpr
    intro node member
    obtain ⟨retained, _retainedMember, nodeExact⟩ := List.mem_map.mp member
    have below : ¬(replacementBase result.plan).nodeCount ≤ node.val := by
      rw [← nodeExact]
      simp [ConcreteWireQuantifier.Internal.checkedNode]
    have notSite : node ∉ argumentSiteNodes result.targetSites := by
      intro site
      exact below ((result.targetSiteNode_iff_ge result.targetSites node).mp site)
    simp [notSite]
  rw [retainedExact]
  have generatedEmpty :
      (((Data.Finite.allFin result.sites.sites.length).filter fun site =>
          retainedRegion source (result.sites.sites.get site).region ==
            retainedRegion source region).map result.targetNode).filter
        (fun node => !decide
          (node ∈ argumentSiteNodes result.targetSites)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node member kept
    obtain ⟨site, _siteMember, nodeExact⟩ := List.mem_map.mp member
    have generatedSite : node ∈ argumentSiteNodes result.targetSites := by
      rw [← nodeExact]
      exact result.generatedNode_targetSiteNode result.targetSites site
    simpa [generatedSite] using kept
  rw [generatedEmpty, List.append_nil]

/-- The ordinary part of an arbitrary normalized source node body is the
normalized compilation of precisely its retained source nodes. -/
theorem recursiveSourceOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (sites : AllAppliedSites source wire)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items retained : ItemSeq definitions (context.extend region).sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) = some items)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes sites)) = some retained)
    (contextNodup : (context.extend region).ids.Nodup)
    (outerHead : Var context.sigs (.rel sourceArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids outerHead =
        wire) :
    recursiveOrdinary
        (recursiveNormalizedNodeShape context region outerHead items) =
      recursiveLeafItems
        (retained.renameWires (recursiveRegionNormalization context region)) := by
  unfold recursiveNormalizedNodeShape
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions source.val
    (context.extend region) (recursiveRegionNormalization context region)
    (Var.appendRight
      ((source.val.wiresAt region).map fun localWire =>
        (source.val.wires localWire).sig) outerHead)
    (argumentSiteNodes sites) (source.val.nodesAt region) items retained compiled
  · simpa using retainedCompiled
  · intro node nodeAt
    exact recursiveRegionClassifier_isSome sourceArguments sourceSignature sites
      context region items compiled contextNodup outerHead outerHeadOrigin node
      nodeAt

/-- The ordinary part of an arbitrary normalized target node body is the
normalized compilation of its retained prefix; generated site nodes are
removed by abstraction. -/
theorem recursiveTargetOrdinary_eq_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (context : ConcreteElaboration.WireContext result.checked.val)
    (region : source.val.RegionId)
    (items retained : ItemSeq definitions
      (context.extend (result.regionImage region)).sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (context.extend (result.regionImage region))
          (result.checked.val.nodesAt (result.regionImage region)) = some items)
    (retainedCompiled :
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (context.extend (result.regionImage region))
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map (fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained))) =
        some retained)
    (contextNodup :
      (context.extend (result.regionImage region)).ids.Nodup)
    (outerHead : Var context.sigs (.rel result.targetArguments))
    (outerHeadOrigin :
      ConcreteElaboration.WireContext.origin result.checked.val context.ids
          outerHead = result.targetWire) :
    recursiveOrdinary
        (recursiveNormalizedNodeShape context (result.regionImage region)
          outerHead items) =
      recursiveLeafItems (retained.renameWires
        (recursiveRegionNormalization context (result.regionImage region))) := by
  unfold recursiveNormalizedNodeShape
  rw [recursiveOrdinary_abstractAppliedItems]
  apply recursiveAbstractOrdinaryItems_compileFilter definitions
    result.checked.val (context.extend (result.regionImage region))
    (recursiveRegionNormalization context (result.regionImage region))
    (Var.appendRight
      ((result.checked.val.wiresAt (result.regionImage region)).map fun localWire =>
        (result.checked.val.wires localWire).sig) outerHead)
    (argumentSiteNodes result.targetSites)
    (result.checked.val.nodesAt (result.regionImage region)) items retained
    compiled
  · rw [ArgumentResult.targetRetainedNodesAt_exact result region]
    exact retainedCompiled
  · intro node nodeAt
    exact recursiveRegionClassifier_isSome result.targetArguments
      result.targetWire_signature result.targetSites context
      (result.regionImage region) items compiled contextNodup outerHead
      outerHeadOrigin node nodeAt

/-- Typed tuples respect pointwise composition of wire actions. -/
theorem recursiveVarsRename_comp
    (first : WireRenaming source middle)
    (second : WireRenaming middle target)
    (combined : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      second (first value) = combined value) :
    ∀ values : Vars source arguments,
      Vars.rename second (Vars.rename first values) =
        Vars.rename combined values
  | .nil => rfl
  | .cons head tail => by
      simp only [Vars.rename]
      rw [pointwise head,
        recursiveVarsRename_comp first second combined pointwise tail]

mutual

/-- Intrinsic regions respect pointwise composition of wire actions. -/
theorem recursiveRegionRename_comp
    (first : WireRenaming source middle)
    (second : WireRenaming middle target)
    (combined : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      second (first value) = combined value) :
    ∀ body : Region definitions source,
      (body.renameWires first).renameWires second =
        body.renameWires combined
  | .mk items => by
      exact congrArg Region.mk
        (recursiveItemSeqRename_comp first second combined pointwise items)

/-- Intrinsic items respect pointwise composition of wire actions. -/
theorem recursiveItemRename_comp
    (first : WireRenaming source middle)
    (second : WireRenaming middle target)
    (combined : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      second (first value) = combined value) :
    ∀ item : Item definitions source,
      (item.renameWires first).renameWires second =
        item.renameWires combined
  | .atom head values => by
      simp only [Item.renameWires]
      rw [pointwise head,
        recursiveVarsRename_comp first second combined pointwise values]
  | .named definition values => by
      simp only [Item.renameWires]
      rw [recursiveVarsRename_comp first second combined pointwise values]
  | .identity signature ports atLeastTwo => by
      simp only [Item.renameWires]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro value _member
      exact pointwise value
  | .cut body => by
      exact congrArg Item.cut
        (recursiveRegionRename_comp first second combined pointwise body)
  | .bind signature body => by
      apply congrArg (Item.bind signature)
      apply recursiveRegionRename_comp
      intro valueSignature value
      cases value with
      | here => rfl
      | there outer => exact congrArg Var.there (pointwise outer)

/-- Intrinsic item sequences respect pointwise composition of wire actions. -/
theorem recursiveItemSeqRename_comp
    (first : WireRenaming source middle)
    (second : WireRenaming middle target)
    (combined : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      second (first value) = combined value) :
    ∀ items : ItemSeq definitions source,
      (items.renameWires first).renameWires second =
        items.renameWires combined
  | .nil => rfl
  | .cons head tail => by
      simp only [ItemSeq.renameWires]
      rw [recursiveItemRename_comp first second combined pointwise head,
        recursiveItemSeqRename_comp first second combined pointwise tail]

end

/-- Typed tuples depend only on the pointwise wire action. -/
theorem recursiveVarsRename_eq
    (left right : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      left value = right value) :
    ∀ values : Vars source arguments,
      Vars.rename left values = Vars.rename right values
  | .nil => rfl
  | .cons head tail => by
      simp only [Vars.rename]
      rw [pointwise head,
        recursiveVarsRename_eq left right pointwise tail]

mutual

/-- Intrinsic regions depend only on the pointwise wire action. -/
theorem recursiveRegionRename_eq
    (left right : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      left value = right value) :
    ∀ body : Region definitions source,
      body.renameWires left = body.renameWires right
  | .mk items => by
      exact congrArg Region.mk
        (recursiveItemSeqRename_eq left right pointwise items)

/-- Intrinsic items depend only on the pointwise wire action. -/
theorem recursiveItemRename_eq
    (left right : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      left value = right value) :
    ∀ item : Item definitions source,
      item.renameWires left = item.renameWires right
  | .atom head values => by
      simp only [Item.renameWires]
      rw [pointwise head,
        recursiveVarsRename_eq left right pointwise values]
  | .named definition values => by
      simp only [Item.renameWires]
      rw [recursiveVarsRename_eq left right pointwise values]
  | .identity signature ports atLeastTwo => by
      simp only [Item.renameWires]
      congr 1
      apply List.map_congr_left
      intro value _member
      exact pointwise value
  | .cut body => by
      exact congrArg Item.cut
        (recursiveRegionRename_eq left right pointwise body)
  | .bind signature body => by
      apply congrArg (Item.bind signature)
      apply recursiveRegionRename_eq
      intro valueSignature value
      cases value with
      | here => rfl
      | there outer => exact congrArg Var.there (pointwise outer)

/-- Intrinsic item sequences depend only on the pointwise wire action. -/
theorem recursiveItemSeqRename_eq
    (left right : WireRenaming source target)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      left value = right value) :
    ∀ items : ItemSeq definitions source,
      items.renameWires left = items.renameWires right
  | .nil => rfl
  | .cons head tail => by
      simp only [ItemSeq.renameWires]
      rw [recursiveItemRename_eq left right pointwise head,
        recursiveItemSeqRename_eq left right pointwise tail]

end

/-- Renaming a typed tuple by the identity action is inert. -/
theorem recursiveVarsRename_id
    (values : Vars context arguments) :
    Vars.rename (fun {_} value => value) values = values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.rename]
      rw [induction]

mutual

/-- Renaming an intrinsic region by the identity action is inert. -/
theorem recursiveRegionRename_id :
    ∀ body : Region definitions context,
      body.renameWires (fun {_} value => value) = body
  | .mk items => by
      exact congrArg Region.mk (recursiveItemSeqRename_id items)

/-- Renaming an intrinsic item by the identity action is inert. -/
theorem recursiveItemRename_id :
    ∀ item : Item definitions context,
      item.renameWires (fun {_} value => value) = item
  | .atom head values => by
      simp only [Item.renameWires]
      rw [recursiveVarsRename_id values]
  | .named definition values => by
      simp only [Item.renameWires]
      rw [recursiveVarsRename_id values]
  | .identity signature ports atLeastTwo => by
      simp only [Item.renameWires]
      congr 1
      simp
  | .cut body => by
      exact congrArg Item.cut (recursiveRegionRename_id body)
  | .bind signature body => by
      apply congrArg (Item.bind signature)
      calc
        _ = body.renameWires (fun {_} value => value) :=
          recursiveRegionRename_eq _ _ (by
            intro valueSignature value
            cases value <;> rfl) body
        _ = body := recursiveRegionRename_id body

/-- Renaming an intrinsic item sequence by the identity action is inert. -/
theorem recursiveItemSeqRename_id :
    ∀ items : ItemSeq definitions context,
      items.renameWires (fun {_} value => value) = items
  | .nil => rfl
  | .cons head tail => by
      simp only [ItemSeq.renameWires]
      rw [recursiveItemRename_id head, recursiveItemSeqRename_id tail]

end

/-- Any decidable ordered subsequence of a successfully compiled node list
also compiles, preserving the retained node order. -/
theorem compileNodes?_filter_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (keep : diagram.NodeId → Bool) :
    ∀ (nodes : List diagram.NodeId)
      (items : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
      ∃ retained,
        ConcreteElaboration.compileNodes? definitions diagram context
          (nodes.filter keep) = some retained
  | [], items, compiled => by
      simp [ConcreteElaboration.compileNodes?] at compiled
      subst items
      exact ⟨.nil, rfl⟩
  | node :: tail, items, compiled => by
      simp only [ConcreteElaboration.compileNodes?] at compiled
      cases headCompiled :
          ConcreteElaboration.Internal.compileNode? definitions diagram
            context node with
      | none => simp [headCompiled] at compiled
      | some head =>
          cases tailCompiled :
              ConcreteElaboration.compileNodes? definitions diagram context
                tail with
          | none => simp [headCompiled, tailCompiled] at compiled
          | some rest =>
              obtain ⟨retained, retainedCompiled⟩ :=
                compileNodes?_filter_complete definitions diagram context keep
                  tail rest tailCompiled
              cases kept : keep node with
              | false =>
                  exact ⟨retained, by
                    simpa [List.filter_cons, kept] using retainedCompiled⟩
              | true =>
                  exact ⟨.cons head retained, by
                    simp [List.filter_cons, kept,
                      ConcreteElaboration.compileNodes?, headCompiled,
                      retainedCompiled]⟩

/-- Retained source and target node compilations below the acted head are
paired by the exact normalized block embedding. -/
theorem recursiveRetainedNodePair
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
    (sourceItems : ItemSeq definitions (sourceOuter.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend region) (source.val.nodesAt region) =
        some sourceItems) :
    ∃ (sourceRetained : ItemSeq definitions
          (sourceOuter.extend region).sigs)
      (targetRetained : ItemSeq definitions
          (targetOuter.extend (result.regionImage region)).sigs),
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend region)
          ((source.val.nodesAt region).filter fun node =>
            decide (node ∉ argumentSiteNodes result.sites)) =
        some sourceRetained ∧
      ConcreteElaboration.compileNodes? definitions result.checked.val
          (targetOuter.extend (result.regionImage region))
          (((replacementBase result.plan).nodesAt
              (retainedRegion source region)).map fun retained =>
            ConcreteWireQuantifier.Internal.checkedNode result.generated
              (Fin.castAdd result.sites.sites.length retained)) =
        some targetRetained ∧
      targetRetained.renameWires
          (recursiveRegionNormalization targetOuter
            (result.regionImage region)) =
        (sourceRetained.renameWires
            (recursiveRegionNormalization sourceOuter region)).renameWires
          ((arityShift_regionBounds_below source wire sourceArguments
            sourceSignature newArgument result accepted region notHead).embed
              outer) := by
  obtain ⟨sourceRetained, sourceRetainedCompiled⟩ :=
    compileNodes?_filter_complete definitions source.val
      (sourceOuter.extend region)
      (fun node => decide (node ∉ argumentSiteNodes result.sites))
      (source.val.nodesAt region) sourceItems sourceCompiled
  obtain ⟨targetRetained, targetRetainedCompiled, targetRawExact⟩ :=
    arityShift_compileNodes_below_natural source wire sourceArguments
      sourceSignature newArgument result accepted region notHead sourceOuter
      targetOuter outer outerOrigin targetNodup
      (ArgumentResult.RetainedContext.nodesAt_retainedPrefix result region)
      sourceRetainedCompiled
  refine ⟨sourceRetained, targetRetained, sourceRetainedCompiled,
    targetRetainedCompiled, ?_⟩
  subst targetRetained
  let raw : WireRenaming (sourceOuter.extend region).sigs
      (targetOuter.extend (result.regionImage region)).sigs :=
    arityShift_regionEmbedding_below source wire sourceArguments
      sourceSignature newArgument result accepted region notHead sourceOuter
      targetOuter outer
  let block : WireRenaming
      (((source.val.wiresAt region).map fun localWire =>
          (source.val.wires localWire).sig) ++ sourceOuter.sigs)
      (((result.checked.val.wiresAt (result.regionImage region)).map fun
          localWire => (result.checked.val.wires localWire).sig) ++
        targetOuter.sigs) :=
    (arityShift_regionBounds_below source wire sourceArguments
      sourceSignature newArgument result accepted region notHead).embed outer
  let combined : WireRenaming (sourceOuter.extend region).sigs
      (((result.checked.val.wiresAt (result.regionImage region)).map fun
        localWire => (result.checked.val.wires localWire).sig) ++
          targetOuter.sigs) :=
    fun {_} value => recursiveRegionNormalization targetOuter
      (result.regionImage region) (raw value)
  calc
    _ = sourceRetained.renameWires combined :=
      recursiveItemSeqRename_comp raw
        (recursiveRegionNormalization targetOuter (result.regionImage region))
        combined (fun _ => rfl) sourceRetained
    _ = _ := (recursiveItemSeqRename_comp
      (recursiveRegionNormalization sourceOuter region) block combined (by
        intro signature value
        exact (recursiveRegionNormalizations_commute source wire
          sourceArguments sourceSignature newArgument result accepted region
          notHead sourceOuter targetOuter outer value).symm) sourceRetained).symm

/-- Abstraction commutes with the intrinsic signature-only region finisher:
local compiler wires become the same ordered block of uniform binders. -/
theorem recursiveAbstract_finishRegionSignatures
    (outerHead : Var outer (.rel arguments)) :
    ∀ (localSigs : List Sig)
      (body : Region definitions (localSigs ++ outer)),
      UniformIntrinsicRegion.abstractApplied outerHead
          (ConcreteElaboration.finishRegionSignatures outer localSigs body) =
        wrapArgumentBinds localSigs
          (UniformIntrinsicRegion.abstractApplied
            (Var.appendRight localSigs outerHead) body)
  | [], body => rfl
  | signature :: tail, body => by
      simp only [ConcreteElaboration.finishRegionSignatures,
        wrapArgumentBinds]
      rw [recursiveAbstract_finishRegionSignatures outerHead tail]
      rfl

/-- Keep an explicit binder prefix fixed while changing only the true outer
context. -/
def recursiveLiftOuterRenaming (bound : List Sig)
    (outer : WireRenaming source target) :
    WireRenaming (bound ++ source) (bound ++ target) :=
  match bound with
  | [] => outer
  | signature :: rest =>
      WireRenaming.lift (recursiveLiftOuterRenaming rest outer) signature

@[simp] theorem recursiveLiftOuterRenaming_appendLeft
    (bound : List Sig) (outer : WireRenaming source target)
    (value : Var bound signature) :
    recursiveLiftOuterRenaming bound outer
        (Var.appendLeft value source) =
      Var.appendLeft value target := by
  induction value with
  | here => rfl
  | there tail induction =>
      exact congrArg Var.there induction

@[simp] theorem recursiveLiftOuterRenaming_appendRight
    (bound : List Sig) (outer : WireRenaming source target)
    (value : Var source signature) :
    recursiveLiftOuterRenaming bound outer
        (Var.appendRight bound value) =
      Var.appendRight bound (outer value) := by
  induction bound with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg Var.there induction

/-- A bound cylindrification is natural in its true outer context. -/
theorem recursiveBoundEmbed_natural
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (oldOuter : WireRenaming smallerOuter largerOuter)
    (sourceRenaming : WireRenaming smallerOuter normalizedSmallerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerOuter signature),
      newOuter (sourceRenaming value) = targetRenaming (oldOuter value)) :
    ∀ {signature : Sig}
      (value : Var (smallerBound ++ smallerOuter) signature),
      recursiveLiftOuterRenaming largerBound targetRenaming
          (bounds.embed oldOuter value) =
        bounds.embed newOuter
          (recursiveLiftOuterRenaming smallerBound sourceRenaming value) := by
  intro signature value
  induction bounds with
  | nil =>
      simpa [recursiveLiftOuterRenaming, BoundCylindrification.embed] using
        (commutes value).symm
  | retained bound rest induction =>
      cases value with
      | here => rfl
      | there outer => exact congrArg Var.there (induction outer)
  | fresh rest induction =>
      exact congrArg Var.there (induction value)

/-- Fresh binder coordinates are unaffected by a change of true outer
context. -/
theorem recursiveBoundFresh_natural
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (oldOuter : WireRenaming smallerOuter largerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter) :
    ∀ index : Fin freshCount,
      recursiveLiftOuterRenaming largerBound targetRenaming
          (bounds.freshVar oldOuter index) =
        bounds.freshVar newOuter index := by
  induction bounds with
  | nil =>
      intro index
      exact Fin.elim0 index
  | retained bound rest induction =>
      intro index
      exact congrArg Var.there (induction index)
  | fresh rest induction =>
      intro index
      cases index using Fin.cases with
      | zero => rfl
      | succ tail => exact congrArg Var.there (induction tail)

/-- Reindex a complete cylindrical hole receipt while keeping its bound
coordinates fixed and changing only the true outer contexts. -/
noncomputable def recursiveReindexHoles
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (oldOuter : WireRenaming smallerOuter largerOuter)
    (sourceRenaming : WireRenaming smallerOuter normalizedSmallerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerOuter signature),
      newOuter (sourceRenaming value) = targetRenaming (oldOuter value))
    {smaller : List
      (Vars (smallerBound ++ smallerOuter) smallerArguments)}
    {larger : List
      (Vars (largerBound ++ largerOuter) largerArguments)}
    (holes : CylindricalHoles insertion bounds oldOuter smaller larger) :
    CylindricalHoles insertion bounds newOuter
      (smaller.map fun values => Vars.rename
        (recursiveLiftOuterRenaming smallerBound sourceRenaming) values)
      (larger.map fun values => Vars.rename
        (recursiveLiftOuterRenaming largerBound targetRenaming) values) := by
  let sourceMap : WireRenaming (smallerBound ++ smallerOuter)
      (smallerBound ++ normalizedSmallerOuter) :=
    recursiveLiftOuterRenaming smallerBound sourceRenaming
  let targetMap : WireRenaming (largerBound ++ largerOuter)
      (largerBound ++ normalizedLargerOuter) :=
    recursiveLiftOuterRenaming largerBound targetRenaming
  have smallerLength :
      (smaller.map fun values => Vars.rename sourceMap values).length =
        freshCount := by simpa [sourceMap] using holes.smaller_length
  have largerLength :
      (larger.map fun values => Vars.rename targetMap values).length =
        freshCount := by simpa [targetMap] using holes.larger_length
  refine
    { smaller_length := smallerLength
      larger_length := largerLength
      sourceIndex := holes.sourceIndex
      sourceIndex_injective := holes.sourceIndex_injective
      sourceIndex_surjective := holes.sourceIndex_surjective
      freshIndex := holes.freshIndex
      freshIndex_injective := holes.freshIndex_injective
      freshIndex_surjective := holes.freshIndex_surjective
      inserted_exact := ?_
      retained_exact := ?_ }
  · intro index
    simp only [List.get_eq_getElem, List.getElem_map,
      TypedArguments.InsertionEvidence.splitVars_rename]
    change targetMap
        (insertion.splitVars
          (larger.get (Fin.cast holes.larger_length.symm index))).1 = _
    rw [holes.inserted_exact]
    exact recursiveBoundFresh_natural bounds oldOuter targetRenaming newOuter
      (holes.freshIndex index)
  · intro index
    simp only [List.get_eq_getElem, List.getElem_map,
      TypedArguments.InsertionEvidence.splitVars_rename]
    change Vars.rename targetMap
        (insertion.splitVars
          (larger.get (Fin.cast holes.larger_length.symm index))).2 =
      Vars.rename (bounds.embed newOuter)
        (Vars.rename sourceMap
          (smaller.get (Fin.cast holes.smaller_length.symm
            (holes.sourceIndex index))))
    rw [holes.retained_exact]
    let selected := smaller.get (Fin.cast holes.smaller_length.symm
      (holes.sourceIndex index))
    let combined : WireRenaming (smallerBound ++ smallerOuter)
        (largerBound ++ normalizedLargerOuter) :=
      fun {_} value => targetMap (bounds.embed oldOuter value)
    calc
      Vars.rename targetMap
          (Vars.rename (bounds.embed oldOuter) selected) =
        Vars.rename combined selected :=
          recursiveVarsRename_comp (bounds.embed oldOuter) targetMap combined
            (fun _ => rfl) selected
      _ = Vars.rename
          (fun {_} value => bounds.embed newOuter (sourceMap value))
          selected := recursiveVarsRename_eq _ _ (by
            intro signature value
            exact recursiveBoundEmbed_natural bounds oldOuter sourceRenaming
              targetRenaming newOuter commutes value) selected
      _ = Vars.rename (bounds.embed newOuter)
          (Vars.rename sourceMap selected) :=
        (recursiveVarsRename_comp sourceMap (bounds.embed newOuter)
          (fun {_} value => bounds.embed newOuter (sourceMap value))
          (fun _ => rfl) selected).symm

mutual

/-- Reindex a consistent cylindrical shape along commuting source and target
context maps. -/
noncomputable def recursiveReindexShape
    (sourceRenaming : WireRenaming smallerOuter normalizedSmallerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter)
    (shape : CylindricalShape definitions insertion smallerOuter largerOuter)
    (consistent : shape.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerOuter signature),
      newOuter (sourceRenaming value) =
        targetRenaming (shape.embedding value)) :
    CylindricalShape definitions insertion normalizedSmallerOuter
      normalizedLargerOuter :=
  match shape with
  | .block (smallerBound := smallerBound) (largerBound := largerBound)
      oldOuter bounds items holes =>
      let sourceMap : WireRenaming (smallerBound ++ smallerOuter)
          (smallerBound ++ normalizedSmallerOuter) :=
        recursiveLiftOuterRenaming smallerBound sourceRenaming
      let targetMap : WireRenaming (largerBound ++ largerOuter)
          (largerBound ++ normalizedLargerOuter) :=
        recursiveLiftOuterRenaming largerBound targetRenaming
      let newEmbedding : WireRenaming
          (smallerBound ++ normalizedSmallerOuter)
          (largerBound ++ normalizedLargerOuter) := bounds.embed newOuter
      let innerCommutes : ∀ {signature : Sig}
          (value : Var (smallerBound ++ smallerOuter) signature),
          newEmbedding (sourceMap value) =
            targetMap (items.embedding value) := by
        intro signature value
        calc
          newEmbedding (sourceMap value) =
              targetMap (bounds.embed oldOuter value) :=
            (recursiveBoundEmbed_natural bounds oldOuter sourceRenaming
              targetRenaming newOuter (by
                intro valueSignature outerValue
                exact commutes outerValue) value).symm
          _ = targetMap (items.embedding value) :=
            congrArg targetMap (consistent.2 value).symm
      .block newOuter bounds
        (recursiveReindexItemSeq sourceMap targetMap newEmbedding items
          consistent.1 innerCommutes)
        (recursiveReindexHoles insertion bounds oldOuter sourceRenaming
          targetRenaming newOuter (by
            intro valueSignature value
            exact commutes value) holes)

/-- Reindex one consistent cylindrical item. -/
noncomputable def recursiveReindexItem
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (item : CylindricalShapeItem definitions insertion smallerContext
      largerContext)
    (consistent : item.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (item.embedding value)) :
    CylindricalShapeItem definitions insertion normalizedSmallerContext
      normalizedLargerContext :=
  match item with
  | .leaf oldEmbedding smaller larger exact =>
      .leaf newEmbedding (smaller.renameWires sourceRenaming)
        (larger.renameWires targetRenaming) (by
          let combined : WireRenaming smallerContext
              normalizedLargerContext :=
            fun {_} value => newEmbedding (sourceRenaming value)
          calc
            (smaller.renameWires sourceRenaming).renameWires newEmbedding =
                smaller.renameWires combined :=
              recursiveItemRename_comp sourceRenaming newEmbedding combined
                (fun _ => rfl) smaller
            _ = smaller.renameWires
                (fun {_} value => targetRenaming (oldEmbedding value)) :=
              recursiveItemRename_eq _ _ (by
                intro signature value
                exact commutes value) smaller
            _ = (smaller.renameWires oldEmbedding).renameWires
                targetRenaming :=
              (recursiveItemRename_comp oldEmbedding targetRenaming
                (fun {_} value => targetRenaming (oldEmbedding value))
                (fun _ => rfl) smaller).symm
            _ = larger.renameWires targetRenaming :=
              congrArg (Item.renameWires targetRenaming) exact)
  | .cut body =>
      .cut (recursiveReindexShape sourceRenaming targetRenaming newEmbedding
        body consistent (by
          intro signature value
          exact commutes value))

/-- Reindex one consistent ordered cylindrical item sequence. -/
noncomputable def recursiveReindexItemSeq
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (items : CylindricalShapeItemSeq definitions insertion smallerContext
      largerContext)
    (consistent : items.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (items.embedding value)) :
    CylindricalShapeItemSeq definitions insertion normalizedSmallerContext
      normalizedLargerContext :=
  match items with
  | .nil oldEmbedding => .nil newEmbedding
  | .cons head tail =>
      .cons
        (recursiveReindexItem sourceRenaming targetRenaming newEmbedding head
          consistent.1 (by
            intro signature value
            exact commutes value))
        (recursiveReindexItemSeq sourceRenaming targetRenaming newEmbedding
          tail consistent.2.1 (by
            intro signature value
            calc
              newEmbedding (sourceRenaming value) =
                  targetRenaming (head.embedding value) := commutes value
              _ = targetRenaming (tail.embedding value) :=
                congrArg targetRenaming (consistent.2.2 value).symm))

end

mutual

/-- Reindexing preserves shape consistency and installs exactly the requested
outer embedding. -/
theorem recursiveReindexShape_valid
    (sourceRenaming : WireRenaming smallerOuter normalizedSmallerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter)
    (shape : CylindricalShape definitions insertion smallerOuter largerOuter)
    (consistent : shape.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerOuter signature),
      newOuter (sourceRenaming value) =
        targetRenaming (shape.embedding value)) :
    let reindexed := recursiveReindexShape sourceRenaming targetRenaming
      newOuter shape consistent commutes
    reindexed.consistent ∧
      ∀ {signature : Sig}
        (value : Var normalizedSmallerOuter signature),
        reindexed.embedding value = newOuter value := by
  cases shape with
  | block oldOuter bounds items holes =>
      simp only [recursiveReindexShape, CylindricalShape.consistent,
        CylindricalShape.embedding]
      constructor
      · constructor
        · exact (recursiveReindexItemSeq_valid _ _ _ items consistent.1 _).1
        · intro signature value
          exact (recursiveReindexItemSeq_valid _ _ _ items consistent.1 _).2
            value
      · intro signature value
        exact True.intro

/-- Reindexing preserves item consistency and installs exactly the requested
item embedding. -/
theorem recursiveReindexItem_valid
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (item : CylindricalShapeItem definitions insertion smallerContext
      largerContext)
    (consistent : item.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (item.embedding value)) :
    let reindexed := recursiveReindexItem sourceRenaming targetRenaming
      newEmbedding item consistent commutes
    reindexed.consistent ∧
      ∀ {signature : Sig}
        (value : Var normalizedSmallerContext signature),
        reindexed.embedding value = newEmbedding value := by
  cases item with
  | leaf oldEmbedding smaller larger exact =>
      exact ⟨True.intro, fun _ => rfl⟩
  | cut body =>
      simpa only [recursiveReindexItem, CylindricalShapeItem.consistent,
        CylindricalShapeItem.embedding] using
        recursiveReindexShape_valid sourceRenaming targetRenaming newEmbedding
          body consistent commutes

/-- Reindexing preserves sequence consistency and installs exactly the
requested sequence embedding. -/
theorem recursiveReindexItemSeq_valid
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (items : CylindricalShapeItemSeq definitions insertion smallerContext
      largerContext)
    (consistent : items.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (items.embedding value)) :
    let reindexed := recursiveReindexItemSeq sourceRenaming targetRenaming
      newEmbedding items consistent commutes
    reindexed.consistent ∧
      ∀ {signature : Sig}
        (value : Var normalizedSmallerContext signature),
        reindexed.embedding value = newEmbedding value := by
  cases items with
  | nil oldEmbedding =>
      exact ⟨True.intro, fun _ => rfl⟩
  | cons head tail =>
      simp only [recursiveReindexItemSeq,
        CylindricalShapeItemSeq.consistent,
        CylindricalShapeItemSeq.embedding]
      have headValid := recursiveReindexItem_valid sourceRenaming
        targetRenaming newEmbedding head consistent.1 commutes
      have tailCommutes : ∀ {signature : Sig}
          (value : Var smallerContext signature),
          newEmbedding (sourceRenaming value) =
            targetRenaming (tail.embedding value) := by
        intro signature value
        calc
          newEmbedding (sourceRenaming value) =
              targetRenaming (head.embedding value) := commutes value
          _ = targetRenaming (tail.embedding value) :=
            congrArg targetRenaming (consistent.2.2 value).symm
      have tailValid := recursiveReindexItemSeq_valid sourceRenaming
        targetRenaming newEmbedding tail consistent.2.1 tailCommutes
      refine ⟨⟨headValid.1, tailValid.1, ?_⟩, headValid.2⟩
      intro signature value
      exact (tailValid.2 value).trans (headValid.2 value).symm

end

mutual
/-- Rename the free context of an already-abstracted uniform region. -/
def recursiveUniformRegionRename
    (rho : WireRenaming source target) :
    UniformIntrinsicRegion definitions arguments source →
      UniformIntrinsicRegion definitions arguments target
  | .mk ordinary holes =>
      .mk (recursiveUniformItemSeqRename rho ordinary)
        ⟨holes.values.map fun values => Vars.rename rho values⟩

/-- Rename the free context of one already-abstracted uniform item. -/
def recursiveUniformItemRename
    (rho : WireRenaming source target) :
    UniformIntrinsicItem definitions arguments source →
      UniformIntrinsicItem definitions arguments target
  | .leaf item => .leaf (item.renameWires rho)
  | .cut body => .cut (recursiveUniformRegionRename rho body)
  | .bind signature body =>
      .bind signature
        (recursiveUniformRegionRename (WireRenaming.lift rho signature) body)

/-- Rename the free context of an ordered already-abstracted item sequence. -/
def recursiveUniformItemSeqRename
    (rho : WireRenaming source target) :
    UniformIntrinsicItemSeq definitions arguments source →
      UniformIntrinsicItemSeq definitions arguments target
  | .nil => .nil
  | .cons head tail =>
      .cons (recursiveUniformItemRename rho head)
        (recursiveUniformItemSeqRename rho tail)
end

/-- Uniform context renaming commutes with one explicit argument binder. -/
theorem recursiveUniformRename_wrapArgumentBind
    (rho : WireRenaming source target)
    (signature : Sig)
    (body : UniformIntrinsicRegion definitions arguments
      (signature :: source)) :
    recursiveUniformRegionRename rho (wrapArgumentBind signature body) =
      wrapArgumentBind signature
        (recursiveUniformRegionRename (WireRenaming.lift rho signature)
          body) := rfl

/-- Uniform context renaming commutes with an ordered argument binder block. -/
theorem recursiveUniformRename_wrapArgumentBinds
    (rho : WireRenaming source target) :
    ∀ (bound : List Sig)
      (body : UniformIntrinsicRegion definitions arguments (bound ++ source)),
      recursiveUniformRegionRename rho (wrapArgumentBinds bound body) =
        wrapArgumentBinds bound
          (recursiveUniformRegionRename
            (recursiveLiftOuterRenaming bound rho) body)
  | [], body => rfl
  | signature :: rest, body => by
      simp only [wrapArgumentBinds]
      rw [recursiveUniformRename_wrapArgumentBinds rho rest]
      rfl

mutual

/-- Reindexing a shape renames its two uniform projections exactly. -/
theorem recursiveReindexShape_projections
    (sourceRenaming : WireRenaming smallerOuter normalizedSmallerOuter)
    (targetRenaming : WireRenaming largerOuter normalizedLargerOuter)
    (newOuter : WireRenaming normalizedSmallerOuter normalizedLargerOuter)
    (shape : CylindricalShape definitions insertion smallerOuter largerOuter)
    (consistent : shape.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerOuter signature),
      newOuter (sourceRenaming value) =
        targetRenaming (shape.embedding value)) :
    let reindexed := recursiveReindexShape sourceRenaming targetRenaming
      newOuter shape consistent commutes
    reindexed.smaller =
        recursiveUniformRegionRename sourceRenaming shape.smaller ∧
      reindexed.larger =
        recursiveUniformRegionRename targetRenaming shape.larger := by
  cases shape with
  | block oldOuter bounds items holes =>
      rename_i smallerBound largerBound freshCount smallerHoles largerHoles
      simp only [recursiveReindexShape, CylindricalShape.smaller,
        CylindricalShape.larger]
      rw [recursiveUniformRename_wrapArgumentBinds,
        recursiveUniformRename_wrapArgumentBinds]
      let sourceMap : WireRenaming (smallerBound ++ smallerOuter)
          (smallerBound ++ normalizedSmallerOuter) :=
        recursiveLiftOuterRenaming smallerBound sourceRenaming
      let targetMap : WireRenaming (largerBound ++ largerOuter)
          (largerBound ++ normalizedLargerOuter) :=
        recursiveLiftOuterRenaming largerBound targetRenaming
      let newEmbedding : WireRenaming
          (smallerBound ++ normalizedSmallerOuter)
          (largerBound ++ normalizedLargerOuter) := bounds.embed newOuter
      have innerCommutes : ∀ {signature : Sig}
          (value : Var (smallerBound ++ smallerOuter) signature),
          newEmbedding (sourceMap value) =
            targetMap (items.embedding value) := by
        intro signature value
        calc
          newEmbedding (sourceMap value) =
              targetMap (bounds.embed oldOuter value) :=
            (recursiveBoundEmbed_natural bounds oldOuter sourceRenaming
              targetRenaming newOuter commutes value).symm
          _ = targetMap (items.embedding value) :=
            congrArg targetMap (consistent.2 value).symm
      have itemExact := recursiveReindexItemSeq_projections sourceMap
        targetMap newEmbedding items consistent.1 innerCommutes
      constructor
      · apply congrArg (wrapArgumentBinds smallerBound)
        rw [itemExact.1]
        rfl
      · apply congrArg (wrapArgumentBinds largerBound)
        rw [itemExact.2]
        rfl

/-- Reindexing an item renames its two uniform projections exactly. -/
theorem recursiveReindexItem_projections
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (item : CylindricalShapeItem definitions insertion smallerContext
      largerContext)
    (consistent : item.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (item.embedding value)) :
    let reindexed := recursiveReindexItem sourceRenaming targetRenaming
      newEmbedding item consistent commutes
    reindexed.smaller =
        recursiveUniformItemRename sourceRenaming item.smaller ∧
      reindexed.larger =
        recursiveUniformItemRename targetRenaming item.larger := by
  cases item with
  | leaf oldEmbedding smaller larger exact => exact ⟨rfl, rfl⟩
  | cut body =>
      have bodyExact := recursiveReindexShape_projections sourceRenaming
        targetRenaming newEmbedding body consistent commutes
      exact ⟨congrArg UniformIntrinsicItem.cut bodyExact.1,
        congrArg UniformIntrinsicItem.cut bodyExact.2⟩

/-- Reindexing an item sequence renames its two uniform projections exactly. -/
theorem recursiveReindexItemSeq_projections
    (sourceRenaming : WireRenaming smallerContext normalizedSmallerContext)
    (targetRenaming : WireRenaming largerContext normalizedLargerContext)
    (newEmbedding : WireRenaming normalizedSmallerContext
      normalizedLargerContext)
    (items : CylindricalShapeItemSeq definitions insertion smallerContext
      largerContext)
    (consistent : items.consistent)
    (commutes : ∀ {signature : Sig}
      (value : Var smallerContext signature),
      newEmbedding (sourceRenaming value) =
        targetRenaming (items.embedding value)) :
    let reindexed := recursiveReindexItemSeq sourceRenaming targetRenaming
      newEmbedding items consistent commutes
    reindexed.smaller =
        recursiveUniformItemSeqRename sourceRenaming items.smaller ∧
      reindexed.larger =
        recursiveUniformItemSeqRename targetRenaming items.larger := by
  cases items with
  | nil oldEmbedding => exact ⟨rfl, rfl⟩
  | cons head tail =>
      simp only [recursiveReindexItemSeq,
        CylindricalShapeItemSeq.smaller, CylindricalShapeItemSeq.larger,
        recursiveUniformItemSeqRename]
      have headExact := recursiveReindexItem_projections sourceRenaming
        targetRenaming newEmbedding head consistent.1 commutes
      have tailCommutes : ∀ {signature : Sig}
          (value : Var smallerContext signature),
          newEmbedding (sourceRenaming value) =
            targetRenaming (tail.embedding value) := by
        intro signature value
        exact (commutes value).trans
          (congrArg targetRenaming (consistent.2.2 value).symm)
      have tailExact := recursiveReindexItemSeq_projections sourceRenaming
        targetRenaming newEmbedding tail consistent.2.1 tailCommutes
      constructor
      · rw [headExact.1, tailExact.1]
      · rw [headExact.2, tailExact.2]

end

/-- Transport a cylindrical shape across exact source and target context
equalities. -/
def recursiveShapeTransport
    (sourceExact : sourceContext = normalizedSourceContext)
    (targetExact : targetContext = normalizedTargetContext)
    (shape : CylindricalShape definitions insertion
      sourceContext targetContext) :
    CylindricalShape definitions insertion
      normalizedSourceContext normalizedTargetContext := by
  cases sourceExact
  cases targetExact
  exact shape

@[simp] theorem recursiveShapeTransport_smaller
    (sourceExact : sourceContext = normalizedSourceContext)
    (targetExact : targetContext = normalizedTargetContext)
    (shape : CylindricalShape definitions insertion
      sourceContext targetContext) :
    (recursiveShapeTransport sourceExact targetExact shape).smaller =
      sourceExact ▸ shape.smaller := by
  cases sourceExact
  cases targetExact
  rfl

@[simp] theorem recursiveShapeTransport_larger
    (sourceExact : sourceContext = normalizedSourceContext)
    (targetExact : targetContext = normalizedTargetContext)
    (shape : CylindricalShape definitions insertion
      sourceContext targetContext) :
    (recursiveShapeTransport sourceExact targetExact shape).larger =
      targetExact ▸ shape.larger := by
  cases sourceExact
  cases targetExact
  rfl

/-- Casting an abstracted region casts its head and body together. -/
theorem recursiveCast_abstractApplied
    (same : sourceContext = targetContext)
    (head : Var sourceContext (.rel arguments))
    (body : Region definitions sourceContext) :
    same ▸ UniformIntrinsicRegion.abstractApplied head body =
      UniformIntrinsicRegion.abstractApplied (same ▸ head) (same ▸ body) := by
  cases same
  rfl

/-- Casting a complete intrinsic region is the same as renaming every wire by
that cast. -/
theorem recursiveCastRegion_eq_rename
    (same : sourceContext = targetContext)
    (body : Region definitions sourceContext) :
    same ▸ body = body.renameWires (fun {_} value => same ▸ value) := by
  cases same
  change body = body.renameWires (fun {_} value => value)
  exact (recursiveRegionRename_id body).symm

/-- The elaborator's dependent region normalization is the corresponding
cast on a complete intrinsic region. -/
theorem recursiveRegionNormalization_region
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (body : Region definitions (context.extend region).sigs) :
    body.renameWires (recursiveRegionNormalization context region) =
      ConcreteElaboration.WireContext.sigs_extend context region ▸ body := by
  unfold recursiveRegionNormalization
  exact (recursiveCastRegion_eq_rename
    (ConcreteElaboration.WireContext.sigs_extend context region) body).symm

/-- Positive climbing from a checked root always fails. -/
theorem recursiveClimb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

/-- A checked region has a unique distance to the root. -/
theorem recursiveClimb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [recursiveClimb_succ_root_none definitions diagram wellFormed
            right] at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [recursiveClimb_succ_root_none definitions diagram wellFormed
            left] at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet => simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              have leftParent :
                  diagram.climb left parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using leftClimb
              have rightParent :
                  diagram.climb right parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using rightClimb
              exact congrArg Nat.succ
                (induction leftParent rightParent)

/-- A strictly deeper recursive region cannot be the acted head region. -/
theorem recursiveBelow_ne_head
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (head region : diagram.RegionId)
    (headDepth regionDepth : Nat)
    (headClimb : diagram.climb headDepth head = some diagram.root)
    (regionClimb : diagram.climb regionDepth region = some diagram.root)
    (below : headDepth < regionDepth) : region ≠ head := by
  intro same
  subst region
  have depthsEqual := recursiveClimb_to_root_unique definitions diagram
    wellFormed headClimb regionClimb
  omega

/-- Casting back across an equality returns the original dependent value. -/
theorem recursiveCast_symm_cancel
    (same : sourceContext = targetContext)
    (value : Var targetContext signature) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

/-- Exact normalized abstraction of one child body after transporting the
child shape into its parent's explicit local/outer context. -/
theorem recursiveTransportedChild_smaller
    (sourceExact : sourceContext = normalizedSourceContext)
    (targetExact : targetContext = normalizedTargetContext)
    (sourceHead : Var normalizedSourceContext (.rel smallerArguments))
    (sourceBody : Region definitions sourceContext)
    (shape : CylindricalShape definitions insertion
      sourceContext targetContext)
    (shapeExact : shape.smaller =
      UniformIntrinsicRegion.abstractApplied
        (sourceExact.symm ▸ sourceHead) sourceBody) :
    (recursiveShapeTransport sourceExact targetExact shape).smaller =
      UniformIntrinsicRegion.abstractApplied sourceHead
        (sourceExact ▸ sourceBody) := by
  rw [recursiveShapeTransport_smaller, shapeExact,
    recursiveCast_abstractApplied]
  rw [recursiveCast_symm_cancel]

/-- Target counterpart of `recursiveTransportedChild_smaller`. -/
theorem recursiveTransportedChild_larger
    (sourceExact : sourceContext = normalizedSourceContext)
    (targetExact : targetContext = normalizedTargetContext)
    (targetHead : Var normalizedTargetContext (.rel largerArguments))
    (targetBody : Region definitions targetContext)
    (shape : CylindricalShape definitions insertion
      sourceContext targetContext)
    (shapeExact : shape.larger =
      UniformIntrinsicRegion.abstractApplied
        (targetExact.symm ▸ targetHead) targetBody) :
    (recursiveShapeTransport sourceExact targetExact shape).larger =
      UniformIntrinsicRegion.abstractApplied targetHead
        (targetExact ▸ targetBody) := by
  rw [recursiveShapeTransport_larger, shapeExact,
    recursiveCast_abstractApplied]
  rw [recursiveCast_symm_cancel]

def recursiveChildSmallerItems
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    List (CylindricalShape definitions insertion smallerContext largerContext) →
      UniformIntrinsicItemSeq definitions smallerArguments smallerContext
  | [] => .nil
  | shape :: tail =>
      .cons (.cut shape.smaller) (recursiveChildSmallerItems insertion tail)

def recursiveChildLargerItems
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    List (CylindricalShape definitions insertion smallerContext largerContext) →
      UniformIntrinsicItemSeq definitions largerArguments largerContext
  | [] => .nil
  | shape :: tail =>
      .cons (.cut shape.larger) (recursiveChildLargerItems insertion tail)

theorem recursiveCompileChildrenCons
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (child : diagram.RegionId)
    (tail : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled : ConcreteElaboration.compileChildrenWith? definitions diagram
      recurse context (child :: tail) = some items) :
    ∃ body rest,
      recurse child context = some body ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
        context tail = some rest ∧
      items = .cons (.cut body) rest := by
  unfold ConcreteElaboration.compileChildrenWith? at compiled
  cases bodyCompiled : recurse child context with
  | none => simp [bodyCompiled] at compiled
  | some body =>
      cases restCompiled : ConcreteElaboration.compileChildrenWith?
          definitions diagram recurse context tail with
      | none => simp [bodyCompiled, restCompiled] at compiled
      | some rest =>
          refine ⟨body, rest, rfl, rfl, ?_⟩
          exact (Option.some.inj (by
            simpa [bodyCompiled, restCompiled] using compiled)).symm

/-- Ordered successful child compilations become an ordered list of
transported cylindrical shapes, represented only by `.cut` items. -/
theorem recursiveChildrenReceipts
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext : ConcreteElaboration.WireContext result.checked.val)
    (sourceExact : sourceContext.sigs = normalizedSourceContext)
    (targetExact : targetContext.sigs = normalizedTargetContext)
    (sourceHead : Var normalizedSourceContext (.rel smallerArguments))
    (targetHead : Var normalizedTargetContext (.rel largerArguments))
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
      Option (Region definitions context.sigs))
    (targetRecurse : (region : result.checked.val.RegionId) →
      (context : ConcreteElaboration.WireContext result.checked.val) →
      Option (Region definitions context.sigs))
    (children : List source.val.RegionId)
    (buildChild : ∀ (child : source.val.RegionId)
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody : Region definitions targetContext.sigs),
      child ∈ children →
      sourceRecurse child sourceContext = some sourceBody →
      targetRecurse (result.regionEquiv child) targetContext = some targetBody →
      ∃ shape : CylindricalShape definitions insertion
          sourceContext.sigs targetContext.sigs,
        shape.smaller = UniformIntrinsicRegion.abstractApplied
          (sourceExact.symm ▸ sourceHead) sourceBody ∧
        shape.larger = UniformIntrinsicRegion.abstractApplied
          (targetExact.symm ▸ targetHead) targetBody) :
    ∀ (sourceItems : ItemSeq definitions sourceContext.sigs)
      (targetItems : ItemSeq definitions targetContext.sigs),
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext children = some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions result.checked.val
          targetRecurse targetContext (children.map result.regionEquiv) =
        some targetItems →
      ∃ shapes : List (CylindricalShape definitions insertion
          normalizedSourceContext normalizedTargetContext),
        UniformIntrinsicRegion.abstractAppliedItems sourceHead
            (sourceItems.renameWires
              (fun {_} value => sourceExact ▸ value)) =
          .mk (recursiveChildSmallerItems insertion shapes) ⟨[]⟩ ∧
        UniformIntrinsicRegion.abstractAppliedItems targetHead
            (targetItems.renameWires
              (fun {_} value => targetExact ▸ value)) =
          .mk (recursiveChildLargerItems insertion shapes) ⟨[]⟩
  := by
    intro sourceItems targetItems sourceCompiled targetCompiled
    induction children generalizing sourceItems targetItems with
    | nil =>
      simp [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      subst sourceItems
      subst targetItems
      exact ⟨[], rfl, rfl⟩
    | cons child tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled, sourceRestCompiled,
          sourceItemsExact⟩ :=
        recursiveCompileChildrenCons definitions source.val
          sourceRecurse sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetBody, targetRest, targetBodyCompiled, targetRestCompiled,
          targetItemsExact⟩ :=
        recursiveCompileChildrenCons definitions result.checked.val
          targetRecurse targetContext (result.regionEquiv child)
          (tail.map result.regionEquiv) targetItems (by
            simpa using targetCompiled)
      obtain ⟨childShape, childSmaller, childLarger⟩ :=
        buildChild child sourceBody targetBody (by simp) sourceBodyCompiled
          targetBodyCompiled
      obtain ⟨tailShapes, tailSmaller, tailLarger⟩ :=
        induction
          (fun candidate candidateSource candidateTarget member =>
            buildChild candidate candidateSource candidateTarget
              (List.mem_cons_of_mem child member))
          sourceRest targetRest sourceRestCompiled targetRestCompiled
      let transported := recursiveShapeTransport sourceExact targetExact
        childShape
      have transportedSmaller : transported.smaller =
          UniformIntrinsicRegion.abstractApplied sourceHead
            (sourceBody.renameWires (fun {_} value => sourceExact ▸ value)) := by
        rw [recursiveTransportedChild_smaller sourceExact targetExact sourceHead
          sourceBody childShape childSmaller]
        exact congrArg (UniformIntrinsicRegion.abstractApplied sourceHead)
          (recursiveCastRegion_eq_rename sourceExact sourceBody)
      have transportedLarger : transported.larger =
          UniformIntrinsicRegion.abstractApplied targetHead
            (targetBody.renameWires (fun {_} value => targetExact ▸ value)) := by
        rw [recursiveTransportedChild_larger sourceExact targetExact targetHead
          targetBody childShape childLarger]
        exact congrArg (UniformIntrinsicRegion.abstractApplied targetHead)
          (recursiveCastRegion_eq_rename targetExact targetBody)
      refine ⟨transported :: tailShapes, ?_, ?_⟩
      · subst sourceItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildSmallerItems]
        rw [← transportedSmaller, tailSmaller]
        rfl
      · subst targetItems
        simp only [ItemSeq.renameWires, Item.renameWires,
          UniformIntrinsicRegion.abstractAppliedItems,
          recursiveChildLargerItems]
        rw [← transportedLarger, tailLarger]
        rfl

/-- Canonical cylindrical receipt for an ordinary compiled leaf sequence and
its exact renaming. -/
def recursiveLeafReceipt
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    (items : ItemSeq definitions smallerContext) →
      CylindricalShapeItemSeq definitions insertion smallerContext largerContext
  | .nil => .nil embedding
  | .cons head tail =>
      .cons (.leaf embedding head (head.renameWires embedding) rfl)
        (recursiveLeafReceipt insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_smaller
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ items : ItemSeq definitions smallerContext,
      (recursiveLeafReceipt insertion embedding items).smaller =
        recursiveLeafItems items
  | .nil => rfl
  | .cons head tail => by
      simp only [recursiveLeafReceipt, CylindricalShapeItemSeq.smaller,
        CylindricalShapeItem.smaller, recursiveLeafItems]
      exact congrArg (UniformIntrinsicItemSeq.cons (.leaf head))
        (recursiveLeafReceipt_smaller insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_larger
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ items : ItemSeq definitions smallerContext,
      (recursiveLeafReceipt insertion embedding items).larger =
        recursiveLeafItems (items.renameWires embedding)
  | .nil => rfl
  | .cons head tail => by
      simp only [recursiveLeafReceipt, CylindricalShapeItemSeq.larger,
        CylindricalShapeItem.larger, recursiveLeafItems, ItemSeq.renameWires]
      exact congrArg
        (UniformIntrinsicItemSeq.cons (.leaf (head.renameWires embedding)))
        (recursiveLeafReceipt_larger insertion embedding tail)

@[simp] theorem recursiveLeafReceipt_embedding
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (embedding : WireRenaming smallerContext largerContext) :
    ∀ (items : ItemSeq definitions smallerContext) {signature : Sig}
      (value : Var smallerContext signature),
      (recursiveLeafReceipt insertion embedding items).embedding value =
        embedding value
  | .nil, _, _ => rfl
  | .cons head tail, _, _ => rfl

/-- Concatenate two cylindrical item-sequence receipts without changing their
shared context action. -/
def recursiveReceiptAppend
    (left right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    CylindricalShapeItemSeq definitions insertion smallerContext largerContext :=
  match left with
  | .nil _ => right
  | .cons head tail => .cons head (recursiveReceiptAppend tail right)

@[simp] theorem recursiveReceiptAppend_smaller
    (right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    ∀ left : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext,
    (recursiveReceiptAppend left right).smaller =
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
        left.smaller right.smaller
  | .nil _ => rfl
  | .cons head tail => by
      simp only [recursiveReceiptAppend, CylindricalShapeItemSeq.smaller,
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.append]
      exact congrArg (UniformIntrinsicItemSeq.cons head.smaller)
        (recursiveReceiptAppend_smaller right tail)

@[simp] theorem recursiveReceiptAppend_larger
    (right : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext) :
    ∀ left : CylindricalShapeItemSeq definitions insertion
      smallerContext largerContext,
    (recursiveReceiptAppend left right).larger =
      UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
        left.larger right.larger
  | .nil _ => rfl
  | .cons head tail => by
      simp only [recursiveReceiptAppend, CylindricalShapeItemSeq.larger,
        UniformIntrinsicRegion.UniformIntrinsicItemSeq.append]
      exact congrArg (UniformIntrinsicItemSeq.cons head.larger)
        (recursiveReceiptAppend_larger right tail)

/-- Exact node/child decomposition of one successful positive-fuel region
compilation.  This is the executable equation consumed by recursive receipts. -/
theorem compileRegion?_recursive_decomposition
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (region : diagram.RegionId)
    (context : ConcreteElaboration.WireContext diagram)
    (body : Region definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileRegion? definitions diagram (fuel + 1)
          region context = some body) :
    ∃ (nodes children : ItemSeq definitions (context.extend region).sigs),
      ConcreteElaboration.compileNodes? definitions diagram
          (context.extend region) (diagram.nodesAt region) = some nodes ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram fuel)
          (context.extend region) (diagram.childrenOf region) = some children ∧
      body = ConcreteElaboration.finishRegion diagram context region
        (.mk (nodes.append children)) := by
  unfold ConcreteElaboration.compileRegion? at compiled
  cases nodesCompiled : ConcreteElaboration.compileNodes? definitions diagram
      (context.extend region) (diagram.nodesAt region) with
  | none => simp [nodesCompiled] at compiled
  | some nodes =>
      cases childrenCompiled :
          ConcreteElaboration.compileChildrenWith? definitions diagram
            (ConcreteElaboration.compileRegion? definitions diagram fuel)
            (context.extend region) (diagram.childrenOf region) with
      | none => simp [nodesCompiled, childrenCompiled] at compiled
      | some children =>
          refine ⟨nodes, children, rfl, rfl, ?_⟩
          have bodyExact : some (ConcreteElaboration.finishRegion diagram
              context region (.mk (nodes.append children))) = some body := by
            simpa [nodesCompiled, childrenCompiled] using compiled
          exact (Option.some.inj bodyExact).symm

/-- One successful ordered child compilation exposes its head cut and the
remaining child sequence without changing order. -/
theorem compileChildrenWith?_cons_decomposition
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (child : diagram.RegionId)
    (tail : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context (child :: tail) = some items) :
    ∃ body rest,
      recurse child context = some body ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context tail = some rest ∧
      items = .cons (.cut body) rest := by
  unfold ConcreteElaboration.compileChildrenWith? at compiled
  cases bodyCompiled : recurse child context with
  | none => simp [bodyCompiled] at compiled
  | some body =>
      cases restCompiled :
          ConcreteElaboration.compileChildrenWith? definitions diagram recurse
            context tail with
      | none => simp [bodyCompiled, restCompiled] at compiled
      | some rest =>
          refine ⟨body, rest, rfl, rfl, ?_⟩
          have itemsExact : some (.cons (.cut body) rest) = some items := by
            simpa [bodyCompiled, restCompiled] using compiled
          exact (Option.some.inj itemsExact).symm

/-- Smaller cut-item projection of an ordered list of child shapes. -/
def recursiveSmallerCutItems
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    List (CylindricalShape definitions insertion smallerContext largerContext) →
      UniformIntrinsicItemSeq definitions smallerArguments smallerContext
  | [] => .nil
  | shape :: tail =>
      .cons (.cut shape.smaller) (recursiveSmallerCutItems insertion tail)

/-- Larger cut-item projection of an ordered list of child shapes. -/
def recursiveLargerCutItems
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    List (CylindricalShape definitions insertion smallerContext largerContext) →
      UniformIntrinsicItemSeq definitions largerArguments largerContext
  | [] => .nil
  | shape :: tail =>
      .cons (.cut shape.larger) (recursiveLargerCutItems insertion tail)

/-- Ordered child shapes become an item-sequence receipt consisting only of
`CylindricalShapeItem.cut` constructors. -/
def recursiveCutReceipt
    (outer : WireRenaming smallerContext largerContext) :
    List (CylindricalShape definitions insertion smallerContext largerContext) →
      CylindricalShapeItemSeq definitions insertion
        smallerContext largerContext
  | [] => .nil outer
  | shape :: tail =>
      .cons (.cut shape) (recursiveCutReceipt outer tail)

@[simp] theorem recursiveCutReceipt_smaller
    (outer : WireRenaming smallerContext largerContext) :
    ∀ shapes :
      List (CylindricalShape definitions insertion smallerContext largerContext),
      (recursiveCutReceipt outer shapes).smaller =
        recursiveSmallerCutItems insertion shapes
  | [] => rfl
  | shape :: tail => by
      simp only [recursiveCutReceipt, CylindricalShapeItemSeq.smaller,
        CylindricalShapeItem.smaller, recursiveSmallerCutItems]
      exact congrArg (UniformIntrinsicItemSeq.cons (.cut shape.smaller))
        (recursiveCutReceipt_smaller outer tail)

@[simp] theorem recursiveCutReceipt_larger
    (outer : WireRenaming smallerContext largerContext) :
    ∀ shapes :
      List (CylindricalShape definitions insertion smallerContext largerContext),
      (recursiveCutReceipt outer shapes).larger =
        recursiveLargerCutItems insertion shapes
  | [] => rfl
  | shape :: tail => by
      simp only [recursiveCutReceipt, CylindricalShapeItemSeq.larger,
        CylindricalShapeItem.larger, recursiveLargerCutItems]
      exact congrArg (UniformIntrinsicItemSeq.cons (.cut shape.larger))
        (recursiveCutReceipt_larger outer tail)

theorem recursiveChildSmallerItems_eq
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    ∀ shapes : List (CylindricalShape definitions insertion
      smallerContext largerContext),
      recursiveChildSmallerItems insertion shapes =
        recursiveSmallerCutItems insertion shapes
  | [] => rfl
  | shape :: tail => by
      simp only [recursiveChildSmallerItems, recursiveSmallerCutItems]
      rw [recursiveChildSmallerItems_eq insertion tail]

theorem recursiveChildLargerItems_eq
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature) :
    ∀ shapes : List (CylindricalShape definitions insertion
      smallerContext largerContext),
      recursiveChildLargerItems insertion shapes =
        recursiveLargerCutItems insertion shapes
  | [] => rfl
  | shape :: tail => by
      simp only [recursiveChildLargerItems, recursiveLargerCutItems]
      rw [recursiveChildLargerItems_eq insertion tail]

/-- Assemble one recursive region block from its normalized retained leaves,
ordered child shapes, and exact hole receipt. -/
noncomputable def recursiveBlockReceipt
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (sourceRetained : ItemSeq definitions (smallerBound ++ smallerOuter))
    (children : List (CylindricalShape definitions insertion
      (smallerBound ++ smallerOuter) (largerBound ++ largerOuter)))
    (holes : CylindricalHoles insertion bounds outer smallerHoles largerHoles) :
    CylindricalShape definitions insertion smallerOuter largerOuter :=
  .block outer bounds
    (recursiveReceiptAppend
      (recursiveLeafReceipt insertion (bounds.embed outer) sourceRetained)
      (recursiveCutReceipt (bounds.embed outer) children)) holes

@[simp] theorem recursiveBlockReceipt_smaller
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (sourceRetained : ItemSeq definitions (smallerBound ++ smallerOuter))
    (children : List (CylindricalShape definitions insertion
      (smallerBound ++ smallerOuter) (largerBound ++ largerOuter)))
    (holes : CylindricalHoles insertion bounds outer smallerHoles largerHoles) :
    (recursiveBlockReceipt insertion bounds outer sourceRetained children
      holes).smaller =
      wrapArgumentBinds smallerBound
        (.mk (UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
          (recursiveLeafItems sourceRetained)
          (recursiveSmallerCutItems insertion children)) ⟨smallerHoles⟩) := by
  unfold recursiveBlockReceipt
  simp only [CylindricalShape.smaller, recursiveReceiptAppend_smaller,
    recursiveLeafReceipt_smaller, recursiveCutReceipt_smaller]

@[simp] theorem recursiveBlockReceipt_larger
    (insertion : TypedArguments.InsertionEvidence largerArguments
      smallerArguments fixedSignature)
    (bounds : BoundCylindrification fixedSignature smallerBound largerBound
      freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (sourceRetained : ItemSeq definitions (smallerBound ++ smallerOuter))
    (children : List (CylindricalShape definitions insertion
      (smallerBound ++ smallerOuter) (largerBound ++ largerOuter)))
    (holes : CylindricalHoles insertion bounds outer smallerHoles largerHoles) :
    (recursiveBlockReceipt insertion bounds outer sourceRetained children
      holes).larger =
      wrapArgumentBinds largerBound
        (.mk (UniformIntrinsicRegion.UniformIntrinsicItemSeq.append
          (recursiveLeafItems
            (sourceRetained.renameWires (bounds.embed outer)))
          (recursiveLargerCutItems insertion children)) ⟨largerHoles⟩) := by
  unfold recursiveBlockReceipt
  simp only [CylindricalShape.larger, recursiveReceiptAppend_larger,
    recursiveLeafReceipt_larger, recursiveCutReceipt_larger]

/-- Total cylindrical-shape receipt for every successfully compiled proper
descendant, by the elaborator's authoritative `(depth, fuel)` induction. -/
theorem recursiveCylindricalShape_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sourceArguments : List Sig)
    (sourceSignature :
      (source.val.wires wire).sig = .rel sourceArguments)
    (newArgument : Sig)
    (result : ArgumentResult source wire)
    (accepted : arityShift source wire newArgument = .ok result)
    (headDepth : Nat)
    (headClimb : source.val.climb headDepth
      (source.val.wires wire).scope = some source.val.root) :
    ∀ (fuel depth : Nat)
      (region : source.val.RegionId)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (targetOuter : ConcreteElaboration.WireContext result.checked.val)
      (outer : WireRenaming sourceOuter.sigs targetOuter.sigs),
      source.val.climb depth region = some source.val.root →
      depth + fuel = source.val.regionCount + 1 →
      headDepth < depth →
      ConcreteElaboration.ContextAbove source.val sourceOuter region →
      ConcreteElaboration.ContextAbove result.checked.val targetOuter
        (result.regionImage region) →
      (∀ {signature : Sig} (value : Var sourceOuter.sigs signature),
        ConcreteElaboration.WireContext.origin result.checked.val
            targetOuter.ids (outer value) =
          result.contextWireMap
            (ConcreteElaboration.WireContext.origin source.val
              sourceOuter.ids value)) →
      ∀ (sourceHead : Var sourceOuter.sigs (.rel sourceArguments))
        (targetHead : Var targetOuter.sigs (.rel result.targetArguments)),
      ConcreteElaboration.WireContext.origin source.val sourceOuter.ids
          sourceHead = wire →
      ConcreteElaboration.WireContext.origin result.checked.val targetOuter.ids
          targetHead = result.targetWire →
      ∀ (sourceBody : Region definitions sourceOuter.sigs)
        (targetBody : Region definitions targetOuter.sigs),
      ConcreteElaboration.compileRegion? definitions source.val fuel region
          sourceOuter = some sourceBody →
      ConcreteElaboration.compileRegion? definitions result.checked.val fuel
          (result.regionImage region) targetOuter = some targetBody →
      ∃ shape : CylindricalShape definitions
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          sourceOuter.sigs targetOuter.sigs,
        shape.smaller = UniformIntrinsicRegion.abstractApplied
          sourceHead sourceBody ∧
        shape.larger = UniformIntrinsicRegion.abstractApplied
          targetHead targetBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth region sourceOuter targetOuter outer regionClimb fuelExact
        below sourceAbove targetAbove outerOrigin sourceHead targetHead
        sourceHeadOrigin targetHeadOrigin sourceBody targetBody sourceCompiled
        targetCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro depth region sourceOuter targetOuter outer regionClimb fuelExact
        below sourceAbove targetAbove outerOrigin sourceHead targetHead
        sourceHeadOrigin targetHeadOrigin sourceBody targetBody sourceCompiled
        targetCompiled
      have notHead : region ≠ (source.val.wires wire).scope :=
        recursiveBelow_ne_head definitions source.val source.property
          (source.val.wires wire).scope region headDepth depth headClimb
          regionClimb below
      obtain ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
          sourceChildrenCompiled, sourceBodyExact⟩ :=
        compileRegion?_recursive_decomposition definitions source.val fuel
          region sourceOuter sourceBody sourceCompiled
      obtain ⟨targetNodes, targetChildren, targetNodesCompiled,
          targetChildrenCompiled, targetBodyExact⟩ :=
        compileRegion?_recursive_decomposition definitions result.checked.val
          fuel (result.regionImage region) targetOuter targetBody targetCompiled
      have sourceNodup : (sourceOuter.extend region).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions source.val source.property
          sourceOuter region sourceAbove
      have targetNodup :
          (targetOuter.extend (result.regionImage region)).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions result.checked.val
          result.checked.property targetOuter (result.regionImage region)
          targetAbove
      obtain ⟨sourceRetained, targetRetained, sourceRetainedCompiled,
          targetRetainedCompiled, retainedExact⟩ :=
        recursiveRetainedNodePair source wire sourceArguments sourceSignature
          newArgument result accepted region notHead sourceOuter targetOuter
          outer outerOrigin targetNodup sourceNodes sourceNodesCompiled
      let sourceExact :=
        ConcreteElaboration.WireContext.sigs_extend sourceOuter region
      let targetExact :=
        ConcreteElaboration.WireContext.sigs_extend targetOuter
          (result.regionImage region)
      let normalizedSourceHead := Var.appendRight
        ((source.val.wiresAt region).map fun localWire =>
          (source.val.wires localWire).sig) sourceHead
      let normalizedTargetHead := Var.appendRight
        ((result.checked.val.wiresAt (result.regionImage region)).map fun
          localWire => (result.checked.val.wires localWire).sig) targetHead
      have targetChildrenMapped :
          ConcreteElaboration.compileChildrenWith? definitions
              result.checked.val
              (ConcreteElaboration.compileRegion? definitions
                result.checked.val fuel)
              (targetOuter.extend (result.regionImage region))
              ((source.val.childrenOf region).map result.regionEquiv) =
            some targetChildren := by
        rw [← result.childrenOf_decomposition region]
        exact targetChildrenCompiled
      obtain ⟨childShapes, sourceChildrenExact, targetChildrenExact⟩ :=
        recursiveChildrenReceipts result
          (arityShiftInsertion source wire sourceArguments sourceSignature
            newArgument result accepted)
          (sourceOuter.extend region)
          (targetOuter.extend (result.regionImage region)) sourceExact
          targetExact normalizedSourceHead normalizedTargetHead
          (ConcreteElaboration.compileRegion? definitions source.val fuel)
          (ConcreteElaboration.compileRegion? definitions result.checked.val
            fuel)
          (source.val.childrenOf region) (by
            intro child childSourceBody childTargetBody childMember
              childSourceCompiled childTargetCompiled
            have childData := ConcreteElaboration.mem_childrenOf source.val
              region child childMember
            have childDepth := ConcreteElaboration.child_depth source.val child
              region depth childData regionClimb
            have childFuel : depth + 1 + fuel = source.val.regionCount + 1 := by
              omega
            have childBelow : headDepth < depth + 1 := by omega
            have childSourceAbove := ConcreteElaboration.extend_above_child
              definitions source.val source.property sourceOuter region child
              sourceAbove childData
            have targetChildData : result.checked.val.regions
                (result.regionImage child) =
              .cut (result.regionImage region) := by
              rw [result.regionImage_exact child,
                result.regionImage_exact region,
                result.regionImage_data child, childData]
              rfl
            have childTargetAbove := ConcreteElaboration.extend_above_child
              definitions result.checked.val result.checked.property targetOuter
              (result.regionImage region) (result.regionImage child) targetAbove
              targetChildData
            let childOuter : WireRenaming (sourceOuter.extend region).sigs
                (targetOuter.extend (result.regionImage region)).sigs :=
              arityShift_regionEmbedding_below source wire sourceArguments
                sourceSignature newArgument result accepted region notHead
                sourceOuter targetOuter outer
            have childOuterOrigin : ∀ {signature : Sig}
                (value : Var (sourceOuter.extend region).sigs signature),
                ConcreteElaboration.WireContext.origin result.checked.val
                    (targetOuter.extend (result.regionImage region)).ids
                    (childOuter value) =
                  result.contextWireMap
                    (ConcreteElaboration.WireContext.origin source.val
                      (sourceOuter.extend region).ids value) := by
              intro signature value
              exact arityShift_regionEmbedding_below_origin source wire
                sourceArguments sourceSignature newArgument result accepted
                region notHead sourceOuter targetOuter outer outerOrigin value
            let childSourceHead : Var (sourceOuter.extend region).sigs
                (.rel sourceArguments) := sourceExact.symm ▸ normalizedSourceHead
            let childTargetHead :
                Var (targetOuter.extend (result.regionImage region)).sigs
                  (.rel result.targetArguments) :=
              targetExact.symm ▸ normalizedTargetHead
            have childSourceHeadOrigin :
                ConcreteElaboration.WireContext.origin source.val
                    (sourceOuter.extend region).ids childSourceHead = wire := by
              unfold childSourceHead normalizedSourceHead sourceExact
              exact (recursive_origin_extend_outer source.val sourceOuter region
                sourceHead).trans sourceHeadOrigin
            have childTargetHeadOrigin :
                ConcreteElaboration.WireContext.origin result.checked.val
                    (targetOuter.extend (result.regionImage region)).ids
                    childTargetHead = result.targetWire := by
              unfold childTargetHead normalizedTargetHead targetExact
              exact (recursive_origin_extend_outer result.checked.val targetOuter
                (result.regionImage region) targetHead).trans targetHeadOrigin
            rw [← result.regionImage_exact child] at childTargetCompiled
            exact induction (depth + 1) child (sourceOuter.extend region)
              (targetOuter.extend (result.regionImage region)) childOuter
              childDepth childFuel childBelow childSourceAbove childTargetAbove
              childOuterOrigin childSourceHead childTargetHead
              childSourceHeadOrigin childTargetHeadOrigin childSourceBody
              childTargetBody childSourceCompiled childTargetCompiled)
          sourceChildren targetChildren sourceChildrenCompiled
          targetChildrenMapped
      rw [recursiveChildSmallerItems_eq] at sourceChildrenExact
      rw [recursiveChildLargerItems_eq] at targetChildrenExact
      let bounds := arityShift_regionBounds_below source wire sourceArguments
        sourceSignature newArgument result accepted region notHead
      let holes := recursiveRegionHoles source wire sourceArguments
        sourceSignature newArgument result accepted region notHead sourceOuter
        targetOuter outer outerOrigin sourceNodes targetNodes sourceNodesCompiled
        targetNodesCompiled sourceNodup targetNodup sourceHead targetHead
        sourceHeadOrigin targetHeadOrigin
      let normalizedSourceRetained := sourceRetained.renameWires
        (recursiveRegionNormalization sourceOuter region)
      let shape := recursiveBlockReceipt
        (arityShiftInsertion source wire sourceArguments sourceSignature
          newArgument result accepted) bounds outer normalizedSourceRetained
        childShapes holes
      refine ⟨shape, ?_, ?_⟩
      · unfold shape
        rw [recursiveBlockReceipt_smaller]
        rw [sourceBodyExact, ConcreteElaboration.finishRegion_eq_signatures]
        rw [recursiveAbstract_finishRegionSignatures]
        apply congrArg (wrapArgumentBinds
          ((source.val.wiresAt region).map fun localWire =>
            (source.val.wires localWire).sig))
        rw [← recursiveRegionNormalization_region sourceOuter region]
        simp only [Region.renameWires,
          UniformIntrinsicRegion.ItemSeq.renameWires_append]
        simp only [UniformIntrinsicRegion.abstractApplied]
        rw [UniformIntrinsicRegion.abstractAppliedItems_append]
        have sourceChildrenExact' := sourceChildrenExact
        dsimp [normalizedSourceHead] at sourceChildrenExact'
        have sourceChildrenNormalization :
            sourceChildren.renameWires
                (recursiveRegionNormalization sourceOuter region) =
              sourceChildren.renameWires
                (fun {_} value => sourceExact ▸ value) := by
          have regionNormalization := recursiveRegionNormalization_region
            sourceOuter region (.mk sourceChildren)
          rw [recursiveCastRegion_eq_rename] at regionNormalization
          injection regionNormalization
        rw [sourceChildrenNormalization]
        rw [sourceChildrenExact']
        unfold normalizedSourceRetained
        have ordinaryExact := recursiveSourceOrdinary_eq_retained
          sourceArguments sourceSignature result.sites sourceOuter region
          sourceNodes sourceRetained sourceNodesCompiled sourceRetainedCompiled
          sourceNodup sourceHead sourceHeadOrigin
        unfold recursiveNormalizedNodeShape at ordinaryExact
        cases nodeShape :
            UniformIntrinsicRegion.abstractAppliedItems normalizedSourceHead
              (sourceNodes.renameWires
                (recursiveRegionNormalization sourceOuter region)) with
        | mk ordinary nodeHoles =>
            rw [nodeShape] at ordinaryExact
            change ordinary = _ at ordinaryExact
            rw [← ordinaryExact]
            unfold recursiveNormalizedNodeShape
            dsimp [normalizedSourceHead] at nodeShape
            rw [nodeShape]
            simp [UniformIntrinsicRegion.holeValues,
              UniformIntrinsicRegion.appendAbstracted]
      · unfold shape
        rw [recursiveBlockReceipt_larger]
        rw [targetBodyExact, ConcreteElaboration.finishRegion_eq_signatures]
        rw [recursiveAbstract_finishRegionSignatures]
        apply congrArg (wrapArgumentBinds
          ((result.checked.val.wiresAt (result.regionImage region)).map fun
            localWire => (result.checked.val.wires localWire).sig))
        rw [← recursiveRegionNormalization_region targetOuter
          (result.regionImage region)]
        simp only [Region.renameWires,
          UniformIntrinsicRegion.ItemSeq.renameWires_append]
        simp only [UniformIntrinsicRegion.abstractApplied]
        rw [UniformIntrinsicRegion.abstractAppliedItems_append]
        have targetChildrenExact' := targetChildrenExact
        dsimp [normalizedTargetHead] at targetChildrenExact'
        have targetChildrenNormalization :
            targetChildren.renameWires
                (recursiveRegionNormalization targetOuter
                  (result.regionImage region)) =
              targetChildren.renameWires
                (fun {_} value => targetExact ▸ value) := by
          have regionNormalization := recursiveRegionNormalization_region
            targetOuter (result.regionImage region) (.mk targetChildren)
          rw [recursiveCastRegion_eq_rename] at regionNormalization
          injection regionNormalization
        rw [targetChildrenNormalization]
        rw [targetChildrenExact']
        unfold normalizedSourceRetained bounds
        rw [← retainedExact]
        have ordinaryExact := recursiveTargetOrdinary_eq_retained result
          targetOuter region targetNodes targetRetained targetNodesCompiled
          targetRetainedCompiled targetNodup targetHead targetHeadOrigin
        unfold recursiveNormalizedNodeShape at ordinaryExact
        cases nodeShape :
            UniformIntrinsicRegion.abstractAppliedItems normalizedTargetHead
              (targetNodes.renameWires
                (recursiveRegionNormalization targetOuter
                  (result.regionImage region))) with
        | mk ordinary nodeHoles =>
            rw [nodeShape] at ordinaryExact
            change ordinary = _ at ordinaryExact
            rw [← ordinaryExact]
            unfold recursiveNormalizedNodeShape
            dsimp [normalizedTargetHead] at nodeShape
            rw [nodeShape]
            simp [UniformIntrinsicRegion.holeValues,
              UniformIntrinsicRegion.appendAbstracted]

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
