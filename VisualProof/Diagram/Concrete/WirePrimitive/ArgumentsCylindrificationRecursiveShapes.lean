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

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
