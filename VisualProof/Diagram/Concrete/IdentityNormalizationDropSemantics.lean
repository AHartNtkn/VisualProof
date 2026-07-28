import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.IdentityNormalizationDropWellFormed
import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof

universe u

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationDropSemantics

private def dropNodes
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List source.val.NodeId :=
  retainedNodes source.val [node]

private def targetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Fin source.val.wiresList.length :=
  ⟨wire.val, by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, wire.isLt]⟩

@[simp] private theorem wiresList_get_targetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    source.val.wiresList.get (targetWire source wire) = wire := by
  apply Fin.ext
  simp [ConcreteDiagram.wiresList, targetWire,
    Data.Finite.allFin_eq_finRange]

private theorem targetWire_injective
    (source : CheckedDiagram definitions) :
    Function.Injective (targetWire source) := by
  intro left right equality
  apply Fin.ext
  simpa [targetWire] using congrArg Fin.val equality

private def targetRegion
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    (dropCandidate source node eligible).RegionId :=
  ⟨region.val, region.isLt⟩

@[simp] private theorem targetRegion_val
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    (targetRegion source node eligible region).val =
      region.val :=
  rfl

@[simp] private theorem targetRegion_eq
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    targetRegion source node eligible region = region := by
  apply Fin.ext
  rfl

private theorem targetRegion_injective
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    Function.Injective
      (targetRegion source node eligible) := by
  intro left right equality
  apply Fin.ext
  simpa using congrArg Fin.val equality

private theorem all_targetRegions
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    Data.Finite.allFin (dropCandidate source node eligible).regionCount =
      (Data.Finite.allFin source.val.regionCount).map
        (targetRegion source node eligible) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  apply List.ext_get
  · simp [dropCandidate]
  · intro index leftBound rightBound
    apply Fin.ext
    simp [targetRegion]

private theorem dropCandidate_childrenOf
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    (dropCandidate source node eligible).childrenOf
        (targetRegion source node eligible region) =
      (source.val.childrenOf region).map
        (targetRegion source node eligible) := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  rw [all_targetRegions source node eligible]
  rw [List.filter_map]
  apply congrArg (List.map (targetRegion source node eligible))
  apply List.filter_congr
  intro child _
  cases data : source.val.regions child <;>
    simp [dropCandidate, targetRegion, data] <;> rfl

private theorem dropCandidate_childrenOf_eq
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    (dropCandidate source node eligible).childrenOf region =
      source.val.childrenOf region := by
  calc
    (dropCandidate source node eligible).childrenOf region =
        (dropCandidate source node eligible).childrenOf
          (targetRegion source node eligible region) :=
      congrArg
        (ConcreteDiagram.childrenOf (dropCandidate source node eligible))
        (targetRegion_eq source node eligible region).symm
    _ = (source.val.childrenOf region).map
          (targetRegion source node eligible) :=
      dropCandidate_childrenOf source node eligible region
    _ = source.val.childrenOf region := by
      induction source.val.childrenOf region with
      | nil => rfl
      | cons head tail induction =>
          simp only [List.map_cons]
          rw [targetRegion_eq, induction]
          rfl

private def targetNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ node) :
    Fin (dropNodes source node).length :=
  (Data.Finite.indexOf? (dropNodes source node) sourceNode).get
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))

@[simp] private theorem dropNodes_get_targetNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ node) :
    (dropNodes source node).get
        (targetNode source node sourceNode survives) =
      sourceNode := by
  unfold targetNode
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))

private def targetEndpoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount)
    (survives : endpoint.node ≠ node) :
    CEndpoint (dropNodes source node).length :=
  ⟨targetNode source node endpoint.node survives, endpoint.port⟩

@[simp] private theorem dropCandidate_wire_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire : source.val.WireId) :
    ((dropCandidate source node eligible).wires
      (targetWire source wire)).sig =
      (source.val.wires wire).sig := by
  change
    (source.val.wires
      (source.val.wiresList.get (targetWire source wire))).sig =
      (source.val.wires wire).sig
  rw [wiresList_get_targetWire]

private theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ node)
    (port : CPort)
    (wire : source.val.WireId)
    (incident :
      (⟨sourceNode, port⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires wire).endpoints) :
    (⟨targetNode source node sourceNode survives, port⟩ :
      CEndpoint (dropCandidate source node eligible).nodeCount) ∈
        ((dropCandidate source node eligible).wires
          (targetWire source wire)).endpoints := by
  apply List.mem_filterMap.mpr
  refine
    ⟨(⟨sourceNode, port⟩ : CEndpoint source.val.nodeCount), ?_, ?_⟩
  · apply List.mem_filter.mpr
    constructor
    · rw [wiresList_get_targetWire]
      exact incident
    · simp [survives]
  · unfold reindexEndpoint?
    have found :
        Data.Finite.indexOf? (dropNodes source node) sourceNode =
          some (targetNode source node sourceNode survives) := by
      unfold targetNode
      exact (Option.some_get _).symm
    change
      (Data.Finite.indexOf? (dropNodes source node) sourceNode).map
          (fun target => (⟨target, port⟩ :
            CEndpoint (dropNodes source node).length)) =
        some (targetEndpoint source node
          ⟨sourceNode, port⟩ survives)
    rw [found]
    rfl

private def targetContext
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext
      (dropCandidate source node eligible) :=
  ⟨context.ids.map (targetWire source)⟩

private theorem targetContext_sigs
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val) :
    (targetContext source node eligible context).sigs =
      context.sigs := by
  unfold targetContext ConcreteElaboration.WireContext.sigs
  rw [List.map_map]
  apply List.map_inj_left.mpr
  intro wire _
  exact dropCandidate_wire_signature source node eligible wire

private def mappedHere
    (signature : targetSig = sourceSig) :
    Var (targetSig :: tail) sourceSig :=
  signature ▸ (Var.here : Var (targetSig :: tail) targetSig)

@[simp] private theorem origin_mappedHere
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (ids : List diagram.WireId)
    (signature : (diagram.wires wire).sig = sourceSig) :
    ConcreteElaboration.WireContext.origin diagram (wire :: ids)
        (mappedHere
          (tail := ids.map fun candidate =>
            (diagram.wires candidate).sig)
          signature) =
      wire := by
  cases signature
  rfl

private def contextRenamingFor
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (ids : List source.val.WireId) :
    WireRenaming
      (ids.map fun wire => (source.val.wires wire).sig)
      ((ids.map (targetWire source)).map fun wire =>
        ((dropCandidate source node eligible).wires wire).sig) :=
  match ids with
  | [] => fun value => nomatch value
  | head :: tail =>
      fun value =>
        match value with
        | Var.here =>
            mappedHere
              (tail :=
                (tail.map (targetWire source)).map fun wire =>
                  ((dropCandidate source node eligible).wires wire).sig)
              (dropCandidate_wire_signature source node eligible head)
        | Var.there value =>
            Var.there
              (contextRenamingFor source node eligible tail value)
termination_by ids

private def contextRenaming
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming context.sigs
      (targetContext source node eligible context).sigs :=
  contextRenamingFor source node eligible context.ids

private theorem contextRenaming_action
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val) :
    ∀ {sig} (value : Var context.sigs sig),
      ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          (targetContext source node eligible context).ids
          (contextRenaming source node eligible context value) =
        targetWire source
          (ConcreteElaboration.WireContext.origin
            source.val context.ids value) := by
  intro sig value
  cases context with
  | mk ids =>
      induction ids with
      | nil => nomatch value
      | cons head tail induction =>
          cases value with
          | here =>
              simp only [contextRenaming, targetContext,
                contextRenamingFor,
                ConcreteElaboration.WireContext.origin]
              exact origin_mappedHere
                (dropCandidate source node eligible)
                (targetWire source head)
                (tail.map (targetWire source))
                (dropCandidate_wire_signature source node eligible head)
          | there value =>
              simpa [contextRenaming, contextRenamingFor, targetContext,
                ConcreteElaboration.WireContext.origin] using induction value

private theorem targetContext_nodup
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (nodup : context.ids.Nodup) :
    (targetContext source node eligible context).ids.Nodup := by
  rw [List.nodup_iff_pairwise_ne] at nodup ⊢
  exact nodup.map (targetWire source) (by
    intro left right different equality
    exact different ((targetWire_injective source) equality))

private theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

private theorem all_targetWires
    (source : CheckedDiagram definitions) :
    Data.Finite.allFin source.val.wiresList.length =
      (Data.Finite.allFin source.val.wireCount).map (targetWire source) := by
  rw [Data.Finite.allFin_eq_finRange,
    Data.Finite.allFin_eq_finRange]
  apply List.ext_get
  · simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange]
  · intro index leftBound rightBound
    apply Fin.ext
    simp [ConcreteDiagram.wiresList, targetWire,
      List.get_eq_getElem]

private theorem dropCandidate_wiresAt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    (dropCandidate source node eligible).wiresAt region =
      (source.val.wiresAt region).map (targetWire source) := by
  unfold ConcreteDiagram.wiresAt
  change
    (Data.Finite.allFin source.val.wiresList.length).filter
        (fun wire =>
          (source.val.wires (source.val.wiresList.get wire)).scope ==
            region) =
      ((Data.Finite.allFin source.val.wireCount).filter
        (fun wire => (source.val.wires wire).scope == region)).map
          (targetWire source)
  rw [all_targetWires, List.filter_map]
  apply congrArg (List.map (targetWire source))
  apply List.filter_congr
  intro wire _
  exact congrArg
    (fun data => data.scope == region)
    (congrArg source.val.wires (wiresList_get_targetWire source wire))

private theorem targetContext_extend
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    targetContext source node eligible (context.extend region) =
      (targetContext source node eligible context).extend region := by
  cases context
  simp only [targetContext, ConcreteElaboration.WireContext.extend,
    dropCandidate_wiresAt, List.map_append]
  rfl

private def sourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    source.val.NodeId :=
  (dropNodes source node).get target

private theorem sourceNode_ne
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    sourceNode source node target ≠ node := by
  have member := List.get_mem (dropNodes source node) target
  have accepted := (List.mem_filter.mp member).2
  exact by
    simpa [sourceNode, dropNodes, retainedNodes] using
      of_decide_eq_true accepted

@[simp] private theorem targetNode_sourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : Fin (dropNodes source node).length) :
    targetNode source node (sourceNode source node target)
        (sourceNode_ne source node target) =
      target := by
  have nodup : (dropNodes source node).Nodup := by
    exact (Data.Finite.allFin_nodup source.val.nodeCount).filter _
  symm
  apply Data.Finite.indexOf?_unique_of_nodup nodup
  · exact Option.eq_some_of_isSome
      (Data.Finite.indexOf?_isSome_iff.mpr (by
        exact List.get_mem (dropNodes source node) target))
  · rfl

private theorem dropCandidate_nodesAt_sources
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (region : source.val.RegionId) :
    ((dropCandidate source node eligible).nodesAt region).map
        (sourceNode source node) =
      (source.val.nodesAt region).filter
        (fun candidate => decide (candidate ≠ node)) := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (((Data.Finite.allFin (dropNodes source node).length).filter
      ((fun candidate =>
        (source.val.nodes candidate).region == region) ∘
          sourceNode source node)).map (sourceNode source node)) =
      (((Data.Finite.allFin source.val.nodeCount).filter
        (fun candidate => (source.val.nodes candidate).region == region)).filter
          (fun candidate => decide (candidate ≠ node)))
  rw [← List.filter_map]
  have allSources :
      (Data.Finite.allFin (dropNodes source node).length).map
          (sourceNode source node) =
        dropNodes source node := by
    simpa [sourceNode] using map_get_allFin (dropNodes source node)
  rw [allSources]
  simp only [dropNodes, retainedNodes,
    List.filter_filter]
  apply List.filter_congr
  intro candidate _
  simpa using
    (Bool.and_comm
      ((source.val.nodes candidate).region == region)
      (decide (candidate ≠ node)))

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
          ConcreteElaboration.compileNodes? definitions diagram context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes?_cons_split
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: nodes) =
        some items) :
    ∃ (headItems tailItems : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some headItems ∧
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some tailItems ∧
      items = headItems.append tailItems := by
  rw [compileNodes?_cons_eq_singleton_bind] at compiled
  obtain ⟨headItems, headCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨tailItems, tailCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have equality : headItems.append tailItems = items :=
    Option.some.inj compiled
  subst items
  exact ⟨headItems, tailItems, headCompiled, tailCompiled, rfl⟩

private theorem ItemSeq.renameWires_append
    (rho : WireRenaming source target) :
    (left right : ItemSeq definitions source) →
      (left.append right).renameWires rho =
        (left.renameWires rho).append (right.renameWires rho)
  | .nil, _ => rfl
  | .cons head tail, right =>
      congrArg (ItemSeq.cons (head.renameWires rho))
        (ItemSeq.renameWires_append rho tail right)

private theorem survivingNode_singleton_natural
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (target : Fin (dropNodes source node).length)
    {sourceItems : ItemSeq definitions context.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [sourceNode source node target] =
        some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions
          (targetContext source node eligible context).sigs,
      ConcreteElaboration.compileNodes? definitions
          (dropCandidate source node eligible)
          (targetContext source node eligible context) [target] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (contextRenaming source node eligible context) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    (IdentityNormalizationCore.dropCandidate_wellFormed
      source node eligible)
    (targetContext_nodup source node eligible context contextNodup)
    (contextRenaming source node eligible context)
    (targetWire source)
    (dropCandidate_wire_signature source node eligible)
    (contextRenaming_action source node eligible context)
    (fun region => region)
    (sourceNode source node target)
    target
  · simp only [dropCandidate, sourceNode, dropNodes]
    generalize nodeData :
      source.val.nodes ((retainedNodes source.val [node]).get target) =
        data
    cases data <;> simp
  · intro port wire incident
    simpa using
      targetEndpoint_incident source node eligible
        (sourceNode source node target)
        (sourceNode_ne source node target) port wire incident
  · exact sourceCompiled

private theorem survivingNodes_natural
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup) :
    ∀ (targets : List (Fin (dropNodes source node).length))
      {sourceItems : ItemSeq definitions context.sigs},
      ConcreteElaboration.compileNodes? definitions source.val context
          (targets.map (sourceNode source node)) =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions
            (targetContext source node eligible context).sigs,
        ConcreteElaboration.compileNodes? definitions
            (dropCandidate source node eligible)
            (targetContext source node eligible context) targets =
          some targetItems ∧
        targetItems =
          sourceItems.renameWires
            (contextRenaming source node eligible context) := by
  intro targets
  induction targets with
  | nil =>
      intro sourceItems sourceCompiled
      have equality :
          (ItemSeq.nil : ItemSeq definitions context.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?], rfl⟩
  | cons target tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, headCompiled, tailCompiled,
          sourceEquality⟩ :=
        compileNodes?_cons_split definitions source.val context
          (sourceNode source node target)
          (tail.map (sourceNode source node)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        survivingNode_singleton_natural source node eligible context
          contextNodup target headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · calc
          ConcreteElaboration.compileNodes? definitions
              (dropCandidate source node eligible)
              (targetContext source node eligible context)
              (target :: tail) =
              (do
                let headItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (dropCandidate source node eligible)
                    (targetContext source node eligible context) [target]
                let tailItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (dropCandidate source node eligible)
                    (targetContext source node eligible context) tail
                pure (headItems.append tailItems)) :=
            compileNodes?_cons_eq_singleton_bind definitions
              (dropCandidate source node eligible)
              (targetContext source node eligible context) target tail
          _ = some (targetHead.append targetTail) := by
            simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there value =>
          exact List.mem_cons_of_mem head (induction value)

private def sourceWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire : (dropCandidate source node eligible).WireId) :
    source.val.WireId :=
  ⟨wire.val, by
    simpa [dropCandidate, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange] using wire.isLt⟩

@[simp] private theorem sourceWire_targetWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire : source.val.WireId) :
    sourceWire source node eligible (targetWire source wire) = wire := by
  apply Fin.ext
  rfl

@[simp] private theorem targetWire_sourceWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (wire : (dropCandidate source node eligible).WireId) :
    targetWire source (sourceWire source node eligible wire) = wire := by
  apply Fin.ext
  rfl

private def varForMember
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId) :
    (ids : List diagram.WireId) →
      wire ∈ ids →
      Var (ids.map fun candidate => (diagram.wires candidate).sig)
        (diagram.wires wire).sig
  | [], member => by simp at member
  | head :: tail, member =>
      if equality : wire = head then
        equality ▸ .here
      else
        .there (varForMember diagram wire tail (by
          simpa [equality] using member))

@[simp] private theorem origin_varForMember
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId)
    (ids : List diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (varForMember diagram wire ids member) =
      wire := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      unfold varForMember
      split
      · rename_i equality
        subst head
        rfl
      · simp only [ConcreteElaboration.WireContext.origin]
        exact induction _

private def castVar
    (equality : sourceSig = targetSig)
    (value : Var context sourceSig) :
    Var context targetSig :=
  equality ▸ value

@[simp] private theorem origin_castVar
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {sourceSig targetSig : Sig}
    (equality : sourceSig = targetSig)
    (value : Var context.sigs sourceSig) :
    ConcreteElaboration.WireContext.origin diagram context.ids
        (castVar equality value) =
      ConcreteElaboration.WireContext.origin diagram context.ids value := by
  cases equality
  rfl

@[simp] private theorem origin_castVarFor
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sourceSig targetSig : Sig}
    (equality : sourceSig = targetSig)
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sourceSig) :
    ConcreteElaboration.WireContext.origin diagram ids
        (castVar equality value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases equality
  rfl

private def contextSection
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming (targetContext source node eligible context).sigs
      context.sigs :=
  fun {sig} value =>
    let targetOrigin :=
      ConcreteElaboration.WireContext.origin
        (dropCandidate source node eligible)
        (targetContext source node eligible context).ids value
    let original := sourceWire source node eligible targetOrigin
    let sourceMember : original ∈ context.ids := by
      have targetMember :=
        origin_mem (dropCandidate source node eligible) value
      rcases List.mem_map.mp targetMember with
        ⟨wire, member, equality⟩
      have originalEquality : original = wire := by
        rw [← sourceWire_targetWire source node eligible wire, equality]
      exact originalEquality.symm ▸ member
    let sourceVar :=
      varForMember source.val original context.ids sourceMember
    let signature : (source.val.wires original).sig = sig :=
      (dropCandidate_wire_signature source node eligible original).symm.trans
        ((congrArg
          (fun wire =>
            ((dropCandidate source node eligible).wires wire).sig)
          (targetWire_sourceWire source node eligible targetOrigin)).trans
        (ConcreteElaboration.WireContext.origin_signature
          (dropCandidate source node eligible)
          (targetContext source node eligible context).ids value))
    castVar signature sourceVar

private theorem contextSection_origin
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    {sig : Sig}
    (value :
      Var (targetContext source node eligible context).sigs sig) :
    ConcreteElaboration.WireContext.origin source.val context.ids
        (contextSection source node eligible context value) =
      sourceWire source node eligible
        (ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          (targetContext source node eligible context).ids value) := by
  unfold contextSection
  dsimp only
  exact
    (origin_castVarFor source.val context.ids _ _).trans
      (origin_varForMember _ _ _ _)

private theorem contextSection_action
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    {sig : Sig}
    (value :
      Var (targetContext source node eligible context).sigs sig) :
    targetWire source
        (ConcreteElaboration.WireContext.origin source.val context.ids
          (contextSection source node eligible context value)) =
      ConcreteElaboration.WireContext.origin
        (dropCandidate source node eligible)
        (targetContext source node eligible context).ids value := by
  rw [contextSection_origin,
    targetWire_sourceWire source node eligible]

private theorem origin_injective_of_nodup
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId}
    (nodup : ids.Nodup)
    {sig : Sig}
    (left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig)
    (sameOrigin :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  induction ids with
  | nil => exact nomatch left
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have member := origin_mem diagram right
              have equality :
                  head =
                    ConcreteElaboration.WireContext.origin
                      diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [← equality] at member
              exact (nodup.1 member).elim
      | there left =>
          cases right with
          | here =>
              have member := origin_mem diagram left
              have equality :
                  ConcreteElaboration.WireContext.origin
                      diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using
                  sameOrigin
              rw [equality] at member
              exact (nodup.1 member).elim
          | there right =>
              exact congrArg Var.there
                (induction nodup.2 left right (by
                  simpa [ConcreteElaboration.WireContext.origin] using
                    sameOrigin))

private theorem contextRenaming_section
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (targetNodup :
      (targetContext source node eligible context).ids.Nodup)
    {sig : Sig}
    (value :
      Var (targetContext source node eligible context).sigs sig) :
    contextRenaming source node eligible context
        (contextSection source node eligible context value) =
      value := by
  apply origin_injective_of_nodup
    (dropCandidate source node eligible) targetNodup
  rw [contextRenaming_action, contextSection_action]

private theorem contextSection_renaming
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (sourceNodup : context.ids.Nodup)
    {sig : Sig} (value : Var context.sigs sig) :
    contextSection source node eligible context
        (contextRenaming source node eligible context value) =
      value := by
  apply origin_injective_of_nodup source.val sourceNodup
  apply targetWire_injective source
  rw [contextSection_action, contextRenaming_action]

private theorem eq_of_mem_of_length_lt_two
    {values : List α}
    (short : values.length < 2)
    {left right : α}
    (leftMember : left ∈ values)
    (rightMember : right ∈ values) :
    left = right := by
  cases values with
  | nil => simp at leftMember
  | cons head tail =>
      have tailEmpty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons second rest =>
            simp only [List.length_cons] at short
            omega
      subst tail
      simp only [List.mem_singleton] at leftMember rightMember
      exact leftMember.trans rightMember.symm

private theorem droppedNode_denotes
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    {items : ItemSeq definitions context.sigs}
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val context [node] =
        some items)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs) :
    denoteItemSeq pre definitionEnv env items := by
  obtain ⟨ports, two, itemsEquality, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      source.val source.property context node eligible.identity.node_eq compiled
  subst items
  simp only [denoteItemSeq_cons, denoteItem_identity,
    denoteItemSeq_nil, and_true]
  intro left leftMember right rightMember
  rcases List.mem_map.mp leftMember with
    ⟨leftVar, leftVarMember, rfl⟩
  rcases List.mem_map.mp rightMember with
    ⟨rightVar, rightVarMember, rfl⟩
  have sameOrigin :
      ConcreteElaboration.WireContext.origin source.val context.ids leftVar =
        ConcreteElaboration.WireContext.origin
          source.val context.ids rightVar :=
    eq_of_mem_of_length_lt_two eligible.incident_lt_two
      ((origins _).mpr ⟨leftVar, leftVarMember, rfl⟩)
      ((origins _).mpr ⟨rightVar, rightVarMember, rfl⟩)
  rw [origin_injective_of_nodup source.val contextNodup
    leftVar rightVar sameOrigin]

private theorem dropNode_filter_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (nodes : List source.val.NodeId)
    {fullItems filteredItems : ItemSeq definitions context.sigs}
    (fullCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context nodes =
        some fullItems)
    (filteredCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (nodes.filter fun candidate => decide (candidate ≠ node)) =
        some filteredItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs) :
    denoteItemSeq pre definitionEnv env filteredItems ↔
      denoteItemSeq pre definitionEnv env fullItems := by
  induction nodes generalizing fullItems filteredItems with
  | nil =>
      simp [ConcreteElaboration.compileNodes?] at fullCompiled filteredCompiled
      subst fullItems
      subst filteredItems
      rfl
  | cons head tail induction =>
      obtain ⟨fullHead, fullTail, fullHeadCompiled, fullTailCompiled,
          fullEquality⟩ :=
        compileNodes?_cons_split definitions source.val context
          head tail fullItems fullCompiled
      by_cases removed : head = node
      · subst head
        have rejected : decide (node ≠ node) = false := by simp
        rw [List.filter_cons, rejected] at filteredCompiled
        simp only [Bool.false_eq_true, ↓reduceIte] at filteredCompiled
        have tailNatural :=
          induction fullTailCompiled filteredCompiled
        have headTrue :=
          droppedNode_denotes source node eligible context contextNodup
            fullHeadCompiled pre definitionEnv env
        rw [fullEquality, denoteItemSeq_append, tailNatural]
        exact ⟨fun tailDenotes => ⟨headTrue, tailDenotes⟩,
          fun both => both.2⟩
      · have accepted : decide (head ≠ node) = true :=
          decide_eq_true removed
        rw [List.filter_cons, accepted] at filteredCompiled
        simp only [↓reduceIte] at filteredCompiled
        obtain ⟨filteredHead, filteredTail, filteredHeadCompiled,
            filteredTailCompiled, filteredEquality⟩ :=
          compileNodes?_cons_split definitions source.val context
            head (tail.filter fun candidate => decide (candidate ≠ node))
            filteredItems filteredCompiled
        have headEquality : filteredHead = fullHead :=
          Option.some.inj
            (filteredHeadCompiled.symm.trans fullHeadCompiled)
        have tailNatural :=
          induction fullTailCompiled filteredTailCompiled
        rw [fullEquality, filteredEquality, headEquality,
          denoteItemSeq_append, denoteItemSeq_append]
        exact and_congr_right fun _ => tailNatural

private theorem compileNodes?_filter_drop
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (removed : diagram.NodeId) :
    ∀ (nodes : List diagram.NodeId)
      {items : ItemSeq definitions context.sigs},
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some items →
      ∃ filteredItems,
        ConcreteElaboration.compileNodes? definitions diagram context
            (nodes.filter fun node => !decide (node = removed)) =
          some filteredItems := by
  intro nodes
  induction nodes with
  | nil =>
      intro items compiled
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?]⟩
  | cons head tail induction =>
      intro items compiled
      obtain ⟨headItems, tailItems, headCompiled, tailCompiled, _⟩ :=
        compileNodes?_cons_split definitions diagram context
          head tail items compiled
      obtain ⟨filteredTail, filteredTailCompiled⟩ :=
        induction tailCompiled
      by_cases equal : head = removed
      · have rejected : (!decide (head = removed)) = false := by
          simp [equal]
        refine ⟨filteredTail, ?_⟩
        rw [List.filter_cons, rejected]
        simpa using filteredTailCompiled
      · have accepted : (!decide (head = removed)) = true := by
          simp [equal]
        refine ⟨headItems.append filteredTail, ?_⟩
        rw [List.filter_cons, accepted]
        simp only [↓reduceIte]
        calc
          ConcreteElaboration.compileNodes? definitions diagram context
              (head :: tail.filter fun node => !decide (node = removed)) =
              (do
                let singleton ←
                  ConcreteElaboration.compileNodes? definitions diagram
                    context [head]
                let rest ←
                  ConcreteElaboration.compileNodes? definitions diagram
                    context (tail.filter fun node => !decide (node = removed))
                pure (singleton.append rest)) :=
            compileNodes?_cons_eq_singleton_bind definitions diagram context
              head (tail.filter fun node => !decide (node = removed))
          _ = some (headItems.append filteredTail) := by
            simp [headCompiled, filteredTailCompiled]

private def extendedContextRenaming
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    WireRenaming (context.extend region).sigs
      ((targetContext source node eligible context).extend region).sigs :=
  fun {_} value =>
    congrArg ConcreteElaboration.WireContext.sigs
        (targetContext_extend source node eligible context region) ▸
      contextRenaming source node eligible (context.extend region) value

private theorem origin_context_cast
    (diagram : ConcreteDiagram definitionCount)
    (left right : ConcreteElaboration.WireContext diagram)
    (same : left = right)
    {sig : Sig} (value : Var left.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

private theorem extendedContextRenaming_action
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    ∀ {sig} (value : Var (context.extend region).sigs sig),
      ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          ((targetContext source node eligible context).extend region).ids
          (extendedContextRenaming source node eligible context region value) =
        targetWire source
          (ConcreteElaboration.WireContext.origin source.val
            (context.extend region).ids value) := by
  intro sig value
  calc
    _ = ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          (targetContext source node eligible
            (context.extend region)).ids
          (contextRenaming source node eligible
            (context.extend region) value) :=
      origin_context_cast
        (dropCandidate source node eligible)
        (targetContext source node eligible (context.extend region))
        ((targetContext source node eligible context).extend region)
        (targetContext_extend source node eligible context region)
        (contextRenaming source node eligible (context.extend region) value)
    _ = _ :=
      contextRenaming_action source node eligible
        (context.extend region) value

private def extendedContextSection
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    WireRenaming
      ((targetContext source node eligible context).extend region).sigs
      (context.extend region).sigs :=
  fun {_} value =>
    contextSection source node eligible (context.extend region)
      (congrArg ConcreteElaboration.WireContext.sigs
        (targetContext_extend source node eligible context region).symm ▸
          value)

private theorem extendedContextSection_action
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    {sig : Sig}
    (value :
      Var
        ((targetContext source node eligible context).extend region).sigs
        sig) :
    targetWire source
        (ConcreteElaboration.WireContext.origin source.val
          (context.extend region).ids
          (extendedContextSection source node eligible context region
            value)) =
      ConcreteElaboration.WireContext.origin
        (dropCandidate source node eligible)
        ((targetContext source node eligible context).extend region).ids
        value := by
  unfold extendedContextSection
  rw [contextSection_action]
  exact origin_context_cast
    (dropCandidate source node eligible)
    ((targetContext source node eligible context).extend region)
    (targetContext source node eligible (context.extend region))
    (targetContext_extend source node eligible context region).symm
    value

private theorem extendedContextRenaming_section
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (targetExtendedNodup :
      ((targetContext source node eligible context).extend region).ids.Nodup)
    {sig : Sig}
    (value :
      Var
        ((targetContext source node eligible context).extend region).sigs
        sig) :
    extendedContextRenaming source node eligible context region
        (extendedContextSection source node eligible context region value) =
      value := by
  apply origin_injective_of_nodup
    (dropCandidate source node eligible) targetExtendedNodup
  rw [extendedContextRenaming_action, extendedContextSection_action]

private theorem extendedContextSection_renaming
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    {sig : Sig}
    (value : Var (context.extend region).sigs sig) :
    extendedContextSection source node eligible context region
        (extendedContextRenaming source node eligible context region value) =
      value := by
  apply origin_injective_of_nodup source.val sourceExtendedNodup
  apply targetWire_injective source
  rw [extendedContextSection_action, extendedContextRenaming_action]

private theorem extendedEnvironment_roundtrip_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (pre : PreModel)
    (env : Env pre (context.extend region).sigs) :
    Env.comp
        (Env.comp env
          (extendedContextSection source node eligible context region))
        (extendedContextRenaming source node eligible context region) =
      env := by
  funext sig value
  exact congrArg (env sig)
    (extendedContextSection_renaming source node eligible context region
      sourceExtendedNodup value)

private theorem origin_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (leftIds rightIds : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (rightIds.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram (leftIds ++ rightIds)
        (ConcreteElaboration.appendRightVar diagram leftIds value) =
      ConcreteElaboration.WireContext.origin diagram rightIds value := by
  induction leftIds with
  | nil => rfl
  | cons head tail induction =>
      exact induction

private theorem extendedContextSection_appendRight
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    {sig : Sig}
    (value :
      Var (targetContext source node eligible context).sigs sig) :
    extendedContextSection source node eligible context region
        (ConcreteElaboration.appendRightVar
          (dropCandidate source node eligible)
          ((dropCandidate source node eligible).wiresAt region) value) =
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region)
        (contextSection source node eligible context value) := by
  apply origin_injective_of_nodup source.val sourceExtendedNodup
  apply targetWire_injective source
  rw [extendedContextSection_action]
  simp only [ConcreteElaboration.WireContext.extend]
  rw [origin_appendRightVar, origin_appendRightVar,
    contextSection_action]

private theorem extendedEnvironment_natural
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (pre : PreModel)
    (targetValues :
      ConcreteElaboration.WireValues pre
        (((dropCandidate source node eligible).wiresAt region).map
          fun wire =>
            ((dropCandidate source node eligible).wires wire).sig))
    (targetEnv :
      Env pre (targetContext source node eligible context).sigs) :
    let targetExtended :=
      ConcreteElaboration.extendEnvironment
        (dropCandidate source node eligible)
        (targetContext source node eligible context) region
        targetValues targetEnv
    let sourceEnv :=
      Env.comp targetExtended
        (extendedContextRenaming source node eligible context region)
    ConcreteElaboration.extendEnvironment source.val context region
        (ConcreteElaboration.valuesFromEnvironmentFor source.val context.ids
          (source.val.wiresAt region) sourceEnv)
        (Env.comp targetEnv
          (contextRenaming source node eligible context)) =
      sourceEnv := by
  simp only
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig outer
  let sourceOuter :=
    ConcreteElaboration.appendRightVar
      source.val (source.val.wiresAt region) outer
  let targetOuter :=
    ConcreteElaboration.appendRightVar
      (dropCandidate source node eligible)
      ((dropCandidate source node eligible).wiresAt region)
      (contextRenaming source node eligible context outer)
  have targetExtendedNodup :
      ((targetContext source node eligible context).extend region).ids.Nodup := by
    have mapped :=
      targetContext_nodup source node eligible
        (context.extend region) sourceExtendedNodup
    simpa [targetContext_extend source node eligible context region] using
      mapped
  have sameOrigin :
      ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          ((targetContext source node eligible context).extend region).ids
          (extendedContextRenaming source node eligible context region
            sourceOuter) =
        ConcreteElaboration.WireContext.origin
          (dropCandidate source node eligible)
          ((targetContext source node eligible context).extend region).ids
          targetOuter := by
    dsimp [sourceOuter, targetOuter]
    rw [extendedContextRenaming_action]
    simp only [ConcreteElaboration.WireContext.extend]
    rw [
      origin_appendRightVar, origin_appendRightVar,
      contextRenaming_action]
  have sameVar :=
    origin_injective_of_nodup
      (dropCandidate source node eligible)
      targetExtendedNodup
      (extendedContextRenaming source node eligible context region sourceOuter)
      targetOuter sameOrigin
  change
    ConcreteElaboration.extendEnvironment
        (dropCandidate source node eligible)
        (targetContext source node eligible context) region
        targetValues targetEnv sig
        (extendedContextRenaming source node eligible context region
          sourceOuter) =
      targetEnv sig
        (contextRenaming source node eligible context outer)
  rw [sameVar]
  exact ConcreteElaboration.extendEnvironment_appendRightVar
    (dropCandidate source node eligible)
    (targetContext source node eligible context) region
    targetValues targetEnv
    (contextRenaming source node eligible context outer)

private theorem reverseExtendedEnvironment_natural
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (targetNodup :
      (targetContext source node eligible context).ids.Nodup)
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((source.val.wiresAt region).map fun wire =>
          (source.val.wires wire).sig))
    (sourceEnv : Env pre context.sigs)
    (targetEnv :
      Env pre (targetContext source node eligible context).sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv
          (contextRenaming source node eligible context)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val context region
        sourceValues sourceEnv
    let targetExtended :=
      Env.comp sourceExtended
        (extendedContextSection source node eligible context region)
    ConcreteElaboration.extendEnvironment
        (dropCandidate source node eligible)
        (targetContext source node eligible context) region
        (ConcreteElaboration.valuesFromEnvironmentFor
          (dropCandidate source node eligible)
          (targetContext source node eligible context).ids
          ((dropCandidate source node eligible).wiresAt region)
          targetExtended)
        targetEnv =
      targetExtended := by
  simp only
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  change
    ConcreteElaboration.extendEnvironment source.val context region
        sourceValues sourceEnv sig
        (extendedContextSection source node eligible context region
          (ConcreteElaboration.appendRightVar
            (dropCandidate source node eligible)
            ((dropCandidate source node eligible).wiresAt region) value)) =
      targetEnv sig value
  rw [extendedContextSection_appendRight source node eligible context region
      sourceExtendedNodup,
    ConcreteElaboration.extendEnvironment_appendRightVar,
    outerRelated]
  change
    targetEnv sig
        (contextRenaming source node eligible context
          (contextSection source node eligible context value)) =
      targetEnv sig value
  rw [contextRenaming_section source node eligible context targetNodup]

private theorem survivingNode_singleton_natural_extended
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (targetExtendedNodup :
      ((targetContext source node eligible context).extend region).ids.Nodup)
    (target : Fin (dropNodes source node).length)
    {sourceItems : ItemSeq definitions (context.extend region).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) [sourceNode source node target] =
        some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions
          ((targetContext source node eligible context).extend region).sigs,
      ConcreteElaboration.compileNodes? definitions
          (dropCandidate source node eligible)
          ((targetContext source node eligible context).extend region)
          [target] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (extendedContextRenaming source node eligible context region) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    (IdentityNormalizationCore.dropCandidate_wellFormed
      source node eligible)
    targetExtendedNodup
    (extendedContextRenaming source node eligible context region)
    (targetWire source)
    (dropCandidate_wire_signature source node eligible)
    (extendedContextRenaming_action source node eligible context region)
    (fun region => region)
    (sourceNode source node target)
    target
  · simp only [dropCandidate, sourceNode, dropNodes]
    generalize nodeData :
      source.val.nodes ((retainedNodes source.val [node]).get target) =
        data
    cases data <;> simp
  · intro port wire incident
    simpa using
      targetEndpoint_incident source node eligible
        (sourceNode source node target)
        (sourceNode_ne source node target) port wire incident
  · exact sourceCompiled

private theorem survivingNodes_natural_extended
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (targetExtendedNodup :
      ((targetContext source node eligible context).extend region).ids.Nodup) :
    ∀ (targets : List (Fin (dropNodes source node).length))
      {sourceItems : ItemSeq definitions (context.extend region).sigs},
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region)
          (targets.map (sourceNode source node)) =
        some sourceItems →
      ∃ targetItems :
          ItemSeq definitions
            ((targetContext source node eligible context).extend region).sigs,
        ConcreteElaboration.compileNodes? definitions
            (dropCandidate source node eligible)
            ((targetContext source node eligible context).extend region)
            targets =
          some targetItems ∧
        targetItems =
          sourceItems.renameWires
            (extendedContextRenaming source node eligible context region) := by
  intro targets
  induction targets with
  | nil =>
      intro sourceItems sourceCompiled
      have equality :
          (ItemSeq.nil :
            ItemSeq definitions (context.extend region).sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileNodes?] using sourceCompiled)
      subst sourceItems
      exact ⟨.nil, by simp [ConcreteElaboration.compileNodes?], rfl⟩
  | cons target tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨sourceHead, sourceTail, headCompiled, tailCompiled,
          sourceEquality⟩ :=
        compileNodes?_cons_split definitions source.val
          (context.extend region)
          (sourceNode source node target)
          (tail.map (sourceNode source node)) sourceItems
          (by simpa using sourceCompiled)
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        survivingNode_singleton_natural_extended source node eligible
          context region targetExtendedNodup target headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · calc
          ConcreteElaboration.compileNodes? definitions
              (dropCandidate source node eligible)
              ((targetContext source node eligible context).extend region)
              (target :: tail) =
              (do
                let headItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (dropCandidate source node eligible)
                    ((targetContext source node eligible context).extend region)
                    [target]
                let tailItems ←
                  ConcreteElaboration.compileNodes? definitions
                    (dropCandidate source node eligible)
                    ((targetContext source node eligible context).extend region)
                    tail
                pure (headItems.append tailItems)) :=
            compileNodes?_cons_eq_singleton_bind definitions
              (dropCandidate source node eligible)
              ((targetContext source node eligible context).extend region)
              target tail
          _ = some (targetHead.append targetTail) := by
            simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

private theorem compiledNodes_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source node eligible context).extend region).sigs)
    (sourceItems : ItemSeq definitions (context.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetItems :
      ItemSeq definitions
        ((targetContext source node eligible context).extend region).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (dropCandidate source node eligible)
          ((targetContext source node eligible context).extend region)
          ((dropCandidate source node eligible).nodesAt region) =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source node eligible context region))
        sourceItems := by
  obtain ⟨filteredItems, filteredCompiled⟩ :=
    compileNodes?_filter_drop definitions source.val
      (context.extend region) node (source.val.nodesAt region) sourceCompiled
  have filteredCompiled' :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region)
          ((source.val.nodesAt region).filter
            fun candidate => decide (candidate ≠ node)) =
        some filteredItems := by
    simpa [Bool.not_eq_true] using filteredCompiled
  have sourceTargetsCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region)
          (((dropCandidate source node eligible).nodesAt region).map
            (sourceNode source node)) =
        some filteredItems := by
    rw [dropCandidate_nodesAt_sources]
    exact filteredCompiled'
  have targetExtendedNodup :
      ((targetContext source node eligible context).extend region).ids.Nodup := by
    have mapped :=
      targetContext_nodup source node eligible
        (context.extend region) sourceExtendedNodup
    simpa [targetContext_extend source node eligible context region] using
      mapped
  obtain ⟨expectedItems, expectedCompiled, expectedEquality⟩ :=
    survivingNodes_natural_extended source node eligible context region
      targetExtendedNodup
      ((dropCandidate source node eligible).nodesAt region)
      sourceTargetsCompiled
  have targetEquality : targetItems = expectedItems :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  have targetDenotation :
      denoteItemSeq pre definitionEnv targetEnv targetItems ↔
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (extendedContextRenaming source node eligible context region))
          filteredItems := by
    rw [targetEquality, expectedEquality, denoteItemSeq_renameWires]
  exact targetDenotation.trans
    (dropNode_filter_denotation source node eligible
      (context.extend region) sourceExtendedNodup
      (source.val.nodesAt region) sourceCompiled filteredCompiled'
      pre definitionEnv
      (Env.comp targetEnv
        (extendedContextRenaming source node eligible context region)))

private theorem compileChildren_denotation
    (definitions : List (List Sig))
    (source target : ConcreteDiagram definitions.length)
    (sourceRecurse : (region : source.RegionId) →
      (context : ConcreteElaboration.WireContext source) →
      Option (Region definitions context.sigs))
    (targetRecurse : (region : target.RegionId) →
      (context : ConcreteElaboration.WireContext target) →
      Option (Region definitions context.sigs))
    (sourceContext : ConcreteElaboration.WireContext source)
    (targetContext : ConcreteElaboration.WireContext target)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs) :
    ∀ (children : List source.RegionId)
      (mapRegion : source.RegionId → target.RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs}
      {targetItems : ItemSeq definitions targetContext.sigs},
      ConcreteElaboration.compileChildrenWith? definitions source
          sourceRecurse sourceContext children =
        some sourceItems →
      ConcreteElaboration.compileChildrenWith? definitions target
          targetRecurse targetContext
          (children.map mapRegion) =
        some targetItems →
      (∀ child, child ∈ children →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse (mapRegion child) targetContext =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv sourceEnv sourceBody)) →
      (denoteItemSeq pre definitionEnv targetEnv targetItems ↔
        denoteItemSeq pre definitionEnv sourceEnv sourceItems) := by
  intro children mapRegion
  induction children with
  | nil =>
      intro sourceItems targetItems sourceCompiled targetCompiled _
      have sourceEquality :
          (ItemSeq.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileChildrenWith?] using
            sourceCompiled)
      have targetEquality :
          (ItemSeq.nil : ItemSeq definitions targetContext.sigs) =
            targetItems :=
        Option.some.inj (by
          simpa [ConcreteElaboration.compileChildrenWith?] using
            targetCompiled)
      subst sourceItems
      subst targetItems
      simp
  | cons child tail induction =>
      intro sourceItems targetItems sourceCompiled targetCompiled recurse
      cases sourceHeadEq : sourceRecurse child sourceContext with
      | none =>
          simp [ConcreteElaboration.compileChildrenWith?,
            sourceHeadEq] at sourceCompiled
      | some sourceBody =>
          cases sourceTailEq :
              ConcreteElaboration.compileChildrenWith? definitions source
                sourceRecurse sourceContext tail with
          | none =>
              simp [ConcreteElaboration.compileChildrenWith?,
                sourceHeadEq, sourceTailEq] at sourceCompiled
          | some sourceTail =>
              cases targetHeadEq :
                  targetRecurse (mapRegion child) targetContext with
              | none =>
                  simp [ConcreteElaboration.compileChildrenWith?,
                    targetHeadEq] at targetCompiled
              | some targetBody =>
                  cases targetTailEq :
                      ConcreteElaboration.compileChildrenWith?
                        definitions target targetRecurse targetContext
                        (tail.map mapRegion) with
                  | none =>
                      simp [ConcreteElaboration.compileChildrenWith?,
                        targetHeadEq, targetTailEq] at targetCompiled
                  | some targetTail =>
                      have sourceEquality :
                          (ItemSeq.cons (.cut sourceBody) sourceTail :
                            ItemSeq definitions sourceContext.sigs) =
                            sourceItems :=
                        Option.some.inj (by
                          simpa [ConcreteElaboration.compileChildrenWith?,
                            sourceHeadEq, sourceTailEq] using sourceCompiled)
                      have targetEquality :
                          (ItemSeq.cons (.cut targetBody) targetTail :
                            ItemSeq definitions targetContext.sigs) =
                            targetItems :=
                        Option.some.inj (by
                          simpa [ConcreteElaboration.compileChildrenWith?,
                            targetHeadEq, targetTailEq] using targetCompiled)
                      subst sourceItems
                      subst targetItems
                      rw [denoteItemSeq_cons, denoteItemSeq_cons]
                      change
                        (¬ denoteRegion pre definitionEnv targetEnv
                            targetBody) ∧
                            denoteItemSeq pre definitionEnv targetEnv
                              targetTail ↔
                          (¬ denoteRegion pre definitionEnv sourceEnv
                            sourceBody) ∧
                            denoteItemSeq pre definitionEnv sourceEnv
                              sourceTail
                      exact and_congr
                        (not_congr
                          (recurse child (by simp) sourceBody targetBody
                            sourceHeadEq targetHeadEq))
                        (induction sourceTailEq targetTailEq (by
                          intro candidate member
                          exact recurse candidate (by simp [member])))

private def contextRenamingInto
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (candidateContext :
      ConcreteElaboration.WireContext (dropCandidate source node eligible))
    (contextEquality :
      candidateContext =
        targetContext source node eligible sourceContext) :
    WireRenaming sourceContext.sigs candidateContext.sigs :=
  fun {_} value =>
    congrArg ConcreteElaboration.WireContext.sigs contextEquality |>.symm ▸
      contextRenaming source node eligible sourceContext value

@[simp] private theorem contextRenamingInto_self
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (equality :
      targetContext source node eligible context =
        targetContext source node eligible context) :
    (contextRenamingInto source node eligible context
        (targetContext source node eligible context) equality :
      WireRenaming context.sigs
        (targetContext source node eligible context).sigs) =
      (fun {_} value =>
        contextRenaming source node eligible context value) := by
  have proofEquality : equality = rfl := Subsingleton.elim _ _
  cases proofEquality
  rfl

private theorem contextRenamingInto_extend
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    (contextRenamingInto source node eligible (context.extend region)
        ((targetContext source node eligible context).extend region)
        (targetContext_extend source node eligible context region).symm :
      WireRenaming (context.extend region).sigs
        ((targetContext source node eligible context).extend region).sigs) =
      (fun {_} value =>
        extendedContextRenaming source node eligible context region value) := by
  apply funext
  intro sig
  apply funext
  intro value
  simp [contextRenamingInto, extendedContextRenaming]

private theorem compileRegion_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      (context : ConcreteElaboration.WireContext source.val)
      (region : source.val.RegionId)
      (_sourceAbove :
        ConcreteElaboration.ContextAbove source.val context region)
      (candidateContext :
        ConcreteElaboration.WireContext
          (dropCandidate source node eligible))
      (contextEquality :
        candidateContext = targetContext source node eligible context)
      (_targetAbove :
        ConcreteElaboration.ContextAbove
          (dropCandidate source node eligible) candidateContext region)
      (targetEnv : Env pre candidateContext.sigs)
      {sourceBody : Region definitions context.sigs}
      {targetBody : Region definitions candidateContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region context =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions
          (dropCandidate source node eligible) fuel region
          candidateContext =
        some targetBody →
      (denoteRegion pre definitionEnv targetEnv targetBody ↔
        denoteRegion pre definitionEnv
          (Env.comp targetEnv
            (contextRenamingInto source node eligible context
              candidateContext contextEquality))
          sourceBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro context region sourceAbove candidateContext contextEquality
        targetAbove targetEnv sourceBody targetBody sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro context region sourceAbove candidateContext contextEquality
        targetAbove targetEnv sourceBody targetBody sourceCompiled
        targetCompiled
      subst candidateContext
      simp only [contextRenamingInto_self]
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceNodesEq :
          ConcreteElaboration.compileNodes? definitions source.val
            (context.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEq] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEq] at sourceCompiled
          cases sourceChildrenEq :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val fuel)
                (context.extend region) (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEq] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEq] at sourceCompiled
              cases targetNodesEq :
                  ConcreteElaboration.compileNodes? definitions
                    (dropCandidate source node eligible)
                    ((targetContext source node eligible context).extend region)
                    ((dropCandidate source node eligible).nodesAt region) with
              | none =>
                  rw [targetNodesEq] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEq] at targetCompiled
                  cases targetChildrenEq :
                      ConcreteElaboration.compileChildrenWith? definitions
                        (dropCandidate source node eligible)
                        (ConcreteElaboration.compileRegion? definitions
                          (dropCandidate source node eligible) fuel)
                        ((targetContext source node eligible context).extend
                          region)
                        ((dropCandidate source node eligible).childrenOf
                          region) with
                  | none =>
                      rw [targetChildrenEq] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEq] at targetCompiled
                      have sourceBodyEquality :
                          ConcreteElaboration.finishRegion source.val context
                              region
                              (.mk (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyEquality :
                          ConcreteElaboration.finishRegion
                              (dropCandidate source node eligible)
                              (targetContext source node eligible context)
                              region
                              (.mk (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      rw [ConcreteElaboration.denote_finishRegion,
                        ConcreteElaboration.denote_finishRegion]
                      have sourceExtendedNodup :
                          (context.extend region).ids.Nodup :=
                        ConcreteElaboration.extend_nodup definitions source.val
                          source.property context region sourceAbove
                      have targetExtendedNodup :
                          ((targetContext source node eligible context).extend
                            region).ids.Nodup :=
                        ConcreteElaboration.extend_nodup definitions
                          (dropCandidate source node eligible)
                          (IdentityNormalizationCore.dropCandidate_wellFormed
                            source node eligible)
                          (targetContext source node eligible context)
                          region targetAbove
                      have targetChildrenEq' :
                          ConcreteElaboration.compileChildrenWith? definitions
                              (dropCandidate source node eligible)
                              (ConcreteElaboration.compileRegion? definitions
                                (dropCandidate source node eligible) fuel)
                              ((targetContext source node eligible context).extend
                                region)
                              ((source.val.childrenOf region).map
                                (fun child => child)) =
                            some targetChildren := by
                        simpa [dropCandidate_childrenOf_eq
                          source node eligible region] using targetChildrenEq
                      constructor
                      · rintro ⟨targetValues, targetCore⟩
                        let targetExtended :=
                          ConcreteElaboration.extendEnvironment
                            (dropCandidate source node eligible)
                            (targetContext source node eligible context) region
                            targetValues targetEnv
                        let sourceExtended :=
                          Env.comp targetExtended
                            (extendedContextRenaming source node eligible
                              context region)
                        let sourceValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor source.val
                            context.ids (source.val.wiresAt region)
                            sourceExtended
                        refine ⟨sourceValues, ?_⟩
                        have sourceEnvironmentEquality :
                            ConcreteElaboration.extendEnvironment source.val
                                context region sourceValues
                                (Env.comp targetEnv
                                  (contextRenaming source node eligible
                                    context)) =
                              sourceExtended :=
                          extendedEnvironment_natural source node eligible
                            context region sourceExtendedNodup pre
                            targetValues targetEnv
                        rw [sourceEnvironmentEquality]
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren) at targetCore
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                        rw [denoteItemSeq_append] at targetCore ⊢
                        constructor
                        · exact
                            (compiledNodes_denotation source node eligible
                              context region sourceExtendedNodup pre
                              definitionEnv targetExtended sourceNodes
                              sourceNodesEq targetNodes targetNodesEq).mp
                              targetCore.1
                        · exact
                            (compileChildren_denotation definitions source.val
                              (dropCandidate source node eligible)
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (dropCandidate source node eligible) fuel)
                              (context.extend region)
                              ((targetContext source node eligible context).extend
                                region)
                              pre definitionEnv sourceExtended targetExtended
                              (source.val.childrenOf region)
                              (fun child => child)
                              sourceChildrenEq targetChildrenEq'
                              (by
                                intro child childMember sourceChild targetChild
                                  sourceChildCompiled targetChildCompiled
                                have sourceChildData :=
                                  ConcreteElaboration.mem_childrenOf source.val
                                    region child childMember
                                have targetChildMember :
                                    child ∈
                                      (dropCandidate source node eligible).childrenOf
                                        region := by
                                  rw [dropCandidate_childrenOf_eq
                                    source node eligible region]
                                  exact childMember
                                have targetChildData :=
                                  ConcreteElaboration.mem_childrenOf
                                    (dropCandidate source node eligible)
                                    region child targetChildMember
                                have sourceChildAbove :=
                                  ConcreteElaboration.extend_above_child
                                    definitions source.val source.property
                                    context region child sourceAbove
                                    sourceChildData
                                have targetChildAbove :=
                                  ConcreteElaboration.extend_above_child
                                    definitions
                                    (dropCandidate source node eligible)
                                    (IdentityNormalizationCore.dropCandidate_wellFormed
                                      source node eligible)
                                    (targetContext source node eligible context)
                                    region child targetAbove targetChildData
                                exact induction (context.extend region) child
                                  sourceChildAbove
                                  ((targetContext source node eligible context).extend
                                    region)
                                  (targetContext_extend source node eligible
                                    context region).symm
                                  targetChildAbove targetExtended
                                  sourceChildCompiled targetChildCompiled)).mp
                              targetCore.2
                      · rintro ⟨sourceValues, sourceCore⟩
                        let sourceOuter :=
                          Env.comp targetEnv
                            (contextRenaming source node eligible context)
                        let sourceExtended :=
                          ConcreteElaboration.extendEnvironment source.val
                            context region sourceValues sourceOuter
                        let targetExtended :=
                          Env.comp sourceExtended
                            (extendedContextSection source node eligible context
                              region)
                        let targetValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            (dropCandidate source node eligible)
                            (targetContext source node eligible context).ids
                            ((dropCandidate source node eligible).wiresAt region)
                            targetExtended
                        refine ⟨targetValues, ?_⟩
                        have targetEnvironmentEquality :
                            ConcreteElaboration.extendEnvironment
                                (dropCandidate source node eligible)
                                (targetContext source node eligible context)
                                region targetValues targetEnv =
                              targetExtended :=
                          reverseExtendedEnvironment_natural source node
                            eligible context region sourceExtendedNodup
                            (targetAbove.1) pre sourceValues sourceOuter targetEnv
                            rfl
                        rw [targetEnvironmentEquality]
                        have sourceRoundtrip :
                            Env.comp targetExtended
                                (extendedContextRenaming source node eligible
                                  context region) =
                              sourceExtended :=
                          extendedEnvironment_roundtrip_source source node
                            eligible context region sourceExtendedNodup pre
                            sourceExtended
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren) at sourceCore
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                        rw [denoteItemSeq_append] at sourceCore ⊢
                        constructor
                        · have nodes :=
                            (compiledNodes_denotation source node eligible
                              context region sourceExtendedNodup pre
                              definitionEnv targetExtended sourceNodes
                              sourceNodesEq targetNodes targetNodesEq).mpr
                              (by simpa [sourceRoundtrip] using sourceCore.1)
                          exact nodes
                        · exact
                            (compileChildren_denotation definitions source.val
                              (dropCandidate source node eligible)
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (dropCandidate source node eligible) fuel)
                              (context.extend region)
                              ((targetContext source node eligible context).extend
                                region)
                              pre definitionEnv sourceExtended targetExtended
                              (source.val.childrenOf region)
                              (fun child => child)
                              sourceChildrenEq targetChildrenEq'
                              (by
                                intro child childMember sourceChild targetChild
                                  sourceChildCompiled targetChildCompiled
                                have sourceChildData :=
                                  ConcreteElaboration.mem_childrenOf source.val
                                    region child childMember
                                have targetChildMember :
                                    child ∈
                                      (dropCandidate source node eligible).childrenOf
                                        region := by
                                  rw [dropCandidate_childrenOf_eq
                                    source node eligible region]
                                  exact childMember
                                have targetChildData :=
                                  ConcreteElaboration.mem_childrenOf
                                    (dropCandidate source node eligible)
                                    region child targetChildMember
                                have sourceChildAbove :=
                                  ConcreteElaboration.extend_above_child
                                    definitions source.val source.property
                                    context region child sourceAbove
                                    sourceChildData
                                have targetChildAbove :=
                                  ConcreteElaboration.extend_above_child
                                    definitions
                                    (dropCandidate source node eligible)
                                    (IdentityNormalizationCore.dropCandidate_wellFormed
                                      source node eligible)
                                    (targetContext source node eligible context)
                                    region child targetAbove targetChildData
                                have childIff :=
                                  induction (context.extend region) child
                                    sourceChildAbove
                                    ((targetContext source node eligible
                                      context).extend region)
                                    (targetContext_extend source node eligible
                                      context region).symm
                                    targetChildAbove targetExtended
                                    sourceChildCompiled targetChildCompiled
                                rw [contextRenamingInto_extend] at childIff
                                rw [sourceRoundtrip] at childIff
                                exact childIff)).mpr
                              (by simpa [sourceRoundtrip] using sourceCore.2)

private theorem dropCandidate_sound
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv
        (⟨dropCandidate source node eligible,
          IdentityNormalizationCore.dropCandidate_wellFormed
            source node eligible⟩ : CheckedDiagram definitions) ↔
      denoteChecked pre definitionEnv source := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked]
  have sourceCompiled :=
    elaborateWith_compiles definitions source.val source.property
  have targetCompiled :=
    elaborateWith_compiles definitions
      (dropCandidate source node eligible)
      (IdentityNormalizationCore.dropCandidate_wellFormed
        source node eligible)
  unfold ConcreteElaboration.compileRoot? at sourceCompiled targetCompiled
  have sourceEmptyAbove :
      ConcreteElaboration.ContextAbove source.val
        (ConcreteElaboration.WireContext.empty source.val)
        source.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  have targetEmptyAbove :
      ConcreteElaboration.ContextAbove
        (dropCandidate source node eligible)
        (ConcreteElaboration.WireContext.empty
          (dropCandidate source node eligible))
        source.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty], by
      intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member⟩
  have emptyEquality :
      ConcreteElaboration.WireContext.empty
          (dropCandidate source node eligible) =
        targetContext source node eligible
          (ConcreteElaboration.WireContext.empty source.val) :=
    rfl
  have result :=
    compileRegion_denotation source node eligible pre definitionEnv
      (source.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty source.val)
      source.val.root sourceEmptyAbove
      (ConcreteElaboration.WireContext.empty
        (dropCandidate source node eligible))
      emptyEquality targetEmptyAbove Env.empty
      sourceCompiled targetCompiled
  have pulledEmpty :
      Env.comp (Env.empty : Env pre [])
          (contextRenamingInto source node eligible
            (ConcreteElaboration.WireContext.empty source.val)
            (ConcreteElaboration.WireContext.empty
              (dropCandidate source node eligible))
            emptyEquality) =
        Env.empty := by
    funext sig value
    nomatch value
  have result' :
      denoteRegion pre definitionEnv Env.empty
          (elaborateWith definitions (dropCandidate source node eligible)
            (IdentityNormalizationCore.dropCandidate_wellFormed
              source node eligible)) ↔
        denoteRegion pre definitionEnv Env.empty
          (elaborateWith definitions source.val source.property) := by
    constructor
    · intro targetDenotes
      exact Eq.mp
        (congrArg
          (fun env =>
            denoteRegion pre definitionEnv env
              (elaborateWith definitions source.val source.property))
          pulledEmpty)
        (result.mp targetDenotes)
    · intro sourceDenotes
      apply result.mpr
      exact Eq.mpr
        (congrArg
          (fun env =>
            denoteRegion pre definitionEnv env
              (elaborateWith definitions source.val source.property))
          pulledEmpty)
        sourceDenotes
  simpa [elaborate] using result'

theorem dropDegenerate_sound
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (target : IdentityRewrite source)
    (result : dropDegenerate source node = some target) :
    denoteChecked pre definitionEnv target.target ↔
      denoteChecked pre definitionEnv source := by
  unfold dropDegenerate at result
  cases eligibilityEq : dropEligibility? source node with
  | none =>
      simp [eligibilityEq] at result
  | some eligible =>
      rw [eligibilityEq] at result
      simp only [Option.map] at result
      have targetEquation := Option.some.inj result
      clear result
      subst target
      exact dropCandidate_sound source node eligible pre definitionEnv

end IdentityNormalizationDropSemantics

theorem dropDegenerate_sound
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (target : IdentityRewrite source)
    (result : dropDegenerate source node = some target) :
    denoteChecked pre definitionEnv target.target ↔
      denoteChecked pre definitionEnv source :=
  IdentityNormalizationDropSemantics.dropDegenerate_sound
    source node pre definitionEnv target result

end ConcreteDiagram

end VisualProof
