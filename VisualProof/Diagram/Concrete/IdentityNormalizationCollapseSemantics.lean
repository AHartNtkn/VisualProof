import VisualProof.Diagram.Concrete.IdentityNormalizationTransport
import VisualProof.Diagram.Concrete.IdentityNormalizationCollapseWellFormed
import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof

universe u

namespace ConcreteDiagram

open IdentityNormalizationCore

namespace IdentityNormalizationCollapseSemantics

private abbrev Target
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :=
  collapseCandidate source node eligible

def representative
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    source.val.WireId :=
  if wire ∈ source.val.identityIncidentWires node then
    eligible.survivor
  else
    wire

private theorem representative_mem_retained
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    representative source node eligible wire ∈
      retainedWires source.val (eligible.second :: eligible.rest) := by
  have incidentNodup :=
    collapseIncidentWires_nodup source node eligible.identity.region
  rw [eligible.incident_eq] at incidentNodup
  have survivorNotAbsorbed :
      eligible.survivor ∉ eligible.second :: eligible.rest := by
    simpa using (List.nodup_cons.mp incidentNodup).1
  have absorbedSubset :
      ∀ candidate,
        candidate ∈ eligible.second :: eligible.rest →
        candidate ∈ source.val.identityIncidentWires node := by
    intro candidate member
    rw [← mem_collapseIncidentWires source node
      eligible.identity.region]
    rw [eligible.incident_eq]
    exact List.mem_cons_of_mem eligible.survivor member
  unfold representative retainedWires
  rw [List.mem_filter]
  constructor
  · exact Data.Finite.mem_allFin _
  · split
    · simpa using survivorNotAbsorbed
    · rename_i notIncident
      simp only [decide_eq_true_eq]
      intro absorbed
      exact notIncident (absorbedSubset wire absorbed)

def targetWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    (Target source node eligible).WireId :=
  (Data.Finite.indexOf?
    (retainedWires source.val (eligible.second :: eligible.rest))
    (representative source node eligible wire)).get
      (Data.Finite.indexOf?_isSome_iff.mpr
        (representative_mem_retained source node eligible wire))

def sourceWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (Target source node eligible).WireId) :
    source.val.WireId :=
  (retainedWires source.val (eligible.second :: eligible.rest)).get wire

@[simp] private theorem retained_get_targetWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    (retainedWires source.val
      (eligible.second :: eligible.rest)).get
        (targetWire source node eligible wire) =
      representative source node eligible wire := by
  unfold targetWire
  exact Data.Finite.indexOf?_sound
    (Option.some_get
      (Data.Finite.indexOf?_isSome_iff.mpr
        (representative_mem_retained source node eligible wire))).symm

@[simp] private theorem targetWire_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    ((Target source node eligible).wires
      (targetWire source node eligible wire)).sig =
        (source.val.wires wire).sig :=
  by
    change
      (source.val.wires
        ((retainedWires source.val
          (eligible.second :: eligible.rest)).get
            (targetWire source node eligible wire))).sig =
        (source.val.wires wire).sig
    rw [retained_get_targetWire]
    unfold representative
    split
    · rename_i incident
      have survivorIncident :
          eligible.survivor ∈ source.val.identityIncidentWires node := by
        rw [← mem_collapseIncidentWires source node
          eligible.identity.region]
        rw [eligible.incident_eq]
        simp
      exact
        (identityIncidentWire_signature definitions source.val source.property
          eligible.identity.node_eq eligible.survivor survivorIncident).trans
        (identityIncidentWire_signature definitions source.val source.property
          eligible.identity.node_eq wire incident).symm
    · rfl

private theorem sourceWire_mem_retained
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (Target source node eligible).WireId) :
    sourceWire source node eligible wire ∈
      retainedWires source.val (eligible.second :: eligible.rest) :=
  List.get_mem _ _

theorem targetWire_sourceWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : (Target source node eligible).WireId) :
    targetWire source node eligible
        (sourceWire source node eligible wire) = wire := by
  have retainedNodup :
      (retainedWires source.val
        (eligible.second :: eligible.rest)).Nodup :=
    (Data.Finite.allFin_nodup source.val.wireCount).filter _
  have representativeSelf :
      representative source node eligible
          (sourceWire source node eligible wire) =
        sourceWire source node eligible wire := by
    unfold representative
    split
    · rename_i incident
      rw [← mem_collapseIncidentWires source node
        eligible.identity.region] at incident
      rw [eligible.incident_eq] at incident
      rcases List.mem_cons.mp incident with survivor | absorbed
      · exact survivor.symm
      · have retained := (List.mem_filter.mp
          (sourceWire_mem_retained source node eligible wire)).2
        simp only [decide_eq_true_eq] at retained
        exact False.elim (retained absorbed)
    · rfl
  have indexed :
      Data.Finite.indexOf?
          (retainedWires source.val
            (eligible.second :: eligible.rest))
          (representative source node eligible
            (sourceWire source node eligible wire)) =
        some (targetWire source node eligible
          (sourceWire source node eligible wire)) := by
    unfold targetWire
    exact (Option.some_get _).symm
  have stored :
      (retainedWires source.val
        (eligible.second :: eligible.rest)).get wire =
        representative source node eligible
          (sourceWire source node eligible wire) := by
    change
      sourceWire source node eligible wire =
        representative source node eligible
          (sourceWire source node eligible wire)
    exact representativeSelf.symm
  exact (Data.Finite.indexOf?_unique_of_nodup
    retainedNodup indexed stored).symm

@[simp] private theorem sourceWire_targetWire
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    sourceWire source node eligible
        (targetWire source node eligible wire) =
      representative source node eligible wire := by
  unfold sourceWire
  exact retained_get_targetWire source node eligible wire

private theorem survivor_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    eligible.survivor ∈ source.val.identityIncidentWires node := by
  rw [← mem_collapseIncidentWires source node
    eligible.identity.region]
  rw [eligible.incident_eq]
  simp

private theorem incident_eq_survivor_or_absorbed
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    wire ∈ source.val.identityIncidentWires node ↔
      wire = eligible.survivor ∨
        wire ∈ eligible.second :: eligible.rest := by
  rw [← mem_collapseIncidentWires source node
    eligible.identity.region]
  rw [eligible.incident_eq]
  simp

private theorem targetWire_scope_representative
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    ((Target source node eligible).wires
      (targetWire source node eligible wire)).scope =
        (source.val.wires
          (representative source node eligible wire)).scope := by
  change
    (source.val.wires
      ((retainedWires source.val
        (eligible.second :: eligible.rest)).get
          (targetWire source node eligible wire))).scope =
      (source.val.wires
        (representative source node eligible wire)).scope
  rw [retained_get_targetWire]

theorem targetWire_eq_survivor_of_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId)
    (incident : wire ∈ source.val.identityIncidentWires node) :
    targetWire source node eligible wire =
      targetWire source node eligible eligible.survivor := by
  apply Fin.ext
  unfold targetWire representative
  simp only [if_pos incident, if_pos (survivor_incident source node eligible)]

def targetNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ node) :
    (Target source node eligible).NodeId :=
  (Data.Finite.indexOf?
    (retainedNodes source.val [node]) sourceNode).get
      (Data.Finite.indexOf?_isSome_iff.mpr (by
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))

private def sourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : (Target source node eligible).NodeId) :
    source.val.NodeId :=
  (retainedNodes source.val [node]).get target

private theorem sourceNode_ne
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : (Target source node eligible).NodeId) :
    sourceNode source node eligible target ≠ node := by
  have member :=
    List.get_mem (retainedNodes source.val [node]) target
  simpa [sourceNode, retainedNodes] using
    (List.mem_filter.mp member).2

@[simp] theorem retained_get_targetNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceNode : source.val.NodeId)
    (survives : sourceNode ≠ node) :
    (retainedNodes source.val [node]).get
        (targetNode source node eligible sourceNode survives) =
      sourceNode := by
  unfold targetNode
  exact Data.Finite.indexOf?_sound
    (Option.some_get
      (Data.Finite.indexOf?_isSome_iff.mpr (by
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))).symm

@[simp] private theorem targetNode_sourceNode
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : (Target source node eligible).NodeId) :
    targetNode source node eligible (sourceNode source node eligible target)
        (sourceNode_ne source node eligible target) =
      target := by
  have nodup :
      (retainedNodes source.val [node]).Nodup :=
    (Data.Finite.allFin_nodup source.val.nodeCount).filter _
  have indexed :
      Data.Finite.indexOf? (retainedNodes source.val [node])
          (sourceNode source node eligible target) =
        some
          (targetNode source node eligible
            (sourceNode source node eligible target)
            (sourceNode_ne source node eligible target)) := by
    unfold targetNode
    exact (Option.some_get _).symm
  have stored :
      (retainedNodes source.val [node]).get target =
        sourceNode source node eligible target := rfl
  exact (Data.Finite.indexOf?_unique_of_nodup
    nodup indexed stored).symm

@[simp] private theorem target_node
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (target : (Target source node eligible).NodeId) :
    (Target source node eligible).nodes target =
      source.val.nodes (sourceNode source node eligible target) := by
  rfl

def targetEndpoint
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (endpoint : CEndpoint source.val.nodeCount)
    (survives : endpoint.node ≠ node) :
    CEndpoint (Target source node eligible).nodeCount :=
  ⟨targetNode source node eligible endpoint.node survives,
    endpoint.port⟩

@[simp] private theorem reindexEndpoint?_target
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (endpoint : CEndpoint source.val.nodeCount)
    (survives : endpoint.node ≠ node) :
  reindexEndpoint? (retainedNodes source.val [node]) endpoint =
      some (targetEndpoint source node eligible endpoint survives) := by
  cases found :
      Data.Finite.indexOf? (retainedNodes source.val [node])
        endpoint.node with
  | none =>
      have member :
          endpoint.node ∈ retainedNodes source.val [node] := by
        apply List.mem_filter.mpr
        constructor
        · exact Data.Finite.mem_allFin _
        · simp [survives]
      have present := Data.Finite.indexOf?_isSome_iff.mpr member
      rw [found] at present
      contradiction
  | some index =>
      simp [reindexEndpoint?, targetEndpoint, targetNode, found]
      rfl

theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (endpoint : CEndpoint source.val.nodeCount)
    (survives : endpoint.node ≠ node)
    (wire : source.val.WireId)
    (incident :
      endpoint ∈ (source.val.wires wire).endpoints) :
    targetEndpoint source node eligible endpoint survives ∈
      ((Target source node eligible).wires
        (targetWire source node eligible wire)).endpoints := by
  change
    targetEndpoint source node eligible endpoint survives ∈
      reindexEndpoints (retainedNodes source.val [node])
        (if (retainedWires source.val
            (eligible.second :: eligible.rest)).get
              (targetWire source node eligible wire) =
              eligible.survivor then
          (source.val.identityIncidentWires node).flatMap fun original =>
            eraseNodeEndpoints node
              (source.val.wires original).endpoints
        else
          eraseNodeEndpoints node
            (source.val.wires
              ((retainedWires source.val
                (eligible.second :: eligible.rest)).get
                  (targetWire source node eligible wire))).endpoints)
  rw [retained_get_targetWire]
  apply List.mem_filterMap.mpr
  refine ⟨endpoint, ?_, reindexEndpoint?_target
    source node eligible endpoint survives⟩
  unfold representative
  split
  · rename_i wireIncident
    rw [if_pos rfl]
    apply List.mem_flatMap.mpr
    exact ⟨wire, wireIncident, by
      simp [eraseNodeEndpoints, incident, survives]⟩
  · rename_i wireNotIncident
    rw [if_neg]
    · simp [eraseNodeEndpoints, incident, survives]
    · intro survivor
      subst wire
      apply wireNotIncident
      rw [← mem_collapseIncidentWires source node
        eligible.identity.region]
      rw [eligible.incident_eq]
      simp

private theorem targetWire_mem_wiresAt_of_representative_scope
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId)
    (wire : source.val.WireId)
    (scope :
      (source.val.wires
        (representative source node eligible wire)).scope = region) :
    targetWire source node eligible wire ∈
      (Target source node eligible).wiresAt region := by
  unfold ConcreteDiagram.wiresAt
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · rw [targetWire_scope_representative, scope]
    simp

private theorem sourceWire_mem_wiresAt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId)
    (wire : (Target source node eligible).WireId)
    (member : wire ∈ (Target source node eligible).wiresAt region) :
    sourceWire source node eligible wire ∈
      source.val.wiresAt region := by
  unfold ConcreteDiagram.wiresAt at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have targetScope := eq_of_beq (List.mem_filter.mp member).2
    change
      (source.val.wires
        ((retainedWires source.val
          (eligible.second :: eligible.rest)).get wire)).scope =
        region at targetScope
    change
      ((source.val.wires
        (sourceWire source node eligible wire)).scope == region) = true
    unfold sourceWire
    rw [targetScope]
    simp

private structure ContextsRelated
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)) :
    Prop where
  forward :
    ∀ wire, wire ∈ sourceContext.ids →
      targetWire source node eligible wire ∈ targetContext.ids
  backward :
    ∀ wire, wire ∈ targetContext.ids →
      sourceWire source node eligible wire ∈ sourceContext.ids

private theorem empty_contexts_related
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    ContextsRelated source node eligible
      (ConcreteElaboration.WireContext.empty source.val)
      (ConcreteElaboration.WireContext.empty
        (Target source node eligible)) := by
  constructor
  · intro wire member
    simp [ConcreteElaboration.WireContext.empty] at member
  · intro wire member
    simp [ConcreteElaboration.WireContext.empty] at member

private theorem extend_contexts_related
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (survivorVisible :
      region = eligible.identity.region →
      (source.val.wires eligible.survivor).scope ≠ region →
        eligible.survivor ∈ sourceContext.ids) :
    ContextsRelated source node eligible
      (sourceContext.extend region) (targetContext.extend region) := by
  constructor
  · intro wire member
    simp only [ConcreteElaboration.WireContext.extend,
      List.mem_append] at member ⊢
    rcases member with localMember | outer
    · have localScope :
          (source.val.wires wire).scope = region := by
        unfold ConcreteDiagram.wiresAt at localMember
        exact eq_of_beq (List.mem_filter.mp localMember).2
      by_cases incident : wire ∈ source.val.identityIncidentWires node
      · rcases
          (incident_eq_survivor_or_absorbed source node eligible wire).mp
            incident with wireSurvivor | absorbed
        · subst wire
          exact Or.inl
            (targetWire_mem_wiresAt_of_representative_scope source node
              eligible region eligible.survivor (by
                simp [representative,
                  survivor_incident source node eligible, localScope]))
        · have absorbedScope :=
            eligible.absorbedCoScoped wire absorbed
          have regionIdentity : region = eligible.identity.region :=
            localScope.symm.trans absorbedScope
          by_cases survivorLocal :
              (source.val.wires eligible.survivor).scope = region
          · exact Or.inl
              (targetWire_mem_wiresAt_of_representative_scope source node
                eligible region wire (by
                  simp [representative, incident, survivorLocal]))
          · exact Or.inr (by
              rw [targetWire_eq_survivor_of_incident source node eligible
                wire incident]
              exact related.forward eligible.survivor
                (survivorVisible regionIdentity survivorLocal))
      · exact Or.inl
          (targetWire_mem_wiresAt_of_representative_scope source node
            eligible region wire (by
              simp [representative, incident, localScope]))
    · exact Or.inr (related.forward wire outer)
  · intro wire member
    simp only [ConcreteElaboration.WireContext.extend,
      List.mem_append] at member ⊢
    rcases member with localMember | outer
    · exact Or.inl
        (sourceWire_mem_wiresAt source node eligible region wire localMember)
    · exact Or.inr (related.backward wire outer)

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

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there value =>
          exact List.mem_cons_of_mem head (induction value)

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

private def contextRenaming
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  fun {sig} value =>
    let sourceWire :=
      ConcreteElaboration.WireContext.origin
        source.val sourceContext.ids value
    let targetVar :=
      varForMember (Target source node eligible)
        (targetWire source node eligible sourceWire)
        targetContext.ids
        (related.forward sourceWire
          (origin_mem source.val sourceContext.ids value))
    let signature :
        ((Target source node eligible).wires
          (targetWire source node eligible sourceWire)).sig = sig :=
      (targetWire_signature source node eligible sourceWire).trans
        (ConcreteElaboration.WireContext.origin_signature
          source.val sourceContext.ids value)
    castVar signature targetVar

private theorem contextRenaming_origin
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    ConcreteElaboration.WireContext.origin
        (Target source node eligible) targetContext.ids
        (contextRenaming source node eligible related value) =
      targetWire source node eligible
        (ConcreteElaboration.WireContext.origin
          source.val sourceContext.ids value) := by
  unfold contextRenaming
  dsimp only
  exact
    (origin_castVar
      (Target source node eligible) targetContext _ _).trans
      (origin_varForMember _ _ _ _)

private def contextSection
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext) :
    WireRenaming targetContext.sigs sourceContext.sigs :=
  fun {sig} value =>
    let targetOrigin :=
      ConcreteElaboration.WireContext.origin
        (Target source node eligible) targetContext.ids value
    let original := sourceWire source node eligible targetOrigin
    let sourceVar :=
      varForMember source.val original sourceContext.ids
        (related.backward targetOrigin
          (origin_mem (Target source node eligible)
            targetContext.ids value))
    let signature :
        (source.val.wires original).sig = sig :=
      (targetWire_signature source node eligible original).symm.trans
        ((congrArg
          (fun wire => ((Target source node eligible).wires wire).sig)
          (targetWire_sourceWire source node eligible targetOrigin)).trans
        (ConcreteElaboration.WireContext.origin_signature
          (Target source node eligible) targetContext.ids value))
    castVar signature sourceVar

private theorem contextSection_origin
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    ConcreteElaboration.WireContext.origin source.val sourceContext.ids
        (contextSection source node eligible related value) =
      sourceWire source node eligible
        (ConcreteElaboration.WireContext.origin
          (Target source node eligible) targetContext.ids value) := by
  unfold contextSection
  dsimp only
  exact
    (origin_castVar source.val sourceContext _ _).trans
      (origin_varForMember _ _ _ _)

private theorem compile_retained_singleton
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (originalNode : source.val.NodeId)
    (survives : originalNode ≠ node)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceContext [originalNode] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source node eligible) targetContext
          [targetNode source node eligible originalNode survives] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (contextRenaming source node eligible related) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    (collapseCandidate_wellFormed source node eligible)
    targetNodup
    (contextRenaming source node eligible related)
    (targetWire source node eligible)
    (targetWire_signature source node eligible)
    (contextRenaming_origin source node eligible related)
    id originalNode
    (targetNode source node eligible originalNode survives)
  · rw [target_node]
    unfold sourceNode
    rw [retained_get_targetNode source node eligible originalNode survives]
    cases source.val.nodes originalNode <;> rfl
  · intro port wire incident
    exact targetEndpoint_incident source node eligible
      ⟨originalNode, port⟩ survives wire incident
  · exact compiled

private theorem option_bind₂_eq_some
    {first : Option α} {second : Option β}
    {combine : α → β → γ} {result : γ}
    (equation :
      (do
        let left ← first
        let right ← second
        pure (combine left right)) = some result) :
    ∃ left right,
      first = some left ∧
      second = some right ∧
      combine left right = result := by
  cases first with
  | none => simp at equation
  | some left =>
      cases second with
      | none => simp at equation
      | some right =>
          exact ⟨left, right, rfl, rfl,
            Option.some.inj equation⟩

private theorem compileNodes_cons_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (tail : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: tail) =
        some items) :
    ∃ head rest,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some (.cons head .nil) ∧
      ConcreteElaboration.compileNodes? definitions diagram context tail =
          some rest ∧
      items = .cons head rest := by
  simp only [ConcreteElaboration.compileNodes?] at compiled
  obtain ⟨head, rest, headEquation, restEquation, itemsEquation⟩ :=
    option_bind₂_eq_some compiled
  subst items
  refine ⟨head, rest, ?_, restEquation, rfl⟩
  simp only [ConcreteElaboration.compileNodes?]
  rw [headEquation]
  rfl

private theorem denote_compileNodes_iff_singletons
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ node, node ∈ nodes →
        ∃ item,
          ConcreteElaboration.compileNodes? definitions diagram context
              [node] =
            some (.cons item .nil) ∧
          denoteItem pre definitionEnv env item := by
  induction nodes generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?] at compiled
      have itemsEmpty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled,
          itemsEquation⟩ :=
        compileNodes_cons_components definitions diagram context head tail
          items compiled
      subst items
      rw [denoteItemSeq_cons,
        induction restItems restCompiled]
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ candidate member
        rcases List.mem_cons.mp member with equality | tailMember
        · subst candidate
          exact ⟨headItem, headCompiled, headDenotes⟩
        · exact tailDenotes candidate tailMember
      · intro each
        obtain ⟨actualHead, actualCompiled, headDenotes⟩ :=
          each head (by simp)
        have actualEquality :
            actualHead = headItem := by
          exact ItemSeq.cons.inj
            (Option.some.inj (actualCompiled.symm.trans headCompiled)) |>.1
        subst actualHead
        exact ⟨headDenotes, fun candidate tailMember =>
          each candidate (List.mem_cons_of_mem head tailMember)⟩

private theorem compileNodes_singleton_of_member
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items)
    (node : diagram.NodeId)
    (member : node ∈ nodes) :
    ∃ item,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some (.cons item .nil) := by
  induction nodes generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled, _⟩ :=
        compileNodes_cons_components definitions diagram context head tail
          items compiled
      rcases List.mem_cons.mp member with equality | tailMember
      · subst node
        exact ⟨headItem, headCompiled⟩
      · exact induction restItems restCompiled tailMember

private theorem identity_mem_nodesAt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    node ∈ source.val.nodesAt eligible.identity.region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  rw [eligible.identity.node_eq]
  simp [CNode.region]

private theorem survivor_mem_outer_context
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (regionIdentity : region = eligible.identity.region)
    (survivorNotLocal :
      (source.val.wires eligible.survivor).scope ≠ region)
    (sourceNodes : ItemSeq definitions (sourceContext.extend region).sigs)
    (sourceNodesEquation :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceContext.extend region) (source.val.nodesAt region) =
        some sourceNodes) :
    eligible.survivor ∈ sourceContext.ids := by
  have nodeMember : node ∈ source.val.nodesAt region := by
    rw [regionIdentity]
    exact identity_mem_nodesAt source node eligible
  obtain ⟨item, singletonCompiled⟩ :=
    compileNodes_singleton_of_member definitions source.val
      (sourceContext.extend region) (source.val.nodesAt region)
      sourceNodes sourceNodesEquation node nodeMember
  obtain ⟨ports, _two, _itemsEquation, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins source.val
      source.property (sourceContext.extend region) node
      eligible.identity.node_eq singletonCompiled
  obtain ⟨survivorVar, _survivorMember, survivorOrigin⟩ :=
    (origins eligible.survivor).mp
      (survivor_incident source node eligible)
  have extendedMember :
      eligible.survivor ∈ (sourceContext.extend region).ids := by
    rw [← survivorOrigin]
    exact origin_mem source.val (sourceContext.extend region).ids survivorVar
  simp only [ConcreteElaboration.WireContext.extend,
    List.mem_append] at extendedMember
  rcases extendedMember with localMember | outerMember
  · have localScope :
        (source.val.wires eligible.survivor).scope = region := by
      unfold ConcreteDiagram.wiresAt at localMember
      exact eq_of_beq (List.mem_filter.mp localMember).2
    exact False.elim (survivorNotLocal localScope)
  · exact outerMember

private theorem origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig}
    {left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig}
    (same :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              have rightMember :=
                origin_mem diagram tail right
              have headNotTail := (List.nodup_cons.mp nodup).1
              have sameOrigin :
                  head =
                    ConcreteElaboration.WireContext.origin diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              exact False.elim
                (headNotTail (sameOrigin ▸ rightMember))
      | there left =>
          cases right with
          | here =>
              have leftMember :=
                origin_mem diagram tail left
              have headNotTail := (List.nodup_cons.mp nodup).1
              have sameOrigin :
                  ConcreteElaboration.WireContext.origin diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              exact False.elim
                (headNotTail (sameOrigin ▸ leftMember))
          | there right =>
              exact congrArg Var.there
                (induction (List.nodup_cons.mp nodup).2
                  (by simpa [ConcreteElaboration.WireContext.origin]
                    using same))

private theorem contextRenaming_eq_of_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sig : Sig}
    (left right : Var sourceContext.sigs sig)
    (leftIncident :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          left ∈
        source.val.identityIncidentWires node)
    (rightIncident :
      ConcreteElaboration.WireContext.origin source.val sourceContext.ids
          right ∈
        source.val.identityIncidentWires node) :
    contextRenaming source node eligible related left =
      contextRenaming source node eligible related right := by
  apply origin_injective (Target source node eligible)
    targetContext.ids targetNodup
  rw [contextRenaming_origin, contextRenaming_origin,
    targetWire_eq_survivor_of_incident source node eligible _ leftIncident,
    targetWire_eq_survivor_of_incident source node eligible _ rightIncident]

private theorem identity_denotes_under_pullback
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (items : ItemSeq definitions sourceContext.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          [node] =
        some items) :
    denoteItemSeq pre definitionEnv
      (Env.comp targetEnv
        (contextRenaming source node eligible related)) items := by
  obtain ⟨ports, two, itemsEquation, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      source.val source.property sourceContext node
      eligible.identity.node_eq compiled
  subst items
  simp only [denoteItemSeq_cons, denoteItem_identity,
    denoteItemSeq_nil, and_true]
  intro leftValue leftMember rightValue rightMember
  rcases List.mem_map.mp leftMember with
    ⟨leftVar, leftVarMember, leftEquation⟩
  rcases List.mem_map.mp rightMember with
    ⟨rightVar, rightVarMember, rightEquation⟩
  subst leftValue
  subst rightValue
  exact congrArg (targetEnv eligible.identity.signature)
    (contextRenaming_eq_of_incident source node eligible related targetNodup
      leftVar rightVar
      ((origins
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids leftVar)).mpr
        ⟨leftVar, leftVarMember, rfl⟩)
      ((origins
        (ConcreteElaboration.WireContext.origin source.val
          sourceContext.ids rightVar)).mpr
        ⟨rightVar, rightVarMember, rfl⟩))

private theorem source_environment_one_point
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (sourceNodup : sourceContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceEnv : Env pre sourceContext.sigs)
    (items : ItemSeq definitions sourceContext.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          [node] =
        some items)
    (denotes : denoteItemSeq pre definitionEnv sourceEnv items) :
    Env.comp
        (Env.comp sourceEnv
          (contextSection source node eligible related))
        (contextRenaming source node eligible related) =
      sourceEnv := by
  obtain ⟨ports, two, itemsEquation, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      source.val source.property sourceContext node
      eligible.identity.node_eq compiled
  have allEqual :
      AllEqual
        (ports.map (sourceEnv eligible.identity.signature)) := by
    rw [itemsEquation] at denotes
    exact denotes.1
  funext sig value
  let wire :=
    ConcreteElaboration.WireContext.origin
      source.val sourceContext.ids value
  by_cases incident : wire ∈ source.val.identityIncidentWires node
  · have wireSignature :=
      ConcreteElaboration.WireContext.origin_signature
        source.val sourceContext.ids value
    have identitySignature :=
      identityIncidentWire_signature definitions source.val source.property
        eligible.identity.node_eq wire incident
    have sigEquation : sig = eligible.identity.signature :=
      wireSignature.symm.trans identitySignature
    subst sig
    obtain ⟨wireVar, wireVarMember, wireVarOrigin⟩ :=
      (origins wire).mp incident
    have survivorIncident :
        eligible.survivor ∈ source.val.identityIncidentWires node :=
      survivor_incident source node eligible
    obtain ⟨survivorVar, survivorVarMember, survivorVarOrigin⟩ :=
      (origins eligible.survivor).mp survivorIncident
    have valueEqWireVar : value = wireVar :=
      origin_injective source.val sourceContext.ids sourceNodup
        (by simpa [wire] using wireVarOrigin.symm)
    have sectionOrigin :
        ConcreteElaboration.WireContext.origin
            source.val sourceContext.ids
            (contextSection source node eligible related
              (contextRenaming source node eligible related value)) =
          eligible.survivor := by
      rw [contextSection_origin, contextRenaming_origin,
        sourceWire_targetWire]
      change representative source node eligible wire = eligible.survivor
      simp [representative, incident]
    have sectionEqSurvivor :
        contextSection source node eligible related
            (contextRenaming source node eligible related value) =
          survivorVar :=
      origin_injective source.val sourceContext.ids sourceNodup
        (sectionOrigin.trans survivorVarOrigin.symm)
    change
      sourceEnv eligible.identity.signature
          (contextSection source node eligible related
            (contextRenaming source node eligible related value)) =
        sourceEnv eligible.identity.signature value
    rw [sectionEqSurvivor, valueEqWireVar]
    exact allEqual
      (sourceEnv eligible.identity.signature survivorVar)
      (List.mem_map.mpr ⟨survivorVar, survivorVarMember, rfl⟩)
      (sourceEnv eligible.identity.signature wireVar)
      (List.mem_map.mpr ⟨wireVar, wireVarMember, rfl⟩)
  · have sectionOrigin :
        ConcreteElaboration.WireContext.origin source.val sourceContext.ids
            (contextSection source node eligible related
              (contextRenaming source node eligible related value)) =
          wire := by
      rw [contextSection_origin, contextRenaming_origin,
        sourceWire_targetWire]
      simp [representative, incident, wire]
    have sameVariable :
        contextSection source node eligible related
            (contextRenaming source node eligible related value) =
          value :=
      origin_injective source.val sourceContext.ids sourceNodup
        (by simpa [wire] using sectionOrigin)
    change
      sourceEnv sig
          (contextSection source node eligible related
            (contextRenaming source node eligible related value)) =
        sourceEnv sig value
    rw [sameVariable]

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
  | cons head tail induction => exact induction

private theorem extendEnvironment_from
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (pre : PreModel)
    (env : Env pre (context.extend region).sigs)
    (outerEnv : Env pre context.sigs)
    (agrees : ∀ {sig} (value : Var context.sigs sig),
      env sig
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value) =
        outerEnv sig value) :
    ConcreteElaboration.extendEnvironment diagram context region
        (ConcreteElaboration.valuesFromEnvironmentFor diagram context.ids
          (diagram.wiresAt region) env)
        outerEnv =
      env := by
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  exact agrees value

private theorem contextRenaming_appendRight
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated source node eligible
        (sourceContext.extend region) (targetContext.extend region))
    (targetExtendedNodup : (targetContext.extend region).ids.Nodup)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    contextRenaming source node eligible
        extendedRelated
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region) value) =
      ConcreteElaboration.appendRightVar
        (Target source node eligible)
        ((Target source node eligible).wiresAt region)
        (contextRenaming source node eligible related value) := by
  apply origin_injective (Target source node eligible)
    (targetContext.extend region).ids targetExtendedNodup
  unfold ConcreteElaboration.WireContext.extend
  rw [contextRenaming_origin, origin_appendRightVar]
  change
    targetWire source node eligible
        (ConcreteElaboration.WireContext.origin
          source.val sourceContext.ids value) =
      ConcreteElaboration.WireContext.origin
        (Target source node eligible)
        (((Target source node eligible).wiresAt region) ++
          targetContext.ids)
        (ConcreteElaboration.appendRightVar
          (Target source node eligible)
          ((Target source node eligible).wiresAt region)
          (contextRenaming source node eligible related value))
  rw [origin_appendRightVar, contextRenaming_origin]

private theorem contextSection_appendRight
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated source node eligible
        (sourceContext.extend region) (targetContext.extend region))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextSection source node eligible
        extendedRelated
        (ConcreteElaboration.appendRightVar
          (Target source node eligible)
          ((Target source node eligible).wiresAt region) value) =
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region)
        (contextSection source node eligible related value) := by
  apply origin_injective source.val
    (sourceContext.extend region).ids sourceExtendedNodup
  unfold ConcreteElaboration.WireContext.extend
  rw [contextSection_origin, origin_appendRightVar]
  change
    sourceWire source node eligible
        (ConcreteElaboration.WireContext.origin
          (Target source node eligible) targetContext.ids value) =
      ConcreteElaboration.WireContext.origin source.val
        ((source.val.wiresAt region) ++ sourceContext.ids)
        (ConcreteElaboration.appendRightVar source.val
          (source.val.wiresAt region)
          (contextSection source node eligible related value))
  rw [origin_appendRightVar, contextSection_origin]

private theorem contextRenaming_section
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sig : Sig} (value : Var targetContext.sigs sig) :
    contextRenaming source node eligible related
        (contextSection source node eligible related value) =
      value := by
  apply origin_injective (Target source node eligible)
    targetContext.ids targetNodup
  rw [contextRenaming_origin, contextSection_origin,
    targetWire_sourceWire]

private theorem target_extended_realizes_source
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated source node eligible
        (sourceContext.extend region) (targetContext.extend region))
    (targetExtendedNodup : (targetContext.extend region).ids.Nodup)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv
          (contextRenaming source node eligible related))
    (targetValues : ConcreteElaboration.WireValues pre
      (((Target source node eligible).wiresAt region).map fun wire =>
        ((Target source node eligible).wires wire).sig)) :
    let targetExtended :=
      ConcreteElaboration.extendEnvironment
        (Target source node eligible) targetContext region
        targetValues targetEnv
    let sourceExtended :=
      Env.comp targetExtended
        (contextRenaming source node eligible
          extendedRelated)
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        (ConcreteElaboration.valuesFromEnvironmentFor source.val
          sourceContext.ids (source.val.wiresAt region) sourceExtended)
        sourceEnv =
      sourceExtended := by
  simp only
  apply extendEnvironment_from
  intro sig value
  have sameVar :=
    contextRenaming_appendRight source node eligible related region
      extendedRelated
      targetExtendedNodup value
  change
    ConcreteElaboration.extendEnvironment
        (Target source node eligible) targetContext region
        targetValues targetEnv sig
        (contextRenaming source node eligible
          extendedRelated
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) value)) =
      sourceEnv sig value
  rw [sameVar,
    ConcreteElaboration.extendEnvironment_appendRightVar]
  rw [outerRelated]
  rfl

private theorem source_extended_realizes_target
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated source node eligible
        (sourceContext.extend region) (targetContext.extend region))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv
          (contextRenaming source node eligible related))
    (sourceValues : ConcreteElaboration.WireValues pre
      ((source.val.wiresAt region).map fun wire =>
        (source.val.wires wire).sig)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv
    let targetExtended :=
      Env.comp sourceExtended
        (contextSection source node eligible
          extendedRelated)
    ConcreteElaboration.extendEnvironment
        (Target source node eligible) targetContext region
        (ConcreteElaboration.valuesFromEnvironmentFor
          (Target source node eligible) targetContext.ids
          ((Target source node eligible).wiresAt region) targetExtended)
        targetEnv =
      targetExtended := by
  simp only
  apply extendEnvironment_from
  intro sig value
  have sameVar :=
    contextSection_appendRight source node eligible related region
      extendedRelated
      sourceExtendedNodup value
  change
    ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv sig
        (contextSection source node eligible
          extendedRelated
          (ConcreteElaboration.appendRightVar
            (Target source node eligible)
            ((Target source node eligible).wiresAt region) value)) =
      targetEnv sig value
  rw [sameVar,
    ConcreteElaboration.extendEnvironment_appendRightVar]
  rw [outerRelated]
  change
    targetEnv sig
        (contextRenaming source node eligible related
          (contextSection source node eligible related value)) =
      targetEnv sig value
  rw [contextRenaming_section source node eligible related targetNodup]

private theorem compileChildren_cons_components
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
          context (child :: tail) =
        some items) :
    ∃ body rest,
      recurse child context = some body ∧
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context tail =
        some rest ∧
      items = .cons (.cut body) rest := by
  simp only [ConcreteElaboration.compileChildrenWith?] at compiled
  obtain ⟨body, rest, bodyEquation, restEquation, itemsEquation⟩ :=
    option_bind₂_eq_some compiled
  subst items
  exact ⟨body, rest, bodyEquation, restEquation, rfl⟩

private theorem compiled_children_equiv
    (definitions : List (List Sig))
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (sourceRecurse : (region : source.val.RegionId) →
      (context : ConcreteElaboration.WireContext source.val) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : (Target source node eligible).RegionId) →
      (context :
        ConcreteElaboration.WireContext (Target source node eligible)) →
        Option (Region definitions context.sigs))
    (sourceContext : ConcreteElaboration.WireContext source.val)
    (targetContext :
      ConcreteElaboration.WireContext (Target source node eligible))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceEnv : Env pre sourceContext.sigs)
    (targetEnv : Env pre targetContext.sigs)
    (children : List source.val.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse sourceContext children =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          (Target source node eligible)
          targetRecurse targetContext
          children =
        some targetItems)
    (bodyEquiv :
      ∀ child, child ∈ children →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse child targetContext = some targetBody →
          (denoteRegion pre definitionEnv sourceEnv sourceBody ↔
            denoteRegion pre definitionEnv targetEnv targetBody)) :
    denoteItemSeq pre definitionEnv sourceEnv sourceItems ↔
      denoteItemSeq pre definitionEnv targetEnv targetItems := by
  induction children generalizing sourceItems targetItems with
  | nil =>
      simp only [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      have sourceEmpty : sourceItems = .nil :=
        Option.some.inj sourceCompiled.symm
      have targetEmpty : targetItems = .nil :=
        Option.some.inj targetCompiled.symm
      subst sourceItems
      subst targetItems
      simp
  | cons child tail induction =>
      obtain ⟨sourceBody, sourceRest, sourceBodyCompiled,
          sourceRestCompiled, sourceEquation⟩ :=
        compileChildren_cons_components definitions source.val
          sourceRecurse sourceContext child tail sourceItems sourceCompiled
      obtain ⟨targetBody, targetRest, targetBodyCompiled,
          targetRestCompiled, targetEquation⟩ :=
        compileChildren_cons_components definitions
          (Target source node eligible)
          targetRecurse targetContext child tail targetItems targetCompiled
      subst sourceItems
      subst targetItems
      rw [denoteItemSeq_cons, denoteItemSeq_cons,
        cut_denotes_negation, cut_denotes_negation,
        induction sourceRest sourceRestCompiled targetRest
          targetRestCompiled (by
            intro tailChild tailMember sourceBody targetBody
              sourceBodyCompiled targetBodyCompiled
            exact bodyEquiv tailChild
              (List.mem_cons_of_mem child tailMember)
              sourceBody targetBody sourceBodyCompiled targetBodyCompiled)]
      exact and_congr
        (not_congr (bodyEquiv child (by simp) sourceBody targetBody
          sourceBodyCompiled targetBodyCompiled))
        Iff.rfl

private theorem targetNode_mem_nodesAt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId)
    (originalNode : source.val.NodeId)
    (survives : originalNode ≠ node)
    (member : originalNode ∈ source.val.nodesAt region) :
    targetNode source node eligible originalNode survives ∈
      (Target source node eligible).nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have sourceRegion := (List.mem_filter.mp member).2
    rw [target_node]
    unfold sourceNode
    rw [retained_get_targetNode source node eligible originalNode survives]
    exact sourceRegion

private theorem sourceNode_mem_nodesAt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId)
    (target : (Target source node eligible).NodeId)
    (member :
      target ∈ (Target source node eligible).nodesAt region) :
    sourceNode source node eligible target ∈
      source.val.nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  constructor
  · exact Data.Finite.mem_allFin _
  · have targetRegion := (List.mem_filter.mp member).2
    rw [target_node] at targetRegion
    exact targetRegion

private theorem retained_singleton_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (originalNode : source.val.NodeId)
    (survives : originalNode ≠ node)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceContext [originalNode] =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source node eligible) targetContext
          [targetNode source node eligible originalNode survives] =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source node eligible related))
        sourceItems := by
  obtain ⟨expected, expectedCompiled, expectedEquation⟩ :=
    compile_retained_singleton source node eligible related targetNodup
      originalNode survives sourceCompiled
  have targetEquation : targetItems = expected :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  subst targetItems
  rw [expectedEquation,
    denoteItemSeq_renameWires]

private theorem retained_item_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (originalNode : source.val.NodeId)
    (survives : originalNode ≠ node)
    (sourceItem : Item definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceContext [originalNode] =
        some (.cons sourceItem .nil))
    (targetItem : Item definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source node eligible) targetContext
          [targetNode source node eligible originalNode survives] =
        some (.cons targetItem .nil)) :
    denoteItem pre definitionEnv targetEnv targetItem ↔
      denoteItem pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source node eligible related))
        sourceItem := by
  have sequence :=
    retained_singleton_denotation source node eligible related targetNodup
      pre definitionEnv targetEnv originalNode survives
      (.cons sourceItem .nil) sourceCompiled
      (.cons targetItem .nil) targetCompiled
  simpa using sequence

private theorem compiled_nodes_under_pullback
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (region : source.val.RegionId)
    (sourceItems : ItemSeq definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val sourceContext
          (source.val.nodesAt region) =
        some sourceItems)
    (targetItems : ItemSeq definitions targetContext.sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source node eligible) targetContext
          ((Target source node eligible).nodesAt region) =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source node eligible related))
        sourceItems := by
  rw [denote_compileNodes_iff_singletons definitions
      (Target source node eligible) targetContext pre definitionEnv
      targetEnv _ _ targetCompiled,
    denote_compileNodes_iff_singletons definitions source.val sourceContext
      pre definitionEnv
      (Env.comp targetEnv
        (contextRenaming source node eligible related))
      _ _ sourceCompiled]
  constructor
  · intro targetDenotes originalNode originalMember
    by_cases removed : originalNode = node
    · subst originalNode
      obtain ⟨identityItem, identityCompiled⟩ :=
        compileNodes_singleton_of_member definitions source.val sourceContext
          (source.val.nodesAt region) sourceItems sourceCompiled node
          originalMember
      exact ⟨_, identityCompiled,
        (by
          have sequence :=
            identity_denotes_under_pullback source node eligible related
              targetNodup pre definitionEnv targetEnv _ identityCompiled
          exact sequence.1)⟩
    · obtain ⟨sourceSingletonItem, sourceSingletonCompiled⟩ :=
        compileNodes_singleton_of_member definitions source.val sourceContext
          (source.val.nodesAt region) sourceItems sourceCompiled originalNode
          originalMember
      obtain ⟨targetSingleton, targetSingletonCompiled, targetSingletonDenotes⟩ :=
        targetDenotes
          (targetNode source node eligible originalNode removed)
          (targetNode_mem_nodesAt source node eligible region
            originalNode removed originalMember)
      exact ⟨sourceSingletonItem, sourceSingletonCompiled,
        (retained_item_denotation source node eligible related targetNodup
          pre definitionEnv targetEnv originalNode removed sourceSingletonItem
          sourceSingletonCompiled targetSingleton
          targetSingletonCompiled).mp targetSingletonDenotes⟩
  · intro sourceDenotes target targetMember
    let originalNode := sourceNode source node eligible target
    have survives := sourceNode_ne source node eligible target
    have originalMember :=
      sourceNode_mem_nodesAt source node eligible region target targetMember
    obtain ⟨sourceSingleton, sourceSingletonCompiled,
        sourceSingletonDenotes⟩ :=
      sourceDenotes originalNode originalMember
    obtain ⟨targetSingleton, targetSingletonCompiled⟩ :=
      compileNodes_singleton_of_member definitions
        (Target source node eligible) targetContext
        ((Target source node eligible).nodesAt region) targetItems
        targetCompiled target targetMember
    have targetNodeEquation :
        targetNode source node eligible originalNode survives = target :=
      targetNode_sourceNode source node eligible target
    have targetSingletonCompiled' :
        ConcreteElaboration.compileNodes? definitions
            (Target source node eligible) targetContext
            [targetNode source node eligible originalNode survives] =
          some (.cons targetSingleton .nil) := by
      rw [targetNodeEquation]
      exact targetSingletonCompiled
    exact ⟨targetSingleton, targetSingletonCompiled,
      (retained_item_denotation source node eligible related targetNodup
        pre definitionEnv targetEnv originalNode survives sourceSingleton
        sourceSingletonCompiled targetSingleton
        targetSingletonCompiled').mpr sourceSingletonDenotes⟩

private theorem pullback_one_point
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (pre : PreModel)
    (targetEnv : Env pre targetContext.sigs) :
    let sourceEnv :=
      Env.comp targetEnv
        (contextRenaming source node eligible related)
    Env.comp
        (Env.comp sourceEnv
          (contextSection source node eligible related))
        (contextRenaming source node eligible related) =
      sourceEnv := by
  simp only
  funext sig value
  change
    targetEnv sig
        (contextRenaming source node eligible related
          (contextSection source node eligible related
            (contextRenaming source node eligible related value))) =
      targetEnv sig
        (contextRenaming source node eligible related value)
  rw [contextRenaming_section source node eligible related targetNodup]

private theorem extended_one_point_without_local_incident
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    {sourceContext : ConcreteElaboration.WireContext source.val}
    {targetContext :
      ConcreteElaboration.WireContext (Target source node eligible)}
    (related :
      ContextsRelated source node eligible sourceContext targetContext)
    (region : source.val.RegionId)
    (extendedRelated :
      ContextsRelated source node eligible
        (sourceContext.extend region) (targetContext.extend region))
    (sourceExtendedNodup : (sourceContext.extend region).ids.Nodup)
    (targetExtendedNodup : (targetContext.extend region).ids.Nodup)
    (localRepresentative :
      ∀ wire, wire ∈ source.val.wiresAt region →
        representative source node eligible wire = wire)
    (pre : PreModel)
    (sourceEnv : Env pre sourceContext.sigs)
    (sourceOnePoint :
      Env.comp
          (Env.comp sourceEnv
            (contextSection source node eligible related))
          (contextRenaming source node eligible related) =
        sourceEnv)
    (sourceValues : ConcreteElaboration.WireValues pre
      ((source.val.wiresAt region).map fun wire =>
        (source.val.wires wire).sig)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val sourceContext region
        sourceValues sourceEnv
    Env.comp
        (Env.comp sourceExtended
          (contextSection source node eligible extendedRelated))
        (contextRenaming source node eligible extendedRelated) =
      sourceExtended := by
  simp only
  funext sig value
  let wire :=
    ConcreteElaboration.WireContext.origin source.val
      (sourceContext.extend region).ids value
  have wireMember :
      wire ∈ source.val.wiresAt region ∨ wire ∈ sourceContext.ids := by
    have := origin_mem source.val (sourceContext.extend region).ids value
    simpa [ConcreteElaboration.WireContext.extend] using this
  rcases wireMember with localMember | outerMember
  · have representativeSelf := localRepresentative wire localMember
    have sectionOrigin :
        ConcreteElaboration.WireContext.origin source.val
            (sourceContext.extend region).ids
            (contextSection source node eligible
              extendedRelated
              (contextRenaming source node eligible
                extendedRelated
                value)) =
          wire := by
      rw [contextSection_origin, contextRenaming_origin,
        sourceWire_targetWire]
      simpa [wire] using representativeSelf
    have sameVariable :
        contextSection source node eligible
            extendedRelated
            (contextRenaming source node eligible
              extendedRelated
              value) =
          value :=
      origin_injective source.val (sourceContext.extend region).ids
        sourceExtendedNodup (by simpa [wire] using sectionOrigin)
    change
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (contextSection source node eligible
            extendedRelated
            (contextRenaming source node eligible
              extendedRelated
              value)) =
        ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig value
    rw [sameVariable]
  · let outerVar :=
      varForMember source.val wire sourceContext.ids outerMember
    let signature : (source.val.wires wire).sig = sig :=
      ConcreteElaboration.WireContext.origin_signature source.val
        (sourceContext.extend region).ids value
    let outerVar' : Var sourceContext.sigs sig :=
      castVar signature outerVar
    have valueEquation :
        value =
          ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) outerVar' := by
      apply origin_injective source.val (sourceContext.extend region).ids
        sourceExtendedNodup
      unfold ConcreteElaboration.WireContext.extend
      rw [ConcreteElaboration.origin_appendRightVar,
        show
          ConcreteElaboration.WireContext.origin source.val
              sourceContext.ids outerVar' =
            wire by
            calc
              _ = ConcreteElaboration.WireContext.origin source.val
                    sourceContext.ids outerVar := by
                    exact origin_castVar source.val sourceContext
                      signature outerVar
              _ = wire := origin_varForMember source.val wire
                sourceContext.ids outerMember]
      rfl
    rw [valueEquation]
    change
      ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (contextSection source node eligible
            extendedRelated
            (contextRenaming source node eligible
              extendedRelated
              (ConcreteElaboration.appendRightVar source.val
                (source.val.wiresAt region) outerVar'))) =
        ConcreteElaboration.extendEnvironment source.val sourceContext region
          sourceValues sourceEnv sig
          (ConcreteElaboration.appendRightVar source.val
            (source.val.wiresAt region) outerVar')
    rw [contextRenaming_appendRight source node eligible related region
        extendedRelated targetExtendedNodup,
      contextSection_appendRight source node eligible related region
        extendedRelated sourceExtendedNodup,
      ConcreteElaboration.extendEnvironment_appendRightVar,
      ConcreteElaboration.extendEnvironment_appendRightVar]
    exact congrFun (congrFun sourceOnePoint sig) outerVar'

private theorem representative_local_of_region_ne
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId)
    (different : region ≠ eligible.identity.region)
    (wire : source.val.WireId)
    (localMember : wire ∈ source.val.wiresAt region) :
    representative source node eligible wire = wire := by
  have localScope :
      (source.val.wires wire).scope = region := by
    unfold ConcreteDiagram.wiresAt at localMember
    exact eq_of_beq (List.mem_filter.mp localMember).2
  unfold representative
  split
  · rename_i incident
    rcases
        (incident_eq_survivor_or_absorbed source node eligible wire).mp
          incident with wireSurvivor | absorbed
    · exact wireSurvivor.symm
    · have absorbedScope :=
        eligible.absorbedCoScoped wire absorbed
      exact False.elim (different (localScope.symm.trans absorbedScope))
  · rfl

@[simp] private theorem target_childrenOf
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (region : source.val.RegionId) :
    (Target source node eligible).childrenOf region =
      source.val.childrenOf region := by
  unfold Target
  dsimp [collapseCandidate, ConcreteDiagram.childrenOf,
    ConcreteDiagram.regionsList]
  apply List.filter_congr
  intro child _
  cases source.val.regions child <;> rfl

private theorem compileRegion_equiv
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      {sourceContext : ConcreteElaboration.WireContext source.val}
      {targetContext :
        ConcreteElaboration.WireContext (Target source node eligible)}
      (related :
        ContextsRelated source node eligible sourceContext targetContext)
      (region : source.val.RegionId)
      (_sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      (_targetAbove :
        ConcreteElaboration.ContextAbove (Target source node eligible)
          targetContext region)
      (sourceEnv : Env pre sourceContext.sigs)
      (targetEnv : Env pre targetContext.sigs)
      (_outerRelated :
        sourceEnv =
          Env.comp targetEnv
            (contextRenaming source node eligible related))
      (_sourceOnePoint :
        Env.comp
            (Env.comp sourceEnv
              (contextSection source node eligible related))
            (contextRenaming source node eligible related) =
          sourceEnv)
      {sourceBody : Region definitions sourceContext.sigs}
      {targetBody : Region definitions targetContext.sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions
          (Target source node eligible) fuel region targetContext =
        some targetBody →
      (denoteRegion pre definitionEnv sourceEnv sourceBody ↔
        denoteRegion pre definitionEnv targetEnv targetBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceContext targetContext related region _sourceAbove _targetAbove
        sourceEnv targetEnv _outerRelated _sourceOnePoint sourceBody targetBody
        sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ fuel induction =>
      intro sourceContext targetContext related region _sourceAbove _targetAbove
        sourceEnv targetEnv _outerRelated _sourceOnePoint sourceBody targetBody
        sourceCompiled targetCompiled
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (sourceContext.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions source.val fuel)
                (sourceContext.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              cases targetNodesEquation :
                  ConcreteElaboration.compileNodes? definitions
                    (Target source node eligible)
                    (targetContext.extend region)
                    ((Target source node eligible).nodesAt region) with
              | none =>
                  rw [targetNodesEquation] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEquation] at targetCompiled
                  cases targetChildrenEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        (Target source node eligible)
                        (ConcreteElaboration.compileRegion? definitions
                          (Target source node eligible) fuel)
                        (targetContext.extend region)
                        ((Target source node eligible).childrenOf region) with
                  | none =>
                      rw [targetChildrenEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEquation] at targetCompiled
                      have targetChildrenEquation' :
                          ConcreteElaboration.compileChildrenWith? definitions
                              (Target source node eligible)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source node eligible) fuel)
                              (targetContext.extend region)
                              (source.val.childrenOf region) =
                            some targetChildren := by
                        simpa only [target_childrenOf] using
                          targetChildrenEquation
                      have sourceBodyEquality :
                          ConcreteElaboration.finishRegion source.val
                              sourceContext region
                              (.mk (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyEquality :
                          ConcreteElaboration.finishRegion
                              (Target source node eligible) targetContext region
                              (.mk (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      rw [ConcreteElaboration.denote_finishRegion,
                        ConcreteElaboration.denote_finishRegion]
                      let extendedRelated :=
                        extend_contexts_related source node eligible related
                          region (fun regionIdentity survivorNotLocal =>
                            survivor_mem_outer_context source node eligible
                              sourceContext region regionIdentity
                              survivorNotLocal sourceNodes
                              sourceNodesEquation)
                      have sourceExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions source.val
                          source.property sourceContext region _sourceAbove
                      have targetExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          (Target source node eligible)
                          (collapseCandidate_wellFormed source node eligible)
                          targetContext region _targetAbove
                      constructor
                      · rintro ⟨sourceValues, sourceCoreDenotes⟩
                        let sourceExtended :=
                          ConcreteElaboration.extendEnvironment source.val
                            sourceContext region sourceValues sourceEnv
                        let targetExtended :=
                          Env.comp sourceExtended
                            (contextSection source node eligible
                              extendedRelated)
                        let targetValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            (Target source node eligible) targetContext.ids
                            ((Target source node eligible).wiresAt region)
                            targetExtended
                        have targetRealizes :
                            ConcreteElaboration.extendEnvironment
                                (Target source node eligible) targetContext
                                region targetValues targetEnv =
                              targetExtended :=
                          source_extended_realizes_target source node eligible
                            related region extendedRelated
                            sourceExtendedNodup
                            _targetAbove.1 pre sourceEnv targetEnv _outerRelated
                            sourceValues
                        refine ⟨targetValues, ?_⟩
                        rw [targetRealizes]
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren) at sourceCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                        rw [denoteItemSeq_append] at sourceCoreDenotes ⊢
                        have extendedOnePoint :
                            Env.comp
                                (Env.comp sourceExtended
                                  (contextSection source node eligible
                                    extendedRelated))
                                (contextRenaming source node eligible
                                  extendedRelated) =
                              sourceExtended := by
                          by_cases same :
                              region = eligible.identity.region
                          · subst region
                            obtain ⟨identityItem, identityCompiled,
                                identityDenotes⟩ :=
                              (denote_compileNodes_iff_singletons definitions
                                source.val (sourceContext.extend
                                  eligible.identity.region)
                                pre definitionEnv sourceExtended
                                (source.val.nodesAt
                                  eligible.identity.region)
                                sourceNodes sourceNodesEquation).mp
                                  sourceCoreDenotes.1 node
                                  (identity_mem_nodesAt source node eligible)
                            exact source_environment_one_point source node
                              eligible extendedRelated sourceExtendedNodup pre
                              definitionEnv sourceExtended
                              (.cons identityItem .nil)
                              identityCompiled (by simpa using identityDenotes)
                          · exact
                              extended_one_point_without_local_incident source
                                node eligible related region extendedRelated
                                sourceExtendedNodup
                                targetExtendedNodup
                                (representative_local_of_region_ne source node
                                  eligible region same)
                                pre sourceEnv _sourceOnePoint sourceValues
                        have extendedEnvRelated :
                            sourceExtended =
                              Env.comp targetExtended
                                (contextRenaming source node eligible
                                  extendedRelated) := by
                          exact extendedOnePoint.symm
                        constructor
                        · exact
                            (compiled_nodes_under_pullback source node eligible
                              extendedRelated targetExtendedNodup pre
                              definitionEnv targetExtended region sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mpr
                              (by
                                rw [← extendedEnvRelated]
                                exact sourceCoreDenotes.1)
                        · apply
                            (compiled_children_equiv definitions source node
                              eligible
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source node eligible) fuel)
                              (sourceContext.extend region)
                              (targetContext.extend region)
                              pre definitionEnv sourceExtended targetExtended
                              (source.val.childrenOf region) sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation' ?_).mp
                              sourceCoreDenotes.2
                          intro child childMember childSourceBody
                            childTargetBody childSourceCompiled
                            childTargetCompiled
                          have sourceChildData :=
                            ConcreteElaboration.mem_childrenOf source.val region
                              child childMember
                          have targetChildData :
                              (Target source node eligible).regions child =
                                .cut region := by
                            simpa [Target, collapseCandidate] using
                              sourceChildData
                          have sourceChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceContext region
                              child _sourceAbove sourceChildData
                          have targetChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              (Target source node eligible)
                              (collapseCandidate_wellFormed source node
                                eligible)
                              targetContext region child _targetAbove
                              targetChildData
                          exact induction extendedRelated child
                            sourceChildAbove targetChildAbove sourceExtended
                            targetExtended extendedEnvRelated extendedOnePoint
                            childSourceCompiled childTargetCompiled
                      · rintro ⟨targetValues, targetCoreDenotes⟩
                        let targetExtended :=
                          ConcreteElaboration.extendEnvironment
                            (Target source node eligible) targetContext region
                            targetValues targetEnv
                        let sourceExtended :=
                          Env.comp targetExtended
                            (contextRenaming source node eligible
                              extendedRelated)
                        let sourceValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            source.val sourceContext.ids
                            (source.val.wiresAt region) sourceExtended
                        have sourceRealizes :
                            ConcreteElaboration.extendEnvironment source.val
                                sourceContext region sourceValues sourceEnv =
                              sourceExtended :=
                          target_extended_realizes_source source node eligible
                            related region extendedRelated
                            targetExtendedNodup pre sourceEnv
                            targetEnv _outerRelated targetValues
                        refine ⟨sourceValues, ?_⟩
                        rw [sourceRealizes]
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren) at targetCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                        rw [denoteItemSeq_append] at targetCoreDenotes ⊢
                        have extendedOnePoint :=
                          pullback_one_point source node eligible
                            extendedRelated targetExtendedNodup pre
                            targetExtended
                        constructor
                        · exact
                            (compiled_nodes_under_pullback source node eligible
                              extendedRelated targetExtendedNodup pre
                              definitionEnv targetExtended region sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mp targetCoreDenotes.1
                        · apply
                            (compiled_children_equiv definitions source node
                              eligible
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source node eligible) fuel)
                              (sourceContext.extend region)
                              (targetContext.extend region)
                              pre definitionEnv sourceExtended targetExtended
                              (source.val.childrenOf region) sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation' ?_).mpr
                              targetCoreDenotes.2
                          intro child childMember childSourceBody
                            childTargetBody childSourceCompiled
                            childTargetCompiled
                          have sourceChildData :=
                            ConcreteElaboration.mem_childrenOf source.val region
                              child childMember
                          have targetChildData :
                              (Target source node eligible).regions child =
                                .cut region := by
                            simpa [Target, collapseCandidate] using
                              sourceChildData
                          have sourceChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              source.val source.property sourceContext region
                              child _sourceAbove sourceChildData
                          have targetChildAbove :=
                            ConcreteElaboration.extend_above_child definitions
                              (Target source node eligible)
                              (collapseCandidate_wellFormed source node
                                eligible)
                              targetContext region child _targetAbove
                              targetChildData
                          exact induction extendedRelated child
                            sourceChildAbove targetChildAbove sourceExtended
                            targetExtended rfl extendedOnePoint
                            childSourceCompiled childTargetCompiled

private theorem collapseCandidate_denotation
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv
        ⟨Target source node eligible,
          collapseCandidate_wellFormed source node eligible⟩ ↔
      denoteChecked pre definitionEnv source := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked]
  have sourceCompiled :=
    elaborateWith_compiles definitions source.val source.property
  have targetCompiled :=
    elaborateWith_compiles definitions
      (Target source node eligible)
      (collapseCandidate_wellFormed source node eligible)
  unfold ConcreteElaboration.compileRoot? at sourceCompiled targetCompiled
  have targetCompiled' :
      ConcreteElaboration.compileRegion? definitions
          (Target source node eligible) (source.val.regionCount + 1)
          source.val.root
          (ConcreteElaboration.WireContext.empty
            (Target source node eligible)) =
        some (elaborateWith definitions
          (Target source node eligible)
          (collapseCandidate_wellFormed source node eligible)) := by
    simpa [Target, collapseCandidate] using targetCompiled
  have sourceAbove :
      ConcreteElaboration.ContextAbove source.val
        (ConcreteElaboration.WireContext.empty source.val)
        source.val.root := by
    constructor
    · simp [ConcreteElaboration.WireContext.empty]
    · intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member
  have targetAbove :
      ConcreteElaboration.ContextAbove (Target source node eligible)
        (ConcreteElaboration.WireContext.empty
          (Target source node eligible))
        source.val.root := by
    constructor
    · simp [ConcreteElaboration.WireContext.empty]
    · intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member
  have emptyRelated :=
    empty_contexts_related source node eligible
  have emptyEnvRelated :
      (Env.empty : Env pre []) =
        Env.comp Env.empty
          (contextRenaming source node eligible emptyRelated) := by
    funext sig value
    nomatch value
  have emptyOnePoint :
      Env.comp
          (Env.comp (Env.empty : Env pre [])
            (contextSection source node eligible emptyRelated))
          (contextRenaming source node eligible emptyRelated) =
        Env.empty := by
    funext sig value
    nomatch value
  exact
    (compileRegion_equiv source node eligible pre definitionEnv
      (source.val.regionCount + 1) emptyRelated source.val.root sourceAbove
      targetAbove Env.empty Env.empty emptyEnvRelated emptyOnePoint
      sourceCompiled targetCompiled').symm

end IdentityNormalizationCollapseSemantics

/--
Rule 2 preserves denotation in every premodel.  Its only premise is the
successful checked structural rewrite; no semantic certificate is required.
-/
theorem collapseOnePoint_sound
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (target : IdentityRewrite source)
    (result : collapseOnePoint source node = some target)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv target.target ↔
      denoteChecked pre definitionEnv source := by
  unfold collapseOnePoint at result
  cases eligibleEquation :
      IdentityNormalizationCore.collapseEligibility? source node with
  | none =>
      rw [eligibleEquation] at result
      simp at result
  | some eligible =>
      rw [eligibleEquation] at result
      have targetEquation := Option.some.inj result
      subst target
      exact
        IdentityNormalizationCollapseSemantics.collapseCandidate_denotation
          source node eligible pre definitionEnv

end ConcreteDiagram

end VisualProof
