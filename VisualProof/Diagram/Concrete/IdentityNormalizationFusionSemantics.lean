import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.ElaborationInvariance

namespace VisualProof

universe u

namespace ConcreteDiagram

open IdentityNormalizationCore
open DenseErasure

namespace IdentityNormalizationFusionSemantics

abbrev Target
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :=
  fusionCandidate source left right eligible

private abbrev fusionNodes
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId) :=
  retainedNodes source.val [right]

def sourceWire
    (source : CheckedDiagram definitions)
    (wire : Fin source.val.wiresList.length) :
    source.val.WireId :=
  source.val.wiresList.get wire

def targetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Fin source.val.wiresList.length :=
  ⟨wire.val, by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, wire.isLt]⟩

@[simp] theorem sourceWire_targetWire
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    sourceWire source (targetWire source wire) = wire := by
  apply Fin.ext
  simp [sourceWire, targetWire, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange]

theorem targetWire_injective
    (source : CheckedDiagram definitions) :
    Function.Injective (targetWire source) := by
  intro leftWire rightWire equality
  apply Fin.ext
  simpa [targetWire] using congrArg Fin.val equality

@[simp] theorem targetWire_sourceWire
    (source : CheckedDiagram definitions)
    (wire : Fin source.val.wiresList.length) :
    targetWire source (sourceWire source wire) = wire := by
  apply Fin.ext
  simp [targetWire, sourceWire, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange]

def targetNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : source.val.NodeId)
    (survives : node ≠ right) :
    Fin (fusionNodes source right).length :=
  (Data.Finite.indexOf? (fusionNodes source right) node).get
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))

@[simp] theorem fusionNodes_get_targetNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : source.val.NodeId)
    (survives : node ≠ right) :
    (fusionNodes source right).get
        (targetNode source right node survives) = node := by
  unfold targetNode
  apply Data.Finite.indexOf?_sound
  exact Option.eq_some_of_isSome
    (Data.Finite.indexOf?_isSome_iff.mpr (by
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin _, by simp [survives]⟩))

def sourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) :
    source.val.NodeId :=
  (fusionNodes source right).get node

theorem sourceNode_ne_right
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) :
    sourceNode source right node ≠ right := by
  have member := List.get_mem (fusionNodes source right) node
  have accepted := (List.mem_filter.mp member).2
  simpa [sourceNode, fusionNodes, retainedNodes] using
    of_decide_eq_true accepted

@[simp] theorem targetNode_sourceNode
    (source : CheckedDiagram definitions)
    (right : source.val.NodeId)
    (node : Fin (fusionNodes source right).length) :
    targetNode source right (sourceNode source right node)
        (sourceNode_ne_right source right node) = node := by
  have nodup : (fusionNodes source right).Nodup :=
    (Data.Finite.allFin_nodup source.val.nodeCount).filter _
  symm
  apply Data.Finite.indexOf?_unique_of_nodup nodup
  · exact Option.eq_some_of_isSome
      (Data.Finite.indexOf?_isSome_iff.mpr
        (List.get_mem (fusionNodes source right) node))
  · rfl

@[simp] private theorem targetWire_signature
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId) :
    ((Target source left right eligible).wires
      (targetWire source wire)).sig =
      (source.val.wires wire).sig := by
  change
    (source.val.wires
      (source.val.wiresList.get (targetWire source wire))).sig =
      (source.val.wires wire).sig
  have equality :
      source.val.wiresList.get (targetWire source wire) = wire :=
    sourceWire_targetWire source wire
  rw [equality]

private def targetContext
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    ConcreteElaboration.WireContext
      (Target source left right eligible) :=
  ⟨context.ids.map (targetWire source)⟩

private theorem targetContext_sigs
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    (targetContext source left right eligible context).sigs =
      context.sigs := by
  unfold targetContext ConcreteElaboration.WireContext.sigs
  rw [List.map_map]
  apply List.map_inj_left.mpr
  intro wire _
  exact targetWire_signature source left right eligible wire

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
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (ids : List source.val.WireId) :
    WireRenaming
      (ids.map fun wire => (source.val.wires wire).sig)
      ((ids.map (targetWire source)).map fun wire =>
        ((Target source left right eligible).wires wire).sig) :=
  match ids with
  | [] => fun value => nomatch value
  | head :: tail =>
      fun value =>
        match value with
        | Var.here =>
            mappedHere
              (tail :=
                (tail.map (targetWire source)).map fun wire =>
                  ((Target source left right eligible).wires wire).sig)
              (targetWire_signature source left right eligible head)
        | Var.there value =>
            Var.there
              (contextRenamingFor source left right eligible tail value)
termination_by ids

private def contextRenaming
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming context.sigs
      (targetContext source left right eligible context).sigs :=
  contextRenamingFor source left right eligible context.ids

private theorem contextRenaming_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    ∀ {sig} (value : Var context.sigs sig),
      ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          (contextRenaming source left right eligible context value) =
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
                (Target source left right eligible)
                (targetWire source head)
                (tail.map (targetWire source))
                (targetWire_signature source left right eligible head)
          | there value =>
              simpa [contextRenaming, contextRenamingFor, targetContext,
                ConcreteElaboration.WireContext.origin] using induction value

private theorem targetContext_nodup
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (nodup : context.ids.Nodup) :
    (targetContext source left right eligible context).ids.Nodup := by
  rw [List.nodup_iff_pairwise_ne] at nodup ⊢
  exact nodup.map (targetWire source) (by
    intro leftWire rightWire different equality
    exact different ((targetWire_injective source) equality))

private def contextSectionFor
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (ids : List source.val.WireId) :
    WireRenaming
      ((ids.map (targetWire source)).map fun wire =>
        ((Target source left right eligible).wires wire).sig)
      (ids.map fun wire => (source.val.wires wire).sig) :=
  match ids with
  | [] => fun value => nomatch value
  | head :: tail =>
      fun value =>
        match value with
        | Var.here =>
            mappedHere
              (tail := tail.map fun wire => (source.val.wires wire).sig)
              (targetWire_signature source left right eligible head).symm
        | Var.there value =>
            Var.there
              (contextSectionFor source left right eligible tail value)
termination_by ids

private def contextSection
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    WireRenaming
      (targetContext source left right eligible context).sigs
      context.sigs :=
  contextSectionFor source left right eligible context.ids

private theorem contextSection_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val) :
    ∀ {sig}
      (value :
        Var
          (targetContext source left right eligible context).sigs sig),
      ConcreteElaboration.WireContext.origin
          source.val context.ids
          (contextSection source left right eligible context value) =
        sourceWire source
          (ConcreteElaboration.WireContext.origin
            (Target source left right eligible)
            (targetContext source left right eligible context).ids
            value) := by
  intro sig value
  cases context with
  | mk ids =>
      induction ids with
      | nil => nomatch value
      | cons head tail induction =>
          cases value with
          | here =>
              simp only [contextSection, targetContext,
                contextSectionFor]
              change
                ConcreteElaboration.WireContext.origin source.val
                    (head :: tail)
                    (mappedHere
                      (tail := tail.map fun wire =>
                        (source.val.wires wire).sig)
                      (targetWire_signature
                        source left right eligible head).symm) =
                  sourceWire source (targetWire source head)
              rw [origin_mappedHere, sourceWire_targetWire]
          | there value =>
              simpa [contextSection, contextSectionFor, targetContext,
                ConcreteElaboration.WireContext.origin] using induction value

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

private theorem target_wiresAt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : source.val.RegionId) :
    (Target source left right eligible).wiresAt region =
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
    (congrArg source.val.wires (sourceWire_targetWire source wire))

private theorem targetContext_extend
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    targetContext source left right eligible (context.extend region) =
      (targetContext source left right eligible context).extend region := by
  cases context
  simp only [targetContext, ConcreteElaboration.WireContext.extend,
    target_wiresAt, List.map_append]
  rfl

theorem targetEndpoint_incident
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (node : source.val.NodeId)
    (notLeft : node ≠ left)
    (notRight : node ≠ right)
    (port : CPort)
    (wire : source.val.WireId)
    (incident :
      (⟨node, port⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires wire).endpoints) :
    (⟨targetNode source right node notRight, port⟩ :
      CEndpoint (Target source left right eligible).nodeCount) ∈
        ((Target source left right eligible).wires
          (targetWire source wire)).endpoints := by
  simp only [fusionCandidate]
  have wireEquality :
      source.val.wiresList.get (targetWire source wire) = wire :=
    sourceWire_targetWire source wire
  rw [wireEquality]
  apply List.mem_append.mpr
  apply Or.inl
  apply List.mem_filterMap.mpr
  refine
    ⟨(⟨node, port⟩ : CEndpoint source.val.nodeCount), ?_, ?_⟩
  · apply List.mem_filter.mpr
    exact ⟨incident, by simp [notLeft, notRight]⟩
  · unfold reindexEndpoint?
    have found :
        Data.Finite.indexOf? (fusionNodes source right) node =
          some (targetNode source right node notRight) := by
      unfold targetNode
      exact (Option.some_get _).symm
    simp [fusionNodes, found]

theorem target_node_of_not_left
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (node : source.val.NodeId)
    (notLeft : node ≠ left)
    (notRight : node ≠ right) :
    (Target source left right eligible).nodes
        (targetNode source right node notRight) =
      source.val.nodes node := by
  change
    (if
      (fusionNodes source right).get
          (targetNode source right node notRight) = left
    then
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (source.val.identityIncidentWires left ++
          source.val.identityIncidentWires right).eraseDups.length
    else
      source.val.nodes
        ((fusionNodes source right).get
          (targetNode source right node notRight))) =
      source.val.nodes node
  rw [fusionNodes_get_targetNode]
  simp [notLeft]

private theorem compile_ordinary_singleton
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (node : source.val.NodeId)
    (notLeft : node ≠ left)
    (notRight : node ≠ right)
    {sourceItems : ItemSeq definitions context.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [node] = some sourceItems) :
    ∃ targetItems :
        ItemSeq definitions
          (targetContext source left right eligible context).sigs,
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          [targetNode source right node notRight] =
        some targetItems ∧
      targetItems =
        sourceItems.renameWires
          (contextRenaming source left right eligible context) := by
  apply ConcreteElaboration.compileNodes?_singleton_natural
    (fusionCandidate_wellFormed source left right eligible)
    (targetContext_nodup source left right eligible context contextNodup)
    (contextRenaming source left right eligible context)
    (targetWire source)
    (targetWire_signature source left right eligible)
    (contextRenaming_origin source left right eligible context)
    id node (targetNode source right node notRight)
  · rw [target_node_of_not_left source left right eligible
      node notLeft notRight]
    cases source.val.nodes node <;> rfl
  · intro port wire incident
    exact targetEndpoint_incident source left right eligible
      node notLeft notRight port wire incident
  · exact sourceCompiled

private theorem option_bind₂_eq_some
    {first : Option α} {second : Option β}
    {combine : α → β → γ} {result : γ}
    (equation :
      (do
        let left ← first
        let right ← second
        pure (combine left right)) = some result) :
    ∃ left right,
      first = some left ∧ second = some right ∧
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
          (node :: tail) = some items) :
    ∃ head rest,
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some (.cons head .nil) ∧
      ConcreteElaboration.compileNodes? definitions diagram context tail =
          some rest ∧
      items = .cons head rest := by
  rw [ConcreteElaboration.compileNodes?_equation] at compiled
  obtain ⟨head, rest, headEquation, restEquation, itemsEquation⟩ :=
    option_bind₂_eq_some compiled
  subst items
  refine ⟨head, rest, ?_, restEquation, rfl⟩
  simp only [ConcreteElaboration.compileNodes?_equation]
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
              [node] = some (.cons item .nil) ∧
          denoteItem pre definitionEnv env item := by
  induction nodes generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileNodes?_equation] at compiled
      have itemsEmpty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons head tail induction =>
      obtain ⟨headItem, restItems, headCompiled, restCompiled,
          itemsEquation⟩ :=
        compileNodes_cons_components definitions diagram context head tail
          items compiled
      subst items
      rw [denoteItemSeq_cons, induction restItems restCompiled]
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ candidate member
        rcases List.mem_cons.mp member with equality | tailMember
        · subst candidate
          exact ⟨headItem, headCompiled, headDenotes⟩
        · exact tailDenotes candidate tailMember
      · intro each
        obtain ⟨actualHead, actualCompiled, headDenotes⟩ :=
          each head (by simp)
        have actualEquality : actualHead = headItem :=
          ItemSeq.cons.inj
            (Option.some.inj
              (actualCompiled.symm.trans headCompiled)) |>.1
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
              have equality :
                  head =
                    ConcreteElaboration.WireContext.origin
                      diagram tail right := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              rw [← equality] at rightMember
              exact False.elim (headNotTail rightMember)
      | there left =>
          cases right with
          | here =>
              have leftMember :=
                origin_mem diagram tail left
              have headNotTail := (List.nodup_cons.mp nodup).1
              have equality :
                  ConcreteElaboration.WireContext.origin
                      diagram tail left =
                    head := by
                simpa [ConcreteElaboration.WireContext.origin] using same
              rw [equality] at leftMember
              exact False.elim (headNotTail leftMember)
          | there right =>
              exact congrArg Var.there
                (induction (List.nodup_cons.mp nodup).2
                  (by simpa [ConcreteElaboration.WireContext.origin]
                    using same))

private theorem contextRenaming_section
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (targetNodup :
      (targetContext source left right eligible context).ids.Nodup)
    {sig : Sig}
    (value :
      Var
        (targetContext source left right eligible context).sigs sig) :
    contextRenaming source left right eligible context
        (contextSection source left right eligible context value) =
      value := by
  apply origin_injective
    (Target source left right eligible)
    (targetContext source left right eligible context).ids
    targetNodup
  rw [contextRenaming_origin, contextSection_origin,
    targetWire_sourceWire]

private theorem contextSection_renaming
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (sourceNodup : context.ids.Nodup)
    {sig : Sig}
    (value : Var context.sigs sig) :
    contextSection source left right eligible context
        (contextRenaming source left right eligible context value) =
      value := by
  apply origin_injective source.val context.ids sourceNodup
  rw [contextSection_origin, contextRenaming_origin,
    sourceWire_targetWire]

private def extendedContextRenaming
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    WireRenaming (context.extend region).sigs
      ((targetContext source left right eligible context).extend region).sigs :=
  fun {_} value =>
    congrArg ConcreteElaboration.WireContext.sigs
        (targetContext_extend source left right eligible context region) ▸
      contextRenaming source left right eligible
        (context.extend region) value

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

private theorem extendedContextRenaming_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    ∀ {sig} (value : Var (context.extend region).sigs sig),
      ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          ((targetContext source left right eligible context).extend
            region).ids
          (extendedContextRenaming source left right eligible
            context region value) =
        targetWire source
          (ConcreteElaboration.WireContext.origin source.val
            (context.extend region).ids value) := by
  intro sig value
  calc
    _ = ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          (targetContext source left right eligible
            (context.extend region)).ids
          (contextRenaming source left right eligible
            (context.extend region) value) :=
      origin_context_cast
        (Target source left right eligible)
        (targetContext source left right eligible
          (context.extend region))
        ((targetContext source left right eligible context).extend region)
        (targetContext_extend source left right eligible context region)
        (contextRenaming source left right eligible
          (context.extend region) value)
    _ = _ :=
      contextRenaming_origin source left right eligible
        (context.extend region) value

private def extendedContextSection
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId) :
    WireRenaming
      ((targetContext source left right eligible context).extend region).sigs
      (context.extend region).sigs :=
  fun {_} value =>
    contextSection source left right eligible (context.extend region)
      (congrArg ConcreteElaboration.WireContext.sigs
        (targetContext_extend source left right eligible
          context region).symm ▸ value)

private theorem extendedContextSection_origin
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    {sig : Sig}
    (value :
      Var
        ((targetContext source left right eligible context).extend region).sigs
        sig) :
    targetWire source
        (ConcreteElaboration.WireContext.origin source.val
          (context.extend region).ids
          (extendedContextSection source left right eligible
            context region value)) =
      ConcreteElaboration.WireContext.origin
        (Target source left right eligible)
        ((targetContext source left right eligible context).extend region).ids
        value := by
  unfold extendedContextSection
  rw [contextSection_origin, targetWire_sourceWire]
  exact origin_context_cast
    (Target source left right eligible)
    ((targetContext source left right eligible context).extend region)
    (targetContext source left right eligible (context.extend region))
    (targetContext_extend source left right eligible context region).symm
    value

private theorem extendedContextRenaming_section
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (targetExtendedNodup :
      ((targetContext source left right eligible context).extend
        region).ids.Nodup)
    {sig : Sig}
    (value :
      Var
        ((targetContext source left right eligible context).extend region).sigs
        sig) :
    extendedContextRenaming source left right eligible context region
        (extendedContextSection source left right eligible
          context region value) =
      value := by
  apply origin_injective
    (Target source left right eligible)
    ((targetContext source left right eligible context).extend region).ids
    targetExtendedNodup
  rw [extendedContextRenaming_origin,
    extendedContextSection_origin]

private theorem extendedContextSection_renaming
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    {sig : Sig}
    (value : Var (context.extend region).sigs sig) :
    extendedContextSection source left right eligible context region
        (extendedContextRenaming source left right eligible
          context region value) =
      value := by
  apply origin_injective source.val
    (context.extend region).ids sourceExtendedNodup
  apply targetWire_injective source
  rw [extendedContextSection_origin,
    extendedContextRenaming_origin]

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

private theorem extendedContextSection_appendRight
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    {sig : Sig}
    (value :
      Var (targetContext source left right eligible context).sigs sig) :
    extendedContextSection source left right eligible context region
        (ConcreteElaboration.appendRightVar
          (Target source left right eligible)
          ((Target source left right eligible).wiresAt region) value) =
      ConcreteElaboration.appendRightVar source.val
        (source.val.wiresAt region)
        (contextSection source left right eligible context value) := by
  apply origin_injective source.val
    (context.extend region).ids sourceExtendedNodup
  apply targetWire_injective source
  rw [extendedContextSection_origin]
  simp only [ConcreteElaboration.WireContext.extend]
  rw [origin_appendRightVar, origin_appendRightVar,
    contextSection_origin, targetWire_sourceWire]

private theorem extendedEnvironment_natural
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (pre : PreModel)
    (targetValues :
      ConcreteElaboration.WireValues pre
        (((Target source left right eligible).wiresAt region).map
          fun wire =>
            ((Target source left right eligible).wires wire).sig))
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs) :
    let targetExtended :=
      ConcreteElaboration.extendEnvironment
        (Target source left right eligible)
        (targetContext source left right eligible context) region
        targetValues targetEnv
    let sourceEnv :=
      Env.comp targetExtended
        (extendedContextRenaming source left right eligible context region)
    ConcreteElaboration.extendEnvironment source.val context region
        (ConcreteElaboration.valuesFromEnvironmentFor source.val context.ids
          (source.val.wiresAt region) sourceEnv)
        (Env.comp targetEnv
          (contextRenaming source left right eligible context)) =
      sourceEnv := by
  simp only
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig outer
  let sourceOuter :=
    ConcreteElaboration.appendRightVar
      source.val (source.val.wiresAt region) outer
  let targetOuter :=
    ConcreteElaboration.appendRightVar
      (Target source left right eligible)
      ((Target source left right eligible).wiresAt region)
      (contextRenaming source left right eligible context outer)
  have targetExtendedNodup :
      ((targetContext source left right eligible context).extend
        region).ids.Nodup := by
    have mapped :=
      targetContext_nodup source left right eligible
        (context.extend region) sourceExtendedNodup
    simpa [targetContext_extend source left right eligible context region]
      using mapped
  have sameOrigin :
      ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          ((targetContext source left right eligible context).extend
            region).ids
          (extendedContextRenaming source left right eligible
            context region sourceOuter) =
        ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          ((targetContext source left right eligible context).extend
            region).ids
          targetOuter := by
    dsimp [sourceOuter, targetOuter]
    rw [extendedContextRenaming_origin]
    simp only [ConcreteElaboration.WireContext.extend]
    rw [origin_appendRightVar, origin_appendRightVar,
      contextRenaming_origin]
  have sameVar :=
    origin_injective
      (Target source left right eligible)
      ((targetContext source left right eligible context).extend region).ids
      targetExtendedNodup sameOrigin
  change
    ConcreteElaboration.extendEnvironment
        (Target source left right eligible)
        (targetContext source left right eligible context) region
        targetValues targetEnv sig
        (extendedContextRenaming source left right eligible
          context region sourceOuter) =
      targetEnv sig
        (contextRenaming source left right eligible context outer)
  rw [sameVar]
  exact ConcreteElaboration.extendEnvironment_appendRightVar
    (Target source left right eligible)
    (targetContext source left right eligible context) region
    targetValues targetEnv
    (contextRenaming source left right eligible context outer)

private theorem reverseExtendedEnvironment_natural
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (targetNodup :
      (targetContext source left right eligible context).ids.Nodup)
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((source.val.wiresAt region).map fun wire =>
          (source.val.wires wire).sig))
    (sourceEnv : Env pre context.sigs)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (outerRelated :
      sourceEnv =
        Env.comp targetEnv
          (contextRenaming source left right eligible context)) :
    let sourceExtended :=
      ConcreteElaboration.extendEnvironment source.val context region
        sourceValues sourceEnv
    let targetExtended :=
      Env.comp sourceExtended
        (extendedContextSection source left right eligible context region)
    ConcreteElaboration.extendEnvironment
        (Target source left right eligible)
        (targetContext source left right eligible context) region
        (ConcreteElaboration.valuesFromEnvironmentFor
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          ((Target source left right eligible).wiresAt region)
          targetExtended)
        targetEnv =
      targetExtended := by
  simp only
  apply ConcreteElaboration.extendEnvironmentFor_from
  intro sig value
  change
    ConcreteElaboration.extendEnvironment source.val context region
        sourceValues sourceEnv sig
        (extendedContextSection source left right eligible context region
          (ConcreteElaboration.appendRightVar
            (Target source left right eligible)
            ((Target source left right eligible).wiresAt region) value)) =
      targetEnv sig value
  rw [extendedContextSection_appendRight source left right eligible
      context region sourceExtendedNodup,
    ConcreteElaboration.extendEnvironment_appendRightVar,
    outerRelated]
  change
    targetEnv sig
        (contextRenaming source left right eligible context
          (contextSection source left right eligible context value)) =
      targetEnv sig value
  rw [contextRenaming_section source left right eligible
    context targetNodup]

private theorem ordinary_singleton_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (node : source.val.NodeId)
    (notLeft : node ≠ left)
    (notRight : node ≠ right)
    (sourceItems : ItemSeq definitions context.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [node] = some sourceItems)
    (targetItems :
      ItemSeq definitions
        (targetContext source left right eligible context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          [targetNode source right node notRight] = some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source left right eligible context))
        sourceItems := by
  obtain ⟨expected, expectedCompiled, expectedEquation⟩ :=
    compile_ordinary_singleton source left right eligible context
      contextNodup node notLeft notRight sourceCompiled
  have itemEquality : targetItems = expected :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  subst targetItems
  rw [expectedEquation,
    denoteItemSeq_renameWires]

abbrev incidentUnion
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId) :
    List source.val.WireId :=
  (source.val.identityIncidentWires left ++
    source.val.identityIncidentWires right).eraseDups

abbrev fusedNode
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (Target source left right eligible).NodeId :=
  targetNode source right left eligible.distinct

@[simp] private theorem sourceNode_fusedNode
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    sourceNode source right (fusedNode source left right eligible) = left :=
  fusionNodes_get_targetNode source right left eligible.distinct

theorem target_identity_incident_iff
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (wire : source.val.WireId) :
    targetWire source wire ∈
        (Target source left right eligible).identityIncidentWires
          (fusedNode source left right eligible) ↔
      wire ∈ incidentUnion source left right := by
  constructor
  · intro targetIncident
    obtain ⟨endpoint, endpointMember, endpointNode⟩ :=
      (mem_identityIncidentWires
        (Target source left right eligible)
        (fusedNode source left right eligible)
        (targetWire source wire)).mp targetIncident
    simp only [fusionCandidate] at endpointMember
    have wireEquality :
        source.val.wiresList.get (targetWire source wire) = wire :=
      sourceWire_targetWire source wire
    rw [wireEquality] at endpointMember
    rcases List.mem_append.mp endpointMember with retained | generated
    · rcases List.mem_filterMap.mp retained with
        ⟨sourceEndpoint, filtered, mapped⟩
      have sourceDifferent :
          sourceEndpoint.node ≠ left ∧ sourceEndpoint.node ≠ right :=
        of_decide_eq_true (List.mem_filter.mp filtered).2
      unfold reindexEndpoint? at mapped
      cases found :
          Data.Finite.indexOf? (fusionNodes source right)
            sourceEndpoint.node with
      | none => simp [found] at mapped
      | some target =>
          have endpointEquality :
              (⟨target, sourceEndpoint.port⟩ :
                CEndpoint (fusionNodes source right).length) = endpoint :=
            Option.some.inj (by simpa [found] using mapped)
          have targetEquality :
              target = fusedNode source left right eligible := by
            exact (congrArg CEndpoint.node endpointEquality).trans
              endpointNode
          have indexed := Data.Finite.indexOf?_sound found
          have sourceNodeEquality : sourceEndpoint.node = left := by
            rw [← sourceNode_fusedNode source left right eligible,
              ← targetEquality]
            exact indexed.symm
          exact False.elim (sourceDifferent.1 sourceNodeEquality)
    · cases leftFound :
          Data.Finite.indexOf? (fusionNodes source right) left with
      | none => simp [leftFound] at generated
      | some target =>
          cases wireFound :
              Data.Finite.indexOf? (incidentUnion source left right) wire with
          | none => simp [leftFound, wireFound] at generated
          | some index =>
              have indexed := Data.Finite.indexOf?_sound wireFound
              rw [← indexed]
              exact List.get_mem _ index
  · intro incident
    have leftMember : left ∈ fusionNodes source right := by
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin left, by simp [eligible.distinct]⟩
    obtain ⟨leftIndex, leftFound⟩ :=
      Data.Finite.indexOf?_complete leftMember
    obtain ⟨wireIndex, wireFound⟩ :=
      Data.Finite.indexOf?_complete incident
    have leftIndexEq :
        leftIndex = fusedNode source left right eligible := by
      apply Fin.ext
      have nodeValuesEqual :
          (fusionNodes source right).get leftIndex =
            (fusionNodes source right).get
              (fusedNode source left right eligible) :=
        (Data.Finite.indexOf?_sound leftFound).trans
          (sourceNode_fusedNode source left right eligible).symm
      exact
        (List.getElem_inj
          ((Data.Finite.allFin_nodup source.val.nodeCount).filter _)).mp
          nodeValuesEqual
    let endpoint :
        CEndpoint (Target source left right eligible).nodeCount :=
      ⟨leftIndex, .identity wireIndex.val⟩
    apply
      (mem_identityIncidentWires
        (Target source left right eligible)
        (fusedNode source left right eligible)
        (targetWire source wire)).mpr
    refine ⟨endpoint, ?_, leftIndexEq⟩
    simp only [fusionCandidate]
    have wireEquality :
        source.val.wiresList.get (targetWire source wire) = wire :=
      sourceWire_targetWire source wire
    rw [wireEquality]
    apply List.mem_append.mpr
    apply Or.inr
    rw [leftFound, wireFound]
    apply List.mem_singleton.mpr
    cases leftIndex
    rfl

private theorem fusion_signature_eq
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    eligible.rightIdentity.signature =
      eligible.leftIdentity.signature := by
  obtain ⟨pivot, leftIncident, rightIncident⟩ := eligible.shared
  exact
    (identityIncidentWire_signature definitions source.val source.property
      eligible.rightIdentity.node_eq pivot rightIncident).symm.trans
      (identityIncidentWire_signature definitions source.val source.property
        eligible.leftIdentity.node_eq pivot leftIncident)

theorem target_node_fused
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (Target source left right eligible).nodes
        (fusedNode source left right eligible) =
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (incidentUnion source left right).length := by
  change
    (if
      (fusionNodes source right).get
          (fusedNode source left right eligible) = left
    then
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (incidentUnion source left right).length
    else
      source.val.nodes
        ((fusionNodes source right).get
          (fusedNode source left right eligible))) =
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (incidentUnion source left right).length
  change
    (if
      (fusionNodes source right).get
          (targetNode source right left eligible.distinct) = left
    then
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (incidentUnion source left right).length
    else
      source.val.nodes
        ((fusionNodes source right).get
          (targetNode source right left eligible.distinct))) =
      .identity eligible.leftIdentity.region
        eligible.leftIdentity.signature
        (incidentUnion source left right).length
  rw [fusionNodes_get_targetNode]
  simp

private theorem fused_singleton_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (leftItems rightItems : ItemSeq definitions context.sigs)
    (leftCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [left] = some leftItems)
    (rightCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [right] = some rightItems)
    (targetItems :
      ItemSeq definitions
        (targetContext source left right eligible context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          [fusedNode source left right eligible] = some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          leftItems ∧
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          rightItems := by
  obtain ⟨leftPorts, leftTwo, leftItemsEquation, leftOrigins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      source.val source.property context left
      eligible.leftIdentity.node_eq leftCompiled
  have rightNodeData :
      source.val.nodes right =
        .identity eligible.rightIdentity.region
          eligible.leftIdentity.signature eligible.rightIdentity.arity := by
    rw [← fusion_signature_eq source left right eligible]
    exact eligible.rightIdentity.node_eq
  obtain ⟨rightPorts, rightTwo, rightItemsEquation, rightOrigins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      source.val source.property context right
      rightNodeData rightCompiled
  have targetNodup :
      (targetContext source left right eligible context).ids.Nodup :=
    targetContext_nodup source left right eligible context contextNodup
  obtain ⟨targetPorts, targetTwo, targetItemsEquation, targetOrigins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins
      (Target source left right eligible)
      (fusionCandidate_wellFormed source left right eligible)
      (targetContext source left right eligible context)
      (fusedNode source left right eligible)
      (target_node_fused source left right eligible)
      targetCompiled
  rw [leftItemsEquation, rightItemsEquation, targetItemsEquation]
  simp only [denoteItemSeq_cons, denoteItem_identity,
    denoteItemSeq_nil, and_true]
  let rho :
      WireRenaming context.sigs
        (targetContext source left right eligible context).sigs :=
    contextRenaming source left right eligible context
  have portMembers :
      ∀ targetVar :
          Var
            (targetContext source left right eligible context).sigs
            eligible.leftIdentity.signature,
        targetVar ∈ targetPorts ↔
          ∃ sourceVar : Var context.sigs eligible.leftIdentity.signature,
            (sourceVar ∈ leftPorts ∨ sourceVar ∈ rightPorts) ∧
              rho sourceVar = targetVar := by
    intro targetVar
    constructor
    · intro targetMember
      let targetOrigin :=
        ConcreteElaboration.WireContext.origin
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          targetVar
      have targetIncident :
          targetOrigin ∈
            (Target source left right eligible).identityIncidentWires
              (fusedNode source left right eligible) :=
        (targetOrigins targetOrigin).mpr
          ⟨targetVar, targetMember, rfl⟩
      let sourceOrigin := sourceWire source targetOrigin
      have sourceIncident :
          sourceOrigin ∈ incidentUnion source left right := by
        apply
          (target_identity_incident_iff
            source left right eligible sourceOrigin).mp
        change
          targetWire source (sourceWire source targetOrigin) ∈
            (Target source left right eligible).identityIncidentWires
              (fusedNode source left right eligible)
        rw [targetWire_sourceWire]
        exact targetIncident
      have sourceSide :
          sourceOrigin ∈ source.val.identityIncidentWires left ∨
            sourceOrigin ∈ source.val.identityIncidentWires right := by
        simpa [incidentUnion] using sourceIncident
      rcases sourceSide with leftIncident | rightIncident
      · obtain ⟨sourceVar, sourceMember, sourceVarOrigin⟩ :=
          (leftOrigins sourceOrigin).mp leftIncident
        refine ⟨sourceVar, Or.inl sourceMember, ?_⟩
        apply origin_injective
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          targetNodup
        rw [contextRenaming_origin, sourceVarOrigin]
        exact targetWire_sourceWire source targetOrigin
      · obtain ⟨sourceVar, sourceMember, sourceVarOrigin⟩ :=
          (rightOrigins sourceOrigin).mp rightIncident
        refine ⟨sourceVar, Or.inr sourceMember, ?_⟩
        apply origin_injective
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          targetNodup
        rw [contextRenaming_origin, sourceVarOrigin]
        exact targetWire_sourceWire source targetOrigin
    · rintro ⟨sourceVar, sourceMember, targetVarEquation⟩
      let sourceOrigin :=
        ConcreteElaboration.WireContext.origin
          source.val context.ids sourceVar
      have sourceIncident :
          sourceOrigin ∈ incidentUnion source left right := by
        apply List.mem_eraseDups.mpr
        apply List.mem_append.mpr
        rcases sourceMember with leftMember | rightMember
        · exact Or.inl
            ((leftOrigins sourceOrigin).mpr
              ⟨sourceVar, leftMember, rfl⟩)
        · exact Or.inr
            ((rightOrigins sourceOrigin).mpr
              ⟨sourceVar, rightMember, rfl⟩)
      have targetIncident :=
        (target_identity_incident_iff
          source left right eligible sourceOrigin).mpr sourceIncident
      obtain ⟨actualTargetVar, actualTargetMember, actualTargetOrigin⟩ :=
        (targetOrigins (targetWire source sourceOrigin)).mp targetIncident
      have actualTargetEquation :
          rho sourceVar = actualTargetVar := by
        apply origin_injective
          (Target source left right eligible)
          (targetContext source left right eligible context).ids
          targetNodup
        rw [contextRenaming_origin]
        exact actualTargetOrigin.symm
      rw [← targetVarEquation, actualTargetEquation]
      exact actualTargetMember
  have valueMembers :
      ∀ value : pre.Domain eligible.leftIdentity.signature,
        value ∈ targetPorts.map (targetEnv eligible.leftIdentity.signature) ↔
          value ∈
            leftPorts.map
                ((Env.comp targetEnv rho)
                  eligible.leftIdentity.signature) ++
              rightPorts.map
                ((Env.comp targetEnv rho)
                  eligible.leftIdentity.signature) := by
    intro value
    constructor
    · intro targetMember
      rcases List.mem_map.mp targetMember with
        ⟨targetVar, targetVarMember, targetValue⟩
      obtain ⟨sourceVar, sourceMember, sourceVarEquation⟩ :=
        (portMembers targetVar).mp targetVarMember
      apply List.mem_append.mpr
      rcases sourceMember with leftMember | rightMember
      · apply Or.inl
        apply List.mem_map.mpr
        refine ⟨sourceVar, leftMember, ?_⟩
        simpa [Env.comp, rho, ← sourceVarEquation] using targetValue
      · apply Or.inr
        apply List.mem_map.mpr
        refine ⟨sourceVar, rightMember, ?_⟩
        simpa [Env.comp, rho, ← sourceVarEquation] using targetValue
    · intro sourceMember
      rcases List.mem_append.mp sourceMember with leftMember | rightMember
      · rcases List.mem_map.mp leftMember with
          ⟨sourceVar, sourceVarMember, sourceValue⟩
        have targetVarMember :
            rho sourceVar ∈ targetPorts :=
          (portMembers (rho sourceVar)).mpr
            ⟨sourceVar, Or.inl sourceVarMember, rfl⟩
        exact List.mem_map.mpr
          ⟨rho sourceVar, targetVarMember, by
            simpa [Env.comp, rho] using sourceValue⟩
      · rcases List.mem_map.mp rightMember with
          ⟨sourceVar, sourceVarMember, sourceValue⟩
        have targetVarMember :
            rho sourceVar ∈ targetPorts :=
          (portMembers (rho sourceVar)).mpr
            ⟨sourceVar, Or.inr sourceVarMember, rfl⟩
        exact List.mem_map.mpr
          ⟨rho sourceVar, targetVarMember, by
            simpa [Env.comp, rho] using sourceValue⟩
  have equalIff :=
    AllEqual.iff_of_mem_iff valueMembers
  constructor
  · intro targetEqual
    have combinedEqual := equalIff.mp targetEqual
    constructor
    · intro first firstMember second secondMember
      exact combinedEqual first (List.mem_append_left _ firstMember)
        second (List.mem_append_left _ secondMember)
    · intro first firstMember second secondMember
      exact combinedEqual first (List.mem_append_right _ firstMember)
        second (List.mem_append_right _ secondMember)
  · rintro ⟨leftEqual, rightEqual⟩
    obtain ⟨pivot, pivotLeft, pivotRight⟩ := eligible.shared
    obtain ⟨leftPivotVar, leftPivotMember, leftPivotOrigin⟩ :=
      (leftOrigins pivot).mp pivotLeft
    obtain ⟨rightPivotVar, rightPivotMember, rightPivotOrigin⟩ :=
      (rightOrigins pivot).mp pivotRight
    have pivotVarEquality :
        rho leftPivotVar = rho rightPivotVar := by
      apply origin_injective
        (Target source left right eligible)
        (targetContext source left right eligible context).ids
        targetNodup
      rw [contextRenaming_origin, contextRenaming_origin,
        leftPivotOrigin, rightPivotOrigin]
    apply equalIff.mpr
    apply AllEqual.union leftEqual rightEqual
    · exact List.mem_map.mpr ⟨leftPivotVar, leftPivotMember, rfl⟩
    · apply List.mem_map.mpr
      refine ⟨rightPivotVar, rightPivotMember, ?_⟩
      exact congrArg
        (targetEnv eligible.leftIdentity.signature)
        pivotVarEquality |>.symm

private theorem ordinary_item_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (node : source.val.NodeId)
    (notLeft : node ≠ left)
    (notRight : node ≠ right)
    (sourceItem : Item definitions context.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [node] = some (.cons sourceItem .nil))
    (targetItem :
      Item definitions
        (targetContext source left right eligible context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          [targetNode source right node notRight] =
        some (.cons targetItem .nil)) :
    denoteItem pre definitionEnv targetEnv targetItem ↔
      denoteItem pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source left right eligible context))
        sourceItem := by
  simpa using
    ordinary_singleton_denotation source left right eligible context
      contextNodup pre definitionEnv targetEnv node notLeft notRight
      (.cons sourceItem .nil) sourceCompiled
      (.cons targetItem .nil) targetCompiled

private theorem fused_item_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (leftItem rightItem : Item definitions context.sigs)
    (leftCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [left] = some (.cons leftItem .nil))
    (rightCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          [right] = some (.cons rightItem .nil))
    (targetItem :
      Item definitions
        (targetContext source left right eligible context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          [fusedNode source left right eligible] =
        some (.cons targetItem .nil)) :
    denoteItem pre definitionEnv targetEnv targetItem ↔
      denoteItem pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          leftItem ∧
        denoteItem pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          rightItem := by
  simpa using
    fused_singleton_denotation source left right eligible context
      contextNodup pre definitionEnv targetEnv
      (.cons leftItem .nil) (.cons rightItem .nil)
      leftCompiled rightCompiled
      (.cons targetItem .nil) targetCompiled

private theorem target_node_region
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (node : source.val.NodeId)
    (notRight : node ≠ right) :
    ((Target source left right eligible).nodes
      (targetNode source right node notRight)).region =
        (source.val.nodes node).region := by
  by_cases nodeLeft : node = left
  · subst node
    rw [target_node_fused, eligible.leftIdentity.node_eq]
    rfl
  · rw [target_node_of_not_left source left right eligible
      node nodeLeft notRight]
    rfl

private theorem targetNode_mem_nodesAt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : source.val.RegionId)
    (node : source.val.NodeId)
    (notRight : node ≠ right)
    (member : node ∈ source.val.nodesAt region) :
    targetNode source right node notRight ∈
      (Target source left right eligible).nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  have sourceRegion := (List.mem_filter.mp member).2
  have sameRegion :=
    target_node_region source left right eligible node notRight
  rw [sameRegion]
  exact sourceRegion

private theorem sourceNode_mem_nodesAt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : source.val.RegionId)
    (node : (Target source left right eligible).NodeId)
    (member :
      node ∈ (Target source left right eligible).nodesAt region) :
    sourceNode source right node ∈ source.val.nodesAt region := by
  let original := sourceNode source right node
  have survives : original ≠ right :=
    sourceNode_ne_right source right node
  have targetEquation :
      targetNode source right original survives = node :=
    targetNode_sourceNode source right node
  have regionEquation :=
    target_node_region source left right eligible original survives
  rw [targetEquation] at regionEquation
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList at member ⊢
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  have targetRegion := (List.mem_filter.mp member).2
  rw [← regionEquation]
  exact targetRegion

private theorem paired_identity_member
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : source.val.RegionId) :
    left ∈ source.val.nodesAt region ↔
      right ∈ source.val.nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  simp only [List.mem_filter, Data.Finite.mem_allFin, true_and]
  rw [eligible.leftIdentity.node_eq,
    eligible.rightIdentity.node_eq]
  simp only [CNode.region, beq_iff_eq]
  change
    eligible.leftIdentity.region = region ↔
      eligible.rightIdentity.region = region
  rw [eligible.sameRegion]

private theorem target_childrenOf
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (region : source.val.RegionId) :
    (Target source left right eligible).childrenOf region =
      source.val.childrenOf region := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  apply List.filter_congr
  intro child _
  simp only [fusionCandidate]
  cases source.val.regions child <;> rfl

private theorem compiled_children_under_pullback
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (sourceRecurse :
      (region : source.val.RegionId) →
        (context : ConcreteElaboration.WireContext source.val) →
          Option (Region definitions context.sigs))
    (targetRecurse :
      (region : (Target source left right eligible).RegionId) →
        (context :
          ConcreteElaboration.WireContext
            (Target source left right eligible)) →
          Option (Region definitions context.sigs)) :
    ∀ (children : List source.val.RegionId)
      (_recurseDenotation :
        ∀ child, child ∈ children → ∀ sourceBody targetBody,
          sourceRecurse child context = some sourceBody →
          targetRecurse child
              (targetContext source left right eligible context) =
            some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (contextRenaming source left right eligible context))
              sourceBody))
      (sourceItems : ItemSeq definitions context.sigs)
      (_sourceCompiled :
        ConcreteElaboration.compileChildrenWith? definitions source.val
            sourceRecurse context children = some sourceItems)
      (targetItems :
        ItemSeq definitions
          (targetContext source left right eligible context).sigs)
      (_targetCompiled :
        ConcreteElaboration.compileChildrenWith? definitions
            (Target source left right eligible) targetRecurse
            (targetContext source left right eligible context) children =
          some targetItems),
      denoteItemSeq pre definitionEnv targetEnv targetItems ↔
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          sourceItems
  | [], recurseDenotation, sourceItems, sourceCompiled,
      targetItems, targetCompiled => by
      have sourceEmpty : sourceItems = .nil :=
        (Option.some.inj (by
          simpa [ConcreteElaboration.compileChildrenWith?] using
            sourceCompiled)).symm
      have targetEmpty : targetItems = .nil :=
        (Option.some.inj (by
          simpa [ConcreteElaboration.compileChildrenWith?] using
            targetCompiled)).symm
      subst sourceItems
      subst targetItems
      rfl
  | child :: tail, recurseDenotation, sourceItems, sourceCompiled,
      targetItems, targetCompiled => by
      simp only [ConcreteElaboration.compileChildrenWith?] at sourceCompiled targetCompiled
      obtain ⟨sourceBody, sourceRest, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsEquation⟩ :=
        option_bind₂_eq_some sourceCompiled
      obtain ⟨targetBody, targetRest, targetHeadCompiled,
          targetTailCompiled, targetItemsEquation⟩ :=
        option_bind₂_eq_some targetCompiled
      subst sourceItems
      subst targetItems
      simp only [denoteItemSeq_cons, denoteItem]
      exact and_congr
        (not_congr
          (recurseDenotation child (by simp) sourceBody targetBody
            sourceHeadCompiled targetHeadCompiled))
        (compiled_children_under_pullback source left right eligible context
          pre definitionEnv targetEnv sourceRecurse targetRecurse tail
          (fun candidate member =>
            recurseDenotation candidate (by simp [member]))
          sourceRest sourceTailCompiled
          targetRest targetTailCompiled)

private theorem compiled_nodes_under_pullback
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre (targetContext source left right eligible context).sigs)
    (region : source.val.RegionId)
    (sourceItems : ItemSeq definitions context.sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (source.val.nodesAt region) = some sourceItems)
    (targetItems :
      ItemSeq definitions
        (targetContext source left right eligible context).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          (targetContext source left right eligible context)
          ((Target source left right eligible).nodesAt region) =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (contextRenaming source left right eligible context))
        sourceItems := by
  rw [denote_compileNodes_iff_singletons definitions
      (Target source left right eligible)
      (targetContext source left right eligible context)
      pre definitionEnv targetEnv _ _ targetCompiled,
    denote_compileNodes_iff_singletons definitions source.val context
      pre definitionEnv
      (Env.comp targetEnv
        (contextRenaming source left right eligible context))
      _ _ sourceCompiled]
  constructor
  · intro targetDenotes sourceNode sourceMember
    by_cases sourceLeft : sourceNode = left
    · subst sourceNode
      obtain ⟨leftItem, leftCompiled⟩ :=
        compileNodes_singleton_of_member definitions source.val context
          (source.val.nodesAt region) sourceItems sourceCompiled left
          sourceMember
      have rightMember :=
        (paired_identity_member source left right eligible region).mp
          sourceMember
      obtain ⟨rightItem, rightCompiled⟩ :=
        compileNodes_singleton_of_member definitions source.val context
          (source.val.nodesAt region) sourceItems sourceCompiled right
          rightMember
      obtain ⟨targetItem, targetItemCompiled, targetItemDenotes⟩ :=
        targetDenotes
          (fusedNode source left right eligible)
          (targetNode_mem_nodesAt source left right eligible region left
            eligible.distinct sourceMember)
      exact ⟨leftItem, leftCompiled,
        (fused_item_denotation source left right eligible context
          contextNodup pre definitionEnv targetEnv leftItem rightItem
          leftCompiled rightCompiled targetItem targetItemCompiled).mp
          targetItemDenotes |>.1⟩
    · by_cases sourceRight : sourceNode = right
      · subst sourceNode
        obtain ⟨rightItem, rightCompiled⟩ :=
          compileNodes_singleton_of_member definitions source.val context
            (source.val.nodesAt region) sourceItems sourceCompiled right
            sourceMember
        have leftMember :=
          (paired_identity_member source left right eligible region).mpr
            sourceMember
        obtain ⟨leftItem, leftCompiled⟩ :=
          compileNodes_singleton_of_member definitions source.val context
            (source.val.nodesAt region) sourceItems sourceCompiled left
            leftMember
        obtain ⟨targetItem, targetItemCompiled, targetItemDenotes⟩ :=
          targetDenotes
            (fusedNode source left right eligible)
            (targetNode_mem_nodesAt source left right eligible region left
              eligible.distinct leftMember)
        exact ⟨rightItem, rightCompiled,
          (fused_item_denotation source left right eligible context
            contextNodup pre definitionEnv targetEnv leftItem rightItem
            leftCompiled rightCompiled targetItem targetItemCompiled).mp
            targetItemDenotes |>.2⟩
      · obtain ⟨sourceItem, sourceItemCompiled⟩ :=
          compileNodes_singleton_of_member definitions source.val context
            (source.val.nodesAt region) sourceItems sourceCompiled sourceNode
            sourceMember
        obtain ⟨targetItem, targetItemCompiled, targetItemDenotes⟩ :=
          targetDenotes
            (targetNode source right sourceNode sourceRight)
            (targetNode_mem_nodesAt source left right eligible region
              sourceNode sourceRight sourceMember)
        exact ⟨sourceItem, sourceItemCompiled,
          (ordinary_item_denotation source left right eligible context
            contextNodup pre definitionEnv targetEnv sourceNode sourceLeft
            sourceRight sourceItem sourceItemCompiled targetItem
            targetItemCompiled).mp targetItemDenotes⟩
  · intro sourceDenotes target targetMember
    let original := sourceNode source right target
    have survives : original ≠ right :=
      sourceNode_ne_right source right target
    have originalMember :=
      sourceNode_mem_nodesAt source left right eligible region target
        targetMember
    have targetEquation :
        targetNode source right original survives = target :=
      targetNode_sourceNode source right target
    obtain ⟨targetItem, targetItemCompiled⟩ :=
      compileNodes_singleton_of_member definitions
        (Target source left right eligible)
        (targetContext source left right eligible context)
        ((Target source left right eligible).nodesAt region) targetItems
        targetCompiled target targetMember
    by_cases originalLeft : original = left
    · change original ∈ source.val.nodesAt region at originalMember
      rw [originalLeft] at originalMember
      obtain ⟨leftItem, leftItemCompiled, leftItemDenotes⟩ :=
        sourceDenotes left originalMember
      have rightMember :=
        (paired_identity_member source left right eligible region).mp
          originalMember
      obtain ⟨rightItem, rightItemCompiled, rightItemDenotes⟩ :=
        sourceDenotes right rightMember
      have targetItemCompiled' :
          ConcreteElaboration.compileNodes? definitions
              (Target source left right eligible)
              (targetContext source left right eligible context)
              [fusedNode source left right eligible] =
            some (.cons targetItem .nil) := by
        have fusedEquation :
            fusedNode source left right eligible = target := by
          simpa [fusedNode, original, originalLeft] using targetEquation
        rw [fusedEquation]
        exact targetItemCompiled
      exact ⟨targetItem, targetItemCompiled,
        (fused_item_denotation source left right eligible context
          contextNodup pre definitionEnv targetEnv leftItem rightItem
          leftItemCompiled rightItemCompiled targetItem
          targetItemCompiled').mpr ⟨leftItemDenotes, rightItemDenotes⟩⟩
    · obtain ⟨sourceItem, sourceItemCompiled, sourceItemDenotes⟩ :=
        sourceDenotes original originalMember
      have targetItemCompiled' :
          ConcreteElaboration.compileNodes? definitions
              (Target source left right eligible)
              (targetContext source left right eligible context)
              [targetNode source right original survives] =
            some (.cons targetItem .nil) := by
        rw [targetEquation]
        exact targetItemCompiled
      exact ⟨targetItem, targetItemCompiled,
        (ordinary_item_denotation source left right eligible context
          contextNodup pre definitionEnv targetEnv original originalLeft
          survives sourceItem sourceItemCompiled targetItem
          targetItemCompiled').mpr sourceItemDenotes⟩

private theorem compiled_nodes_extended
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (sourceExtendedNodup : (context.extend region).ids.Nodup)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source left right eligible context).extend
          region).sigs)
    (sourceItems : ItemSeq definitions (context.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetItems :
      ItemSeq definitions
        ((targetContext source left right eligible context).extend
          region).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions
          (Target source left right eligible)
          ((targetContext source left right eligible context).extend region)
          ((Target source left right eligible).nodesAt region) =
        some targetItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source left right eligible context region))
        sourceItems := by
  let exactContext :=
    targetContext source left right eligible (context.extend region)
  let actualContext :=
    (targetContext source left right eligible context).extend region
  have same : exactContext = actualContext :=
    targetContext_extend source left right eligible context region
  let P : ConcreteElaboration.WireContext
      (Target source left right eligible) → Prop :=
    fun targetCtx =>
      ∀ (alignment : exactContext = targetCtx)
        (env : Env pre targetCtx.sigs)
        (items : ItemSeq definitions targetCtx.sigs),
        ConcreteElaboration.compileNodes? definitions
            (Target source left right eligible) targetCtx
            ((Target source left right eligible).nodesAt region) =
          some items →
        (denoteItemSeq pre definitionEnv env items ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (fun {_} value =>
                congrArg ConcreteElaboration.WireContext.sigs alignment ▸
                  contextRenaming source left right eligible
                    (context.extend region) value))
            sourceItems)
  have exactProof : P exactContext := by
    intro alignment env items compiled
    have alignmentProof : alignment = rfl := Subsingleton.elim _ _
    rw [alignmentProof]
    exact compiled_nodes_under_pullback source left right eligible
      (context.extend region) sourceExtendedNodup pre definitionEnv
      env region sourceItems sourceCompiled items compiled
  have actualProof : P actualContext :=
    Eq.mp (congrArg P same) exactProof
  exact actualProof same targetEnv targetItems targetCompiled

private theorem compiled_children_extended
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source left right eligible context).extend
          region).sigs)
    (sourceRecurse :
      (child : source.val.RegionId) →
        (childContext :
          ConcreteElaboration.WireContext source.val) →
          Option (Region definitions childContext.sigs))
    (targetRecurse :
      (child : (Target source left right eligible).RegionId) →
        (childContext :
          ConcreteElaboration.WireContext
            (Target source left right eligible)) →
          Option (Region definitions childContext.sigs))
    (children : List source.val.RegionId)
    (sourceItems : ItemSeq definitions (context.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions source.val
          sourceRecurse (context.extend region) children =
        some sourceItems)
    (targetItems :
      ItemSeq definitions
        ((targetContext source left right eligible context).extend
          region).sigs)
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions
          (Target source left right eligible) targetRecurse
          ((targetContext source left right eligible context).extend region)
          children = some targetItems)
    (recurseDenotation :
      ∀ child, child ∈ children → ∀ sourceBody targetBody,
        sourceRecurse child (context.extend region) = some sourceBody →
        targetRecurse child
            ((targetContext source left right eligible context).extend
              region) =
          some targetBody →
        (denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv
              (extendedContextRenaming source left right eligible
                context region))
            sourceBody)) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source left right eligible context region))
        sourceItems := by
  let sourceContext := context.extend region
  let exactContext :=
    targetContext source left right eligible sourceContext
  let actualContext :=
    (targetContext source left right eligible context).extend region
  have same : exactContext = actualContext :=
    targetContext_extend source left right eligible context region
  let P : ConcreteElaboration.WireContext
      (Target source left right eligible) → Prop :=
    fun targetCtx =>
      ∀ (alignment : exactContext = targetCtx)
        (env : Env pre targetCtx.sigs)
        (items : ItemSeq definitions targetCtx.sigs),
        ConcreteElaboration.compileChildrenWith? definitions
            (Target source left right eligible) targetRecurse targetCtx
            children = some items →
        (∀ child, child ∈ children → ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse child targetCtx = some targetBody →
          (denoteRegion pre definitionEnv env targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp env
                (fun {_} value =>
                  congrArg ConcreteElaboration.WireContext.sigs alignment ▸
                    contextRenaming source left right eligible
                      sourceContext value))
              sourceBody)) →
        (denoteItemSeq pre definitionEnv env items ↔
          denoteItemSeq pre definitionEnv
            (Env.comp env
              (fun {_} value =>
                congrArg ConcreteElaboration.WireContext.sigs alignment ▸
                  contextRenaming source left right eligible
                    sourceContext value))
            sourceItems)
  have exactProof : P exactContext := by
    intro alignment env items compiled recurse
    have alignmentProof : alignment = rfl := Subsingleton.elim _ _
    rw [alignmentProof] at recurse ⊢
    exact compiled_children_under_pullback source left right eligible
      sourceContext pre definitionEnv env sourceRecurse targetRecurse
      children recurse sourceItems sourceCompiled items compiled
  have actualProof : P actualContext :=
    Eq.mp (congrArg P same) exactProof
  exact actualProof same targetEnv targetItems targetCompiled
    recurseDenotation

private theorem compileRegion_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel
      (context : ConcreteElaboration.WireContext source.val)
      (region : source.val.RegionId)
      (_sourceAbove :
        ConcreteElaboration.ContextAbove source.val context region)
      (_targetAbove :
        ConcreteElaboration.ContextAbove
          (Target source left right eligible)
          (targetContext source left right eligible context) region)
      (targetEnv :
        Env pre (targetContext source left right eligible context).sigs)
      {sourceBody : Region definitions context.sigs}
      {targetBody :
        Region definitions
          (targetContext source left right eligible context).sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel
          region context = some sourceBody →
      ConcreteElaboration.compileRegion? definitions
          (Target source left right eligible) fuel region
          (targetContext source left right eligible context) =
        some targetBody →
      (denoteRegion pre definitionEnv targetEnv targetBody ↔
        denoteRegion pre definitionEnv
          (Env.comp targetEnv
            (contextRenaming source left right eligible context))
          sourceBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro context region sourceAbove targetAbove targetEnv
        sourceBody targetBody sourceCompiled
      simpa using sourceCompiled
  | succ fuel induction =>
      intro context region sourceAbove targetAbove targetEnv
        sourceBody targetBody sourceCompiled targetCompiled
      simp only [ConcreteElaboration.compileRegion?_succ] at sourceCompiled
      simp only [ConcreteElaboration.compileRegion?_succ] at targetCompiled
      cases sourceNodesEquation :
          ConcreteElaboration.compileNodes? definitions source.val
            (context.extend region) (source.val.nodesAt region) with
      | none =>
          rw [sourceNodesEquation] at sourceCompiled
          simp at sourceCompiled
      | some sourceNodes =>
          rw [sourceNodesEquation] at sourceCompiled
          cases sourceChildrenEquation :
              ConcreteElaboration.compileChildrenWith? definitions source.val
                (ConcreteElaboration.compileRegion? definitions
                  source.val fuel)
                (context.extend region)
                (source.val.childrenOf region) with
          | none =>
              rw [sourceChildrenEquation] at sourceCompiled
              simp at sourceCompiled
          | some sourceChildren =>
              rw [sourceChildrenEquation] at sourceCompiled
              cases targetNodesEquation :
                  ConcreteElaboration.compileNodes? definitions
                    (Target source left right eligible)
                    ((targetContext source left right eligible context).extend
                      region)
                    ((Target source left right eligible).nodesAt region) with
              | none =>
                  rw [targetNodesEquation] at targetCompiled
                  simp at targetCompiled
              | some targetNodes =>
                  rw [targetNodesEquation] at targetCompiled
                  cases targetChildrenEquation :
                      ConcreteElaboration.compileChildrenWith? definitions
                        (Target source left right eligible)
                        (ConcreteElaboration.compileRegion? definitions
                          (Target source left right eligible) fuel)
                        ((targetContext source left right eligible
                          context).extend region)
                        ((Target source left right eligible).childrenOf
                          region) with
                  | none =>
                      rw [targetChildrenEquation] at targetCompiled
                      simp at targetCompiled
                  | some targetChildren =>
                      rw [targetChildrenEquation] at targetCompiled
                      have sourceBodyEquality :
                          ConcreteElaboration.finishRegion source.val
                              context region
                              (.mk (sourceNodes.append sourceChildren)) =
                            sourceBody :=
                        Option.some.inj sourceCompiled
                      have targetBodyEquality :
                          ConcreteElaboration.finishRegion
                              (Target source left right eligible)
                              (targetContext source left right eligible
                                context)
                              region
                              (.mk (targetNodes.append targetChildren)) =
                            targetBody :=
                        Option.some.inj targetCompiled
                      subst sourceBody
                      subst targetBody
                      rw [ConcreteElaboration.denote_finishRegion,
                        ConcreteElaboration.denote_finishRegion]
                      have sourceExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions source.val
                          source.property context region sourceAbove
                      have targetExtendedNodup :=
                        ConcreteElaboration.extend_nodup definitions
                          (Target source left right eligible)
                          (fusionCandidate_wellFormed source left right
                            eligible)
                          (targetContext source left right eligible context)
                          region targetAbove
                      have recurseEquiv :
                          ∀ (sourceExtended :
                              Env pre (context.extend region).sigs)
                            (targetExtended :
                              Env pre
                                ((targetContext source left right eligible
                                  context).extend region).sigs),
                            sourceExtended =
                                Env.comp targetExtended
                                  (extendedContextRenaming source left right
                                    eligible context region) →
                            ∀ child,
                              child ∈ source.val.childrenOf region →
                              ∀ sourceChildBody targetChildBody,
                                ConcreteElaboration.compileRegion? definitions
                                    source.val fuel child
                                    (context.extend region) =
                                  some sourceChildBody →
                                ConcreteElaboration.compileRegion? definitions
                                    (Target source left right eligible) fuel
                                    child
                                    ((targetContext source left right eligible
                                      context).extend region) =
                                  some targetChildBody →
                                (denoteRegion pre definitionEnv targetExtended
                                    targetChildBody ↔
                                  denoteRegion pre definitionEnv sourceExtended
                                    sourceChildBody) := by
                        intro sourceExtended targetExtended envRelated child
                          childMember sourceChildBody targetChildBody
                          sourceChildCompiled targetChildCompiled
                        have sourceChildData :=
                          ConcreteElaboration.mem_childrenOf source.val
                            region child childMember
                        have targetChildData :
                            (Target source left right eligible).regions child =
                              .cut region := by
                          simpa [Target, fusionCandidate] using sourceChildData
                        have sourceChildAbove :=
                          ConcreteElaboration.extend_above_child definitions
                            source.val source.property context region child
                            sourceAbove sourceChildData
                        have targetChildAbove :=
                          ConcreteElaboration.extend_above_child definitions
                            (Target source left right eligible)
                            (fusionCandidate_wellFormed source left right
                              eligible)
                            (targetContext source left right eligible context)
                            region child targetAbove targetChildData
                        let sourceContext := context.extend region
                        let exactContext :=
                          targetContext source left right eligible sourceContext
                        let actualContext :=
                          (targetContext source left right eligible
                            context).extend region
                        have same : exactContext = actualContext :=
                          targetContext_extend source left right eligible
                            context region
                        let P : ConcreteElaboration.WireContext
                            (Target source left right eligible) → Prop :=
                          fun targetCtx =>
                            ∀ (alignment : exactContext = targetCtx)
                              (above :
                                ConcreteElaboration.ContextAbove
                                  (Target source left right eligible)
                                  targetCtx child)
                              (env : Env pre targetCtx.sigs)
                              (targetResult :
                                Region definitions targetCtx.sigs),
                              sourceExtended =
                                  Env.comp env
                                    (fun {_} value =>
                                      congrArg
                                          ConcreteElaboration.WireContext.sigs
                                          alignment ▸
                                        contextRenaming source left right
                                          eligible sourceContext value) →
                              ConcreteElaboration.compileRegion? definitions
                                  (Target source left right eligible) fuel child
                                  targetCtx =
                                some targetResult →
                              (denoteRegion pre definitionEnv env
                                  targetResult ↔
                                denoteRegion pre definitionEnv sourceExtended
                                  sourceChildBody)
                        have exactProof : P exactContext := by
                          intro alignment above env targetResult related
                            compiled
                          have alignmentProof : alignment = rfl :=
                            Subsingleton.elim _ _
                          rw [alignmentProof] at related
                          rw [related]
                          exact induction sourceContext child sourceChildAbove
                            above env sourceChildCompiled compiled
                        have actualProof : P actualContext :=
                          Eq.mp (congrArg P same) exactProof
                        exact actualProof same targetChildAbove targetExtended
                          targetChildBody envRelated targetChildCompiled
                      constructor
                      · rintro ⟨targetValues, targetCoreDenotes⟩
                        let targetExtended :=
                          ConcreteElaboration.extendEnvironment
                            (Target source left right eligible)
                            (targetContext source left right eligible context)
                            region targetValues targetEnv
                        let sourceExtended :=
                          Env.comp targetExtended
                            (extendedContextRenaming source left right eligible
                              context region)
                        let sourceValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            source.val context.ids
                            (source.val.wiresAt region) sourceExtended
                        have sourceRealizes :
                            ConcreteElaboration.extendEnvironment source.val
                                context region sourceValues
                                (Env.comp targetEnv
                                  (contextRenaming source left right eligible
                                    context)) =
                              sourceExtended :=
                          extendedEnvironment_natural source left right eligible
                            context region sourceExtendedNodup pre targetValues
                            targetEnv
                        refine ⟨sourceValues, ?_⟩
                        rw [sourceRealizes]
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                            at targetCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                        rw [denoteItemSeq_append] at targetCoreDenotes ⊢
                        constructor
                        · exact
                            (compiled_nodes_extended source left right eligible
                              context region sourceExtendedNodup pre
                              definitionEnv targetExtended sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mp targetCoreDenotes.1
                        · rw [target_childrenOf source left right eligible
                            region] at targetChildrenEquation
                          exact
                            (compiled_children_extended source left right
                              eligible context region pre definitionEnv
                              targetExtended
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source left right eligible) fuel)
                              (source.val.childrenOf region) sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation
                              (recurseEquiv sourceExtended targetExtended rfl)
                              ).mp targetCoreDenotes.2
                      · rintro ⟨sourceValues, sourceCoreDenotes⟩
                        let sourceExtended :=
                          ConcreteElaboration.extendEnvironment source.val
                            context region sourceValues
                            (Env.comp targetEnv
                              (contextRenaming source left right eligible
                                context))
                        let targetExtended :=
                          Env.comp sourceExtended
                            (extendedContextSection source left right eligible
                              context region)
                        let targetValues :=
                          ConcreteElaboration.valuesFromEnvironmentFor
                            (Target source left right eligible)
                            (targetContext source left right eligible
                              context).ids
                            ((Target source left right eligible).wiresAt region)
                            targetExtended
                        have targetRealizes :
                            ConcreteElaboration.extendEnvironment
                                (Target source left right eligible)
                                (targetContext source left right eligible
                                  context)
                                region targetValues targetEnv =
                              targetExtended :=
                          reverseExtendedEnvironment_natural source left right
                            eligible context region sourceExtendedNodup
                            targetAbove.1 pre sourceValues
                            (Env.comp targetEnv
                              (contextRenaming source left right eligible
                                context))
                            targetEnv rfl
                        have envRelated :
                            sourceExtended =
                              Env.comp targetExtended
                                (extendedContextRenaming source left right
                                  eligible context region) := by
                          funext sig value
                          change
                            sourceExtended sig value =
                              sourceExtended sig
                                (extendedContextSection source left right
                                  eligible context region
                                  (extendedContextRenaming source left right
                                    eligible context region value))
                          rw [extendedContextSection_renaming source left right
                            eligible context region sourceExtendedNodup]
                        refine ⟨targetValues, ?_⟩
                        rw [targetRealizes]
                        change
                          denoteItemSeq pre definitionEnv sourceExtended
                            (sourceNodes.append sourceChildren)
                            at sourceCoreDenotes
                        change
                          denoteItemSeq pre definitionEnv targetExtended
                            (targetNodes.append targetChildren)
                        rw [denoteItemSeq_append] at sourceCoreDenotes ⊢
                        constructor
                        · exact
                            (compiled_nodes_extended source left right eligible
                              context region sourceExtendedNodup pre
                              definitionEnv targetExtended sourceNodes
                              sourceNodesEquation targetNodes
                              targetNodesEquation).mpr
                              (by rw [← envRelated]
                                  exact sourceCoreDenotes.1)
                        · rw [target_childrenOf source left right eligible
                            region] at targetChildrenEquation
                          exact
                            (compiled_children_extended source left right
                              eligible context region pre definitionEnv
                              targetExtended
                              (ConcreteElaboration.compileRegion? definitions
                                source.val fuel)
                              (ConcreteElaboration.compileRegion? definitions
                                (Target source left right eligible) fuel)
                              (source.val.childrenOf region) sourceChildren
                              sourceChildrenEquation targetChildren
                              targetChildrenEquation
                              (by
                                intro child member sourceChild targetChild
                                  sourceChildCompiled targetChildCompiled
                                have childEquivalence :=
                                  recurseEquiv sourceExtended targetExtended
                                    envRelated child member sourceChild
                                    targetChild sourceChildCompiled
                                    targetChildCompiled
                                rw [envRelated] at childEquivalence
                                exact childEquivalence)).mpr
                              (by
                                rw [← envRelated]
                                exact sourceCoreDenotes.2)

private theorem fusionCandidate_denotation
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv
        ⟨Target source left right eligible,
          fusionCandidate_wellFormed source left right eligible⟩ ↔
      denoteChecked pre definitionEnv source := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked]
  have sourceCompiled :=
    elaborateWith_compiles definitions source.val source.property
  have targetCompiled :=
    elaborateWith_compiles definitions
      (Target source left right eligible)
      (fusionCandidate_wellFormed source left right eligible)
  unfold ConcreteElaboration.compileRoot? at sourceCompiled targetCompiled
  have targetCompiled' :
      ConcreteElaboration.compileRegion? definitions
          (Target source left right eligible)
          (source.val.regionCount + 1)
          source.val.root
          (ConcreteElaboration.WireContext.empty
            (Target source left right eligible)) =
        some (elaborateWith definitions
          (Target source left right eligible)
          (fusionCandidate_wellFormed source left right eligible)) := by
    simpa [Target, fusionCandidate] using targetCompiled
  have sourceAbove :
      ConcreteElaboration.ContextAbove source.val
        (ConcreteElaboration.WireContext.empty source.val)
        source.val.root := by
    constructor
    · simp [ConcreteElaboration.WireContext.empty]
    · intro wire member
      simp [ConcreteElaboration.WireContext.empty] at member
  have targetAbove :
      ConcreteElaboration.ContextAbove
        (Target source left right eligible)
        (targetContext source left right eligible
          (ConcreteElaboration.WireContext.empty source.val))
        source.val.root := by
    constructor
    · simp [targetContext, ConcreteElaboration.WireContext.empty]
    · intro wire member
      simp [targetContext, ConcreteElaboration.WireContext.empty] at member
  let targetEnv :
      Env pre
        (targetContext source left right eligible
          (ConcreteElaboration.WireContext.empty source.val)).sigs :=
    fun _ value => nomatch value
  have core :=
    compileRegion_denotation source left right eligible pre definitionEnv
      (source.val.regionCount + 1)
      (ConcreteElaboration.WireContext.empty source.val)
      source.val.root sourceAbove targetAbove targetEnv
      sourceCompiled (by
        simpa [targetContext, ConcreteElaboration.WireContext.empty]
          using targetCompiled')
  have sourceEnvEmpty :
      Env.comp targetEnv
          (contextRenaming source left right eligible
            (ConcreteElaboration.WireContext.empty source.val)) =
        Env.empty := by
    funext sig value
    exact nomatch value
  have targetEnvEmpty : targetEnv = Env.empty := by
    funext sig value
    exact nomatch value
  rw [sourceEnvEmpty, targetEnvEmpty] at core
  simpa [elaborate] using core

end IdentityNormalizationFusionSemantics

/--
Rule 3 preserves denotation in every premodel. Its sole premise is successful
checked fusion; no caller-supplied semantic certificate is required.
-/
theorem fuseSameRegion_sound
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (target : IdentityRewrite source)
    (result : fuseSameRegion source left right = some target)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv target.target ↔
      denoteChecked pre definitionEnv source := by
  unfold fuseSameRegion at result
  cases eligibleEquation :
      IdentityNormalizationCore.fusionEligibility? source left right with
  | none =>
      rw [eligibleEquation] at result
      simp at result
  | some eligible =>
      rw [eligibleEquation] at result
      have targetEquation := Option.some.inj result
      subst target
      exact
        IdentityNormalizationFusionSemantics.fusionCandidate_denotation
          source left right eligible pre definitionEnv

end ConcreteDiagram

end VisualProof
