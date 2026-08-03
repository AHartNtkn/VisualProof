import VisualProof.Rule.DefinitionSemantics
import VisualProof.Rule.Theorem
import VisualProof.Rule.Step
import VisualProof.Rule.Structural
import VisualProof.Rule.WirePrimitive.CompilerSoundness
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturality
import VisualProof.Diagram.Concrete.IdentityNormalizationSemantics
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinApplicationSemantics

namespace VisualProof

universe u

private theorem reference_local_empty
    (definitions : List (List Sig))
    (definition : Fin definitions.length) :
    ConcreteElaboration.openRootLocalWires
      (referenceFragmentRaw definitions definition) = [] := by
  unfold ConcreteElaboration.openRootLocalWires
  have allTrue :
      List.filter (fun _ => true)
          (Data.Finite.allFin (definitions.get definition).length) =
        Data.Finite.allFin (definitions.get definition).length := by
    apply List.filter_eq_self.mpr
    simp
  rw [show
    (referenceFragmentRaw definitions definition).diagram.wiresAt
        (referenceFragmentRaw definitions definition).diagram.root =
      List.filter (fun _ => true)
        (Data.Finite.allFin (definitions.get definition).length) by rfl,
    allTrue]
  apply List.filter_eq_nil_iff.mpr
  intro wire member
  have inBoundary : wire ∈
      ConcreteElaboration.openBoundaryWires
        (referenceFragmentRaw definitions definition) := by
    unfold ConcreteElaboration.openBoundaryWires
    exact List.mem_eraseDups.mpr (Data.Finite.mem_allFin wire)
  simp [inBoundary]

private theorem reference_root_nodes
    (definitions : List (List Sig))
    (definition : Fin definitions.length) :
    (referenceFragmentRaw definitions definition).diagram.nodesAt
        (referenceFragmentRaw definitions definition).diagram.root =
      [⟨0, Nat.zero_lt_one⟩] := by
  simp [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList,
    referenceFragmentRaw, CNode.region, Data.Finite.allFin]

private theorem reference_root_children
    (definitions : List (List Sig))
    (definition : Fin definitions.length) :
    (referenceFragmentRaw definitions definition).diagram.childrenOf
        (referenceFragmentRaw definitions definition).diagram.root = [] := by
  simp [ConcreteDiagram.childrenOf, ConcreteDiagram.regionsList,
    referenceFragmentRaw, Data.Finite.allFin]

private theorem compileNodes_ref_shape
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId) {region : diagram.RegionId}
    {definition : Fin definitions.length}
    (nodeData : diagram.nodes node =
      .ref region definition (definitions.get definition))
    {items : ItemSeq definitions context.sigs}
    (compiled : ConcreteElaboration.compileNodes? definitions diagram context
      [node] = some items) :
    ∃ arguments : Vars context.sigs (definitions.get definition),
      items = .cons (.named
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        arguments) .nil ∧
      ConcreteElaboration.ArgumentOrigins diagram context node 0 arguments := by
  simp only [List.get_eq_getElem] at nodeData ⊢
  have portOrigin :
      ∀ (port : CPort) (expected : Sig)
        (value : Var context.sigs expected),
        ConcreteElaboration.Internal.resolvePort? diagram context node port
            expected = some value →
          diagram.endpointOwner? ⟨node, port⟩ =
            some (ConcreteElaboration.WireContext.origin diagram
              context.ids value) := by
    intro port expected value resolved
    unfold ConcreteElaboration.Internal.resolvePort? at resolved
    cases owner : diagram.endpointOwner? ⟨node, port⟩ with
    | none => simp [owner] at resolved
    | some wire =>
        simp only [owner] at resolved
        rw [← ConcreteElaboration.Internal.origin_of_resolvedExpected
          diagram context wire expected resolved]
  have argsOrigins :
      ∀ (remaining : List Sig) (index : Nat)
        (values : Vars context.sigs remaining),
        ConcreteElaboration.Internal.resolveArgs? diagram context node
            remaining index = some values →
          ConcreteElaboration.ArgumentOrigins diagram context node index
            values := by
    intro remaining
    induction remaining with
    | nil =>
        intro index values resolved
        cases values
        trivial
    | cons sig rest induction =>
        intro index values resolved
        cases headEquation :
            ConcreteElaboration.Internal.resolvePort? diagram context node
              (.arg index) sig with
        | none =>
            simp [ConcreteElaboration.Internal.resolveArgs?, headEquation]
              at resolved
        | some head =>
            cases tailEquation :
                ConcreteElaboration.Internal.resolveArgs? diagram context node
                  rest (index + 1) with
            | none =>
                simp [ConcreteElaboration.Internal.resolveArgs?, headEquation,
                  tailEquation] at resolved
            | some tail =>
                have valuesExact : Vars.cons head tail = values :=
                  Option.some.inj (by
                    simpa [ConcreteElaboration.Internal.resolveArgs?,
                      headEquation, tailEquation] using resolved)
                subst values
                exact ⟨portOrigin _ _ _ headEquation,
                  induction (index + 1) tail tailEquation⟩
  simp only [ConcreteElaboration.compileNodes?_equation,
    ConcreteElaboration.Internal.compileNode?_equation, nodeData] at compiled
  cases argumentsEquation :
      ConcreteElaboration.Internal.resolveArgs? diagram context node
        definitions[definition.val] 0 with
  | none => simp [argumentsEquation] at compiled
  | some arguments =>
      exact ⟨arguments,
        (Option.some.inj
          (by simpa [argumentsEquation] using compiled)).symm,
        argsOrigins _ _ arguments argumentsEquation⟩

private theorem empty_local_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outerIds localIds : List diagram.WireId)
    (localEmpty : localIds = [])
    (nodeIds : List diagram.NodeId)
    (childIds : List diagram.RegionId)
    (nodes children : ItemSeq definitions
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig))
    (values : ConcreteElaboration.WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig))
    (env : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    (definitionEnv : DefinitionEnv pre definitions)
    (nodesCompiled :
      ConcreteElaboration.compileNodes? definitions diagram
        ⟨localIds ++ outerIds⟩ nodeIds = some nodes)
    (childrenCompiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram
            diagram.regionCount)
          ⟨localIds ++ outerIds⟩ childIds = some children)
    (denotes : denoteRegion pre definitionEnv
      (ConcreteElaboration.extendEnvironmentFor diagram outerIds localIds
        values env) (.mk (nodes.append children))) :
    ∃ (nodes' children' : ItemSeq definitions
        (outerIds.map fun wire => (diagram.wires wire).sig)),
      ConcreteElaboration.compileNodes? definitions diagram
          ⟨outerIds⟩ nodeIds = some nodes' ∧
        ConcreteElaboration.compileChildrenWith? definitions diagram
            (ConcreteElaboration.compileRegion? definitions diagram
              diagram.regionCount)
            ⟨outerIds⟩ childIds = some children' ∧
          denoteRegion pre definitionEnv env
            (.mk (nodes'.append children')) := by
  subst localIds
  cases values
  exact ⟨nodes, children, nodesCompiled, childrenCompiled, denotes⟩

private theorem empty_local_nodes
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outerIds localIds : List diagram.WireId)
    (localEmpty : localIds = [])
    (nodeIds : List diagram.NodeId)
    (nodes : ItemSeq definitions
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig))
    (compiled : ConcreteElaboration.compileNodes? definitions diagram
      ⟨localIds ++ outerIds⟩ nodeIds = some nodes) :
    ∃ nodes' : ItemSeq definitions
        (outerIds.map fun wire => (diagram.wires wire).sig),
      ConcreteElaboration.compileNodes? definitions diagram
        ⟨outerIds⟩ nodeIds = some nodes' := by
  subst localIds
  exact ⟨nodes, compiled⟩

private theorem restore_empty_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outerIds localIds : List diagram.WireId)
    (localEmpty : localIds = [])
    (nodeIds : List diagram.NodeId)
    (childIds : List diagram.RegionId)
    (nodes children : ItemSeq definitions
      (outerIds.map fun wire => (diagram.wires wire).sig))
    (env : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    (definitionEnv : DefinitionEnv pre definitions)
    (nodesCompiled : ConcreteElaboration.compileNodes? definitions diagram
      ⟨outerIds⟩ nodeIds = some nodes)
    (childrenCompiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram
          (ConcreteElaboration.compileRegion? definitions diagram
            diagram.regionCount)
          ⟨outerIds⟩ childIds = some children)
    (denotes : denoteRegion pre definitionEnv env
      (.mk (nodes.append children))) :
    ∃ (fullNodes fullChildren : ItemSeq definitions
          ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig))
        (values : ConcreteElaboration.WireValues pre
          (localIds.map fun wire => (diagram.wires wire).sig)),
      ConcreteElaboration.compileNodes? definitions diagram
          ⟨localIds ++ outerIds⟩ nodeIds = some fullNodes ∧
        ConcreteElaboration.compileChildrenWith? definitions diagram
            (ConcreteElaboration.compileRegion? definitions diagram
              diagram.regionCount)
            ⟨localIds ++ outerIds⟩ childIds = some fullChildren ∧
          denoteRegion pre definitionEnv
            (ConcreteElaboration.extendEnvironmentFor diagram outerIds
              localIds values env) (.mk (fullNodes.append fullChildren)) := by
  subst localIds
  exact ⟨nodes, children, .nil, nodesCompiled, childrenCompiled, denotes⟩

private theorem variableOrigins_length
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    (ConcreteElaboration.variableOrigins diagram context variables).length =
      args.length := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp [ConcreteElaboration.variableOrigins, induction]

private theorem argumentOrigins_get
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
        ⟨index, by simpa [variableOrigins_length] using bound⟩) := by
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

private theorem variableOrigins_cast
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {left right : List Sig}
    (same : left = right)
    (variables : Vars context.sigs left) :
    ConcreteElaboration.variableOrigins diagram context (same ▸ variables) =
      ConcreteElaboration.variableOrigins diagram context variables := by
  cases same
  rfl

private theorem denote_cast
    (env : Env pre context)
    {left right : List Sig}
    (same : left = right)
    (variables : Vars context left) :
    Vars.denote env (same ▸ variables) =
      same ▸ Vars.denote env variables := by
  cases same
  rfl

private theorem origin_member
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value : Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => simp [ConcreteElaboration.WireContext.origin]
      | there rest => exact List.mem_cons_of_mem head (induction rest)

private theorem origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig} :
    Function.Injective
      (ConcreteElaboration.WireContext.origin diagram ids (sig := sig)) := by
  intro left right same
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      have parts := List.pairwise_cons.mp nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there rest =>
              exact (parts.1 _ (origin_member diagram tail rest) same).elim
      | there leftRest =>
          cases right with
          | here =>
              exact (parts.1 _ (origin_member diagram tail leftRest)
                same.symm).elim
          | there rightRest =>
              exact congrArg Var.there (induction parts.2 same)

private theorem variables_eq_of_origins
    {argumentTypes : List Sig}
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.ids.Nodup)
    (left right : Vars context.sigs argumentTypes)
    (same :
      ConcreteElaboration.variableOrigins diagram context left =
        ConcreteElaboration.variableOrigins diagram context right) :
    left = right := by
  induction left with
  | nil => cases right; rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [ConcreteElaboration.variableOrigins, List.cons.injEq]
            at same
          have headExact := origin_injective diagram context.ids nodup same.1
          subst rightHead
          exact congrArg (Vars.cons leftHead) (induction rightTail same.2)

private theorem variableOrigins_eq_map_entries
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins diagram context variables =
      variables.entries.map
        (fun packed => match packed with
          | ⟨_, value⟩ =>
              ConcreteElaboration.WireContext.origin diagram context.ids
                value) := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp only [ConcreteElaboration.variableOrigins, Vars.entries,
        List.map_cons, induction]

private theorem wireOfPacked_eq_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (packed : PackedVar
      (ids.map fun wire => (diagram.wires wire).sig)) :
    ExtractedBoundaryCompiler.wireOfPacked diagram ids packed =
      match packed with
      | ⟨_, value⟩ =>
          ConcreteElaboration.WireContext.origin diagram ids value := by
  rcases packed with ⟨sig, value⟩
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest

private theorem variableOrigins_boundary
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    ConcreteElaboration.variableOrigins fragment.val.diagram
        ⟨ConcreteElaboration.openBoundaryWires fragment.val⟩
        compiled.boundary = fragment.val.boundary := by
  have origins := compileExtractedBoundary?_origins fragment compiled.boundary
    compiled.boundary_generated
  rw [variableOrigins_eq_map_entries fragment.val.diagram
    ⟨ConcreteElaboration.openBoundaryWires fragment.val⟩
    compiled.boundary]
  have mapped :
      compiled.boundary.entries.map
          (ExtractedBoundaryCompiler.wireOfPacked fragment.val.diagram
            (ConcreteElaboration.openBoundaryWires fragment.val)) =
        compiled.boundary.entries.map
          (fun packed => match packed with
            | ⟨_, value⟩ => ConcreteElaboration.WireContext.origin
                fragment.val.diagram
                (ConcreteElaboration.openBoundaryWires fragment.val) value) := by
    apply List.map_congr_left
    intro packed _
    exact wireOfPacked_eq_origin fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val) packed
  exact mapped.symm.trans origins

private theorem reference_arguments_exact
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment)
    (arguments : Vars
      (ConcreteElaboration.openBoundaryClassSigs reference.fragment.val)
      (definitions.get definition))
    (argumentOrigins : ConcreteElaboration.ArgumentOrigins
      (referenceFragmentRaw definitions definition).diagram
      ⟨ConcreteElaboration.openBoundaryWires
        (referenceFragmentRaw definitions definition)⟩
      ⟨0, Nat.zero_lt_one⟩ 0 arguments) :
    arguments = reference.boundarySignatures ▸ compiled.boundary := by
  have argumentsOrigins :
      ConcreteElaboration.variableOrigins
          (referenceFragmentRaw definitions definition).diagram
          ⟨ConcreteElaboration.openBoundaryWires
            (referenceFragmentRaw definitions definition)⟩
          arguments =
        (referenceFragmentRaw definitions definition).boundary := by
    apply List.ext_get
    · simp [variableOrigins_length, referenceFragmentRaw,
        Data.Finite.allFin_eq_finRange]
    · intro index leftBound rightBound
      have compiledOwner := argumentOrigins_get
        (referenceFragmentRaw definitions definition).diagram
        ⟨ConcreteElaboration.openBoundaryWires
          (referenceFragmentRaw definitions definition)⟩
        ⟨0, Nat.zero_lt_one⟩ 0 arguments argumentOrigins index
        (by
          rw [← variableOrigins_length
            (referenceFragmentRaw definitions definition).diagram
            ⟨ConcreteElaboration.openBoundaryWires
              (referenceFragmentRaw definitions definition)⟩ arguments]
          exact leftBound)
      let wire : (referenceFragmentRaw definitions definition).diagram.WireId :=
        ⟨index, by simpa [referenceFragmentRaw,
          Data.Finite.allFin_eq_finRange] using rightBound⟩
      have expectedOwner :
          (referenceFragmentRaw definitions definition).diagram.endpointOwner?
              ⟨⟨0, Nat.zero_lt_one⟩, .arg index⟩ = some wire := by
        apply ConcreteDiagram.endpointOwner?_eq_of_incident definitions
          (referenceFragmentRaw definitions definition).diagram
          reference.wellFormed.diagram
        · simp [ConcreteDiagram.requiredPorts, referenceFragmentRaw]
          exact wire.isLt
        · simp only [referenceFragmentRaw]
          exact List.mem_singleton.mpr rfl
      simpa [wire, referenceFragmentRaw,
        Data.Finite.allFin_eq_finRange] using
        Option.some.inj (compiledOwner.symm.trans (by
          simpa using expectedOwner))
  have boundaryOrigins := variableOrigins_boundary compiled
  have castBoundaryOrigins :
      ConcreteElaboration.variableOrigins
          (referenceFragmentRaw definitions definition).diagram
          ⟨ConcreteElaboration.openBoundaryWires
            (referenceFragmentRaw definitions definition)⟩
          (reference.boundarySignatures ▸ compiled.boundary) =
        (referenceFragmentRaw definitions definition).boundary := by
    exact (variableOrigins_cast
      (referenceFragmentRaw definitions definition).diagram
      ⟨ConcreteElaboration.openBoundaryWires
        (referenceFragmentRaw definitions definition)⟩
      reference.boundarySignatures compiled.boundary).trans (by
        simpa only [CheckedReferenceFragment.generated] using boundaryOrigins)
  exact variables_eq_of_origins
    (referenceFragmentRaw definitions definition).diagram
    ⟨ConcreteElaboration.openBoundaryWires
      (referenceFragmentRaw definitions definition)⟩
    (Data.Finite.eraseDups_nodup _) arguments
    (reference.boundarySignatures ▸ compiled.boundary)
    (argumentsOrigins.trans castBoundaryOrigins.symm)

private theorem reference_nodes_compile
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment) :
    ConcreteElaboration.compileNodes? definitions reference.fragment.val.diagram
        ⟨ConcreteElaboration.openBoundaryWires reference.fragment.val⟩
        [⟨0, Nat.zero_lt_one⟩] =
      some (.cons (.named
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (reference.boundarySignatures ▸ compiled.boundary)) .nil) := by
  have generated := compiled.body_generated
  rw [ConcreteElaboration.compileOpenRoot?_equation] at generated
  simp only [CheckedReferenceFragment.generated] at generated
  obtain ⟨nodes, nodeEquation, _⟩ := Option.bind_eq_some_iff.mp generated
  have localEmpty := reference_local_empty definitions definition
  have rootNodes := reference_root_nodes definitions definition
  obtain ⟨nodes', nodeEquation'⟩ := empty_local_nodes definitions
    (referenceFragmentRaw definitions definition).diagram
    (ConcreteElaboration.openBoundaryWires
      (referenceFragmentRaw definitions definition))
    (ConcreteElaboration.openRootLocalWires
      (referenceFragmentRaw definitions definition)) localEmpty
    ((referenceFragmentRaw definitions definition).diagram.nodesAt
      (referenceFragmentRaw definitions definition).diagram.root)
    nodes nodeEquation
  rw [rootNodes] at nodeEquation'
  obtain ⟨arguments, exact, origins⟩ := compileNodes_ref_shape
    (referenceFragmentRaw definitions definition).diagram
    ⟨ConcreteElaboration.openBoundaryWires
      (referenceFragmentRaw definitions definition)⟩
    ⟨0, Nat.zero_lt_one⟩ rfl nodeEquation'
  have argumentsExact := reference_arguments_exact reference compiled
    arguments origins
  subst arguments
  simpa only [CheckedReferenceFragment.generated] using
    (exact ▸ nodeEquation')

private theorem reference_body_denotes
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.openDiagram.classes) :
    denoteRegion pre definitionEnv env compiled.body ↔
      DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (reference.boundarySignatures ▸
          Vars.denote env compiled.boundary) := by
  have components :=
    ConcreteElaboration.denote_compileOpenRoot_components definitions
      reference.fragment.val compiled.body compiled.body_generated pre
      definitionEnv env
  simp only [CheckedReferenceFragment.fragment] at components
  have localEmpty := reference_local_empty definitions definition
  have rootNodes := reference_root_nodes definitions definition
  have rootChildren := reference_root_children definitions definition
  constructor
  · intro bodyDenotes
    obtain ⟨nodes, children, localValues, nodesCompiled,
        childrenCompiled, componentsDenote⟩ := components.mp bodyDenotes
    change denoteRegion pre definitionEnv
      (ConcreteElaboration.extendEnvironmentFor
        (referenceFragmentRaw definitions definition).diagram
        (ConcreteElaboration.openBoundaryWires
          (referenceFragmentRaw definitions definition))
        (ConcreteElaboration.openRootLocalWires
          (referenceFragmentRaw definitions definition))
        localValues env) (.mk (nodes.append children)) at componentsDenote
    obtain ⟨nodes', children', nodesCompiled', childrenCompiled',
        componentsDenote'⟩ := empty_local_components definitions
      (referenceFragmentRaw definitions definition).diagram
      (ConcreteElaboration.openBoundaryWires
        (referenceFragmentRaw definitions definition))
      (ConcreteElaboration.openRootLocalWires
        (referenceFragmentRaw definitions definition)) localEmpty
      ((referenceFragmentRaw definitions definition).diagram.nodesAt
        (referenceFragmentRaw definitions definition).diagram.root)
      ((referenceFragmentRaw definitions definition).diagram.childrenOf
        (referenceFragmentRaw definitions definition).diagram.root)
      nodes children localValues env definitionEnv nodesCompiled
      childrenCompiled componentsDenote
    rw [rootNodes] at nodesCompiled'
    rw [rootChildren] at childrenCompiled'
    simp only [ConcreteElaboration.compileChildrenWith?] at childrenCompiled'
    have childrenExact : children' = .nil := by
      simpa using Option.some.inj childrenCompiled'.symm
    subst children'
    obtain ⟨arguments, nodesExact, argumentOrigins⟩ :=
      compileNodes_ref_shape
        (referenceFragmentRaw definitions definition).diagram
        ⟨ConcreteElaboration.openBoundaryWires
          (referenceFragmentRaw definitions definition)⟩
        ⟨0, Nat.zero_lt_one⟩ rfl nodesCompiled'
    subst nodes'
    have argumentsExact := reference_arguments_exact reference compiled
      arguments argumentOrigins
    subst arguments
    have rawNamed : DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (Vars.denote env
          (reference.boundarySignatures ▸ compiled.boundary)) := by
      simpa only [ItemSeq.append_nil, denoteRegion, denoteItemSeq, denoteItem]
        using componentsDenote'.1
    exact Eq.mp (congrArg
      (DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition))
      (denote_cast env reference.boundarySignatures compiled.boundary))
      rawNamed
  · intro namedDenotes
    let nodes : ItemSeq definitions compiled.openDiagram.classes :=
      .cons (.named
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (reference.boundarySignatures ▸ compiled.boundary)) .nil
    let children : ItemSeq definitions compiled.openDiagram.classes := .nil
    have nodesCompiled :
        ConcreteElaboration.compileNodes? definitions
            (referenceFragmentRaw definitions definition).diagram
            ⟨ConcreteElaboration.openBoundaryWires
              (referenceFragmentRaw definitions definition)⟩
            ((referenceFragmentRaw definitions definition).diagram.nodesAt
              (referenceFragmentRaw definitions definition).diagram.root) =
          some nodes := by
      rw [rootNodes]
      simpa only [CheckedReferenceFragment.generated, nodes] using
        reference_nodes_compile reference compiled
    have childrenCompiled :
        ConcreteElaboration.compileChildrenWith? definitions
            (referenceFragmentRaw definitions definition).diagram
            (ConcreteElaboration.compileRegion? definitions
              (referenceFragmentRaw definitions definition).diagram
              (referenceFragmentRaw definitions definition).diagram.regionCount)
            ⟨ConcreteElaboration.openBoundaryWires
              (referenceFragmentRaw definitions definition)⟩
            ((referenceFragmentRaw definitions definition).diagram.childrenOf
              (referenceFragmentRaw definitions definition).diagram.root) =
          some children := by
      rw [rootChildren]
      rfl
    have intrinsicDenotes : denoteRegion pre definitionEnv env
        (.mk (nodes.append children)) := by
      have rawNamed := Eq.mpr (congrArg
        (DefinitionEnv.lookup definitionEnv
          (ConcreteElaboration.Internal.definitionVarAt definitions definition))
        (denote_cast env reference.boundarySignatures compiled.boundary))
        namedDenotes
      simpa only [nodes, children, ItemSeq.append_nil, denoteRegion,
        denoteItemSeq, denoteItem] using And.intro rawNamed trivial
    obtain ⟨fullNodes, fullChildren, localValues, fullNodesCompiled,
        fullChildrenCompiled, fullDenotes⟩ :=
      restore_empty_components definitions
        (referenceFragmentRaw definitions definition).diagram
        (ConcreteElaboration.openBoundaryWires
          (referenceFragmentRaw definitions definition))
        (ConcreteElaboration.openRootLocalWires
          (referenceFragmentRaw definitions definition)) localEmpty
        ((referenceFragmentRaw definitions definition).diagram.nodesAt
          (referenceFragmentRaw definitions definition).diagram.root)
        ((referenceFragmentRaw definitions definition).diagram.childrenOf
          (referenceFragmentRaw definitions definition).diagram.root)
        nodes children env definitionEnv nodesCompiled childrenCompiled
        intrinsicDenotes
    exact components.mpr ⟨fullNodes, fullChildren, localValues,
      fullNodesCompiled, fullChildrenCompiled, by
        simpa only [ConcreteElaboration.extendOpenRootEnvironment] using
          fullDenotes⟩

private theorem nodup_of_map_nodup
    (values : List α) (mapping : α → β)
    (mapped : (values.map mapping).Nodup) : values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.map_cons, List.nodup_cons] at mapped
      rw [List.nodup_cons]
      constructor
      · intro member
        exact mapped.1 (List.mem_map.mpr ⟨_, member, rfl⟩)
      · exact induction mapped.2

private theorem reference_boundary_entries_nodup
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment) :
    compiled.boundary.entries.Nodup := by
  have origins := compileExtractedBoundary?_origins reference.fragment
    compiled.boundary compiled.boundary_generated
  apply nodup_of_map_nodup compiled.boundary.entries
    (ExtractedBoundaryCompiler.wireOfPacked reference.fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires reference.fragment.val))
  apply Eq.mpr (congrArg List.Nodup origins)
  simpa only [CheckedReferenceFragment.generated, referenceFragmentRaw] using
    Data.Finite.allFin_nodup (definitions.get definition).length

private theorem source_mem_of_paired
    {source target : List Sig}
    {args : List Sig}
    {sig : Sig}
    {sources : Vars source args}
    {targets : Vars target args}
    {sourceValue : Var source sig}
    {targetValue : Var target sig}
    (paired : Vars.Paired sources targets sourceValue targetValue) :
    (⟨_, sourceValue⟩ : PackedVar source) ∈ sources.entries := by
  induction paired with
  | head => simp [Vars.entries]
  | tail _ induction => exact List.mem_cons_of_mem _ induction

private theorem paired_target_eq_of_source_nodup
    {source target : List Sig}
    {args : List Sig}
    {sig : Sig}
    {sources : Vars source args}
    {targets : Vars target args}
    {sourceValue : Var source sig}
    {left right : Var target sig}
    (nodup : sources.entries.Nodup)
    (first : Vars.Paired sources targets sourceValue left)
    (second : Vars.Paired sources targets sourceValue right) :
    left = right := by
  induction first with
  | head =>
      cases second with
      | head => rfl
      | tail second =>
          exact (List.nodup_cons.mp nodup).1
            (source_mem_of_paired second) |>.elim
  | tail first induction =>
      cases second with
      | head =>
          exact (List.nodup_cons.mp nodup).1
            (source_mem_of_paired first) |>.elim
      | tail second =>
          exact induction (List.nodup_cons.mp nodup).2 second

private theorem denote_eq_of_paired_values
    (sources : Vars source args)
    (targets : Vars target args)
    (left : Env pre source)
    (right : Env pre target)
    (equal : ∀ {sig} (sourceValue : Var source sig)
      (targetValue : Var target sig),
      Vars.Paired sources targets sourceValue targetValue →
        left sig sourceValue = right sig targetValue) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil => cases targets; rfl
  | cons sourceHead sourceTail induction =>
      cases targets with
      | cons targetHead targetTail =>
          simp only [Vars.denote_cons, PreModel.Args, Prod.mk.injEq]
          constructor
          · exact equal sourceHead targetHead .head
          · apply induction
            intro sig sourceValue targetValue paired
            exact equal sourceValue targetValue (.tail paired)

private theorem reference_attachment_boundary_values
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment)
    (attachment : SpliceAttachment compiled.openDiagram target)
    (env : Env pre target) :
    Vars.denote (Env.comp env attachment.classMap) compiled.boundary =
      Vars.denote env attachment.positions := by
  apply denote_eq_of_paired_values compiled.boundary attachment.positions
  intro sig sourceValue targetValue paired
  have targetExact := paired_target_eq_of_source_nodup
    (reference_boundary_entries_nodup reference compiled)
    (attachment.representative_position sourceValue) paired
  simpa only [Env.comp] using congrArg (env sig) targetExact

private theorem reference_open_at_attachment
    {definitions : List (List Sig)}
    {definition : Fin definitions.length}
    (reference : CheckedReferenceFragment definitions definition)
    (compiled : OpenCompilation reference.fragment)
    (attachment : SpliceAttachment compiled.openDiagram target)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre target) :
    denoteOpen pre definitionEnv compiled.openDiagram
        (Vars.denote env attachment.positions) ↔
      DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (reference.boundarySignatures ▸
          Vars.denote env attachment.positions) := by
  have boundaryValues := reference_attachment_boundary_values
    reference compiled attachment env
  constructor
  · rintro ⟨classEnv, suppliedValues, bodyDenotes⟩
    have named := (reference_body_denotes reference compiled pre
      definitionEnv classEnv).mp bodyDenotes
    exact Eq.mp (congrArg
      (DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition))
      (congrArg
        (fun values => reference.boundarySignatures ▸ values)
        suppliedValues)) named
  · intro named
    let classEnv : Env pre compiled.openDiagram.classes :=
      Env.comp env attachment.classMap
    have classNamed : DefinitionEnv.lookup definitionEnv
        (ConcreteElaboration.Internal.definitionVarAt definitions definition)
        (reference.boundarySignatures ▸
          Vars.denote classEnv compiled.boundary) := by
      exact Eq.mpr (congrArg
        (DefinitionEnv.lookup definitionEnv
          (ConcreteElaboration.Internal.definitionVarAt definitions definition))
        (congrArg
          (fun values => reference.boundarySignatures ▸ values)
          boundaryValues)) named
    exact ⟨classEnv, boundaryValues,
      (reference_body_denotes reference compiled pre definitionEnv classEnv).mpr
        classNamed⟩

private theorem insertion_position_origins
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site) :
    ConcreteElaboration.variableOrigins base.val common.frame.visible
        (compiled.positionsAt common) =
      List.ofFn attachment.target := by
  rw [variableOrigins_eq_map_entries]
  apply List.ext_get
  · simp only [List.length_map, ExtractedBoundaryCompiler.entries_length,
      List.length_ofFn, checkedBoundarySigs, List.length_map]
  · intro position leftBound rightBound
    let boundaryPosition : Fin fragment.val.boundary.length :=
      ⟨position, by simpa using rightBound⟩
    have exactOrigin := compiled.targetPackedAtAt_origin common boundaryPosition
    simpa only [InsertionCompilation.targetPackedAtAt,
      VisualProof.targetPackedAt, List.get_eq_getElem, List.getElem_map,
      List.getElem_ofFn, wireOfPacked_eq_origin] using exactOrigin

private theorem insertion_positions_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {leftFragment rightFragment : CheckedOpenDiagram definitions}
    {leftCompiled : OpenCompilation leftFragment}
    {rightCompiled : OpenCompilation rightFragment}
    {leftAttachment : ConcreteSpliceAttachment base site leftFragment}
    {rightAttachment : ConcreteSpliceAttachment base site rightFragment}
    (left : InsertionCompilation leftCompiled leftAttachment)
    (right : InsertionCompilation rightCompiled rightAttachment)
    (common : SiteCompilation base site)
    (signatures : checkedBoundarySigs leftFragment =
      checkedBoundarySigs rightFragment)
    (boundaryLength : leftFragment.val.boundary.length =
      rightFragment.val.boundary.length)
    (targets : ∀ position : Fin leftFragment.val.boundary.length,
      leftAttachment.target position =
        rightAttachment.target (Fin.cast boundaryLength position)) :
    signatures ▸ left.positionsAt common = right.positionsAt common := by
  apply variables_eq_of_origins base.val common.frame.visible
    (ConcreteWireQuantifier.RelationJoinSemantics.Internal.siteCompilation_visible_nodup
      common)
  rw [variableOrigins_cast,
    insertion_position_origins left common,
    insertion_position_origins right common]
  apply List.ext_get
  · simpa only [List.length_ofFn] using boundaryLength
  · intro position leftBound rightBound
    let leftPosition : Fin leftFragment.val.boundary.length :=
      ⟨position, by simpa only [List.length_ofFn] using leftBound⟩
    simpa only [List.get_eq_getElem, List.getElem_ofFn] using
      targets leftPosition

private theorem insertion_denotation_equiv
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {leftFragment rightFragment : CheckedOpenDiagram definitions}
    {leftCompiled : OpenCompilation leftFragment}
    {rightCompiled : OpenCompilation rightFragment}
    {leftAttachment : ConcreteSpliceAttachment base site leftFragment}
    {rightAttachment : ConcreteSpliceAttachment base site rightFragment}
    (left : InsertionCompilation leftCompiled leftAttachment)
    (right : InsertionCompilation rightCompiled rightAttachment)
    (common : SiteCompilation base site)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (openEquivalent : ∀ env : Env pre common.frame.visible.sigs,
      denoteOpen pre definitionEnv leftCompiled.openDiagram
          (Vars.denote env (left.intrinsicAttachmentAt common).positions) ↔
        denoteOpen pre definitionEnv rightCompiled.openDiagram
          (Vars.denote env (right.intrinsicAttachmentAt common).positions)) :
    denoteRegion pre definitionEnv Env.empty (left.insertedAt common) ↔
      denoteRegion pre definitionEnv Env.empty (right.insertedAt common) := by
  unfold InsertionCompilation.insertedAt
  apply context_equiv
  intro env
  rw [Region.denote_conjoin, Region.denote_conjoin,
    denote_intrinsicSplice, denote_intrinsicSplice]
  exact and_congr Iff.rfl (openEquivalent env)

private theorem reference_resolved_body_open_equiv
    (definitions : CheckedDefinitions)
    (definition : Fin definitions.intrinsic.signatures.length)
    (reference : CheckedReferenceFragment
      definitions.intrinsic.signatures definition)
    (referenceCompiled : OpenCompilation reference.fragment)
    (body : ResolvedDefinitionBody definitions.intrinsic
      (definitions.intrinsic.signatures.get definition))
    (bodyAccepted :
      definitions.resolveBody
          (ConcreteElaboration.Internal.definitionVarAt
            definitions.intrinsic.signatures definition) =
        .ok body)
    (referenceAttachment : SpliceAttachment referenceCompiled.openDiagram target)
    (bodyAttachment : SpliceAttachment body.compilation.openDiagram target)
    (model : Model)
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv)
    (env : Env model.toPreModel target)
    (argumentValues :
      reference.boundarySignatures ▸
          Vars.denote env referenceAttachment.positions =
        body.boundarySignatures ▸
          Vars.denote env bodyAttachment.positions) :
    denoteOpen model.toPreModel definitionEnv referenceCompiled.openDiagram
        (Vars.denote env referenceAttachment.positions) ↔
      denoteOpen model.toPreModel definitionEnv body.compilation.openDiagram
        (Vars.denote env bodyAttachment.positions) := by
  rw [reference_open_at_attachment reference referenceCompiled,
    definitions.intrinsic.lawful_lookup_iff model.toPreModel definitionEnv
      lawful,
    CheckedDefinitionData.resolved_denotes_definitionBody definitions.data
      (ConcreteElaboration.Internal.definitionVarAt
        definitions.intrinsic.signatures definition)
      body bodyAccepted model.toPreModel definitionEnv]
  exact iff_of_eq (congrArg
    (definitions.intrinsic.definitionBody model.toPreModel definitionEnv
      (ConcreteElaboration.Internal.definitionVarAt
        definitions.intrinsic.signatures definition))
    argumentValues)

private theorem boundary_argument_values_eq
    {leftSignatures rightSignatures arguments context : List Sig}
    (across : leftSignatures = rightSignatures)
    (leftBoundary : leftSignatures = arguments)
    (rightBoundary : rightSignatures = arguments)
    (left : Vars context leftSignatures)
    (right : Vars context rightSignatures)
    (positions : across ▸ left = right)
    (env : Env pre context) :
    leftBoundary ▸ Vars.denote env left =
      rightBoundary ▸ Vars.denote env right := by
  cases across
  cases positions
  rfl

/-- Replacing one checked canonical reference by its resolved stored body
preserves denotation under every lawful interpretation of the definitions. -/
theorem unfold_sound
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : UnfoldInput definitions source)
    (applied : AppliedUnfold definitions source input)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv applied.target := by
  induction applied using AppliedUnfold.rec
  rename_i definition region arguments sourceNode reference occurrence removed
    referenceCompilation referenceCompilationAccepted reconstruction
    reconstructionAccepted reconstructionIso reconstructionIsoAccepted
    reconstructionCompilation reconstructionCompilationAccepted body
    bodyAccepted attachment boundaryTargets bodyInsertion
    bodyInsertionAccepted result resultAccepted
  change denoteChecked model.toPreModel definitionEnv source ↔
    denoteChecked model.toPreModel definitionEnv result.checked
  let reconstructionChecked :
      CheckedDiagram definitions.intrinsic.signatures :=
    ⟨reconstruction.diagram, reconstructionCompilation.generated_wellFormed⟩
  have sourceInserted :
      denoteChecked model.toPreModel definitionEnv source ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          reconstructionCompilation.inserted :=
    (iso_denotation (left := reconstructionChecked) (right := source)
      reconstructionIso model.toPreModel definitionEnv).symm.trans
        (reconstructionCompilation.generated_checked_denotes_inserted
          model.toPreModel definitionEnv)
  have targetInserted :
      denoteChecked model.toPreModel definitionEnv result.checked ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          bodyInsertion.inserted := by
    rw [spliceRaw_success_checked resultAccepted]
    exact bodyInsertion.generated_checked_denotes_inserted
      model.toPreModel definitionEnv
  have signatures : checkedBoundarySigs reference.fragment =
      checkedBoundarySigs body.body :=
    reference.boundarySignatures.trans body.boundarySignatures.symm
  have boundaryLength : reference.fragment.val.boundary.length =
      body.body.val.boundary.length := by
    have lengths := congrArg List.length signatures
    simpa only [checkedBoundarySigs, List.length_map] using lengths
  have targets : ∀ position : Fin reference.fragment.val.boundary.length,
      reconstruction.target position =
        attachment.target (Fin.cast boundaryLength position) := by
    intro position
    have exactTarget :=
      (boundaryTargets (Fin.cast reference.boundaryLength position)).symm
    simpa only [Fin.cast_cast] using exactTarget
  let common := reconstructionCompilation.site
  have positions := insertion_positions_eq reconstructionCompilation
    bodyInsertion common signatures boundaryLength targets
  have replacementEquivalent :
      denoteRegion model.toPreModel definitionEnv Env.empty
          reconstructionCompilation.inserted ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          bodyInsertion.inserted := by
    rw [reconstructionCompilation.inserted_eq_insertedAt common,
      bodyInsertion.inserted_eq_insertedAt common]
    apply insertion_denotation_equiv
    intro env
    exact reference_resolved_body_open_equiv definitions definition reference
      referenceCompilation body bodyAccepted
      (reconstructionCompilation.intrinsicAttachmentAt common)
      (bodyInsertion.intrinsicAttachmentAt common) model definitionEnv lawful
      env (boundary_argument_values_eq signatures
        reference.boundarySignatures body.boundarySignatures
        (reconstructionCompilation.intrinsicAttachmentAt common).positions
        (bodyInsertion.intrinsicAttachmentAt common).positions positions env)
  exact sourceInserted.trans (replacementEquivalent.trans targetInserted.symm)

/-- Replacing one checked stored-body occurrence by its canonical reference
preserves denotation under every lawful interpretation of the definitions. -/
theorem fold_sound
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : FoldInput definitions source)
    (applied : AppliedFold definitions source input)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv) :
    denoteChecked model.toPreModel definitionEnv source ↔
      denoteChecked model.toPreModel definitionEnv applied.target := by
  induction applied using AppliedFold.rec
  rename_i removed removedAccepted bodyReconstruction
    bodyReconstructionAccepted bodyReconstructionIso
    bodyReconstructionIsoAccepted bodyReconstructionCompilation
    bodyReconstructionCompilationAccepted reference referenceCompilation
    referenceCompilationAccepted attachment boundaryTargets insertion
    insertionAccepted result resultAccepted
  change denoteChecked model.toPreModel definitionEnv source ↔
    denoteChecked model.toPreModel definitionEnv result.checked
  let reconstructionChecked :
      CheckedDiagram definitions.intrinsic.signatures :=
    ⟨bodyReconstruction.diagram,
      bodyReconstructionCompilation.generated_wellFormed⟩
  have sourceInserted :
      denoteChecked model.toPreModel definitionEnv source ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          bodyReconstructionCompilation.inserted :=
    (iso_denotation (left := reconstructionChecked) (right := source)
      bodyReconstructionIso model.toPreModel definitionEnv).symm.trans
        (bodyReconstructionCompilation.generated_checked_denotes_inserted
          model.toPreModel definitionEnv)
  have targetInserted :
      denoteChecked model.toPreModel definitionEnv result.checked ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          insertion.inserted := by
    rw [spliceRaw_success_checked resultAccepted]
    exact insertion.generated_checked_denotes_inserted
      model.toPreModel definitionEnv
  have signatures : checkedBoundarySigs input.body.body =
      checkedBoundarySigs reference.fragment :=
    input.body.boundarySignatures.trans reference.boundarySignatures.symm
  have boundaryLength : input.body.body.val.boundary.length =
      reference.fragment.val.boundary.length := by
    have lengths := congrArg List.length signatures
    simpa only [checkedBoundarySigs, List.length_map] using lengths
  have bodyArgumentLength : input.body.body.val.boundary.length =
      (definitions.intrinsic.signatures.get input.definition).length := by
    have lengths := congrArg List.length input.body.boundarySignatures
    simpa only [checkedBoundarySigs, List.length_map] using lengths
  have targets : ∀ position : Fin input.body.body.val.boundary.length,
      bodyReconstruction.target position =
        attachment.target (Fin.cast boundaryLength position) := by
    intro position
    have exactTarget :=
      (boundaryTargets (Fin.cast bodyArgumentLength position)).symm
    simpa only [Fin.cast_cast] using exactTarget
  let common := bodyReconstructionCompilation.site
  have positions := insertion_positions_eq bodyReconstructionCompilation
    insertion common signatures boundaryLength targets
  have replacementEquivalent :
      denoteRegion model.toPreModel definitionEnv Env.empty
          bodyReconstructionCompilation.inserted ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          insertion.inserted := by
    rw [bodyReconstructionCompilation.inserted_eq_insertedAt common,
      insertion.inserted_eq_insertedAt common]
    apply insertion_denotation_equiv
    intro env
    exact (reference_resolved_body_open_equiv definitions input.definition
      reference referenceCompilation input.body input.bodyAccepted
      (insertion.intrinsicAttachmentAt common)
      (bodyReconstructionCompilation.intrinsicAttachmentAt common) model
      definitionEnv lawful env
      (boundary_argument_values_eq signatures input.body.boundarySignatures
        reference.boundarySignatures
        (bodyReconstructionCompilation.intrinsicAttachmentAt common).positions
        (insertion.intrinsicAttachmentAt common).positions positions env).symm).symm
  exact sourceInserted.trans (replacementEquivalent.trans targetInserted.symm)

private theorem denoteOpen_cast_boundary
    {definitions : List (List Sig)} {left right : List Sig}
    (same : left = right)
    (diagram : OpenDiagram definitions left)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (values : BoundaryEnv pre left) :
    denoteOpen pre definitionEnv diagram values ↔
      denoteOpen pre definitionEnv (same ▸ diagram) (same ▸ values) := by
  cases same
  rfl

private def TheoremSideEntails
    (direction : TheoremDirection) (source target : Prop) : Prop :=
  match direction with
  | .forward => source → target
  | .reverse => target → source

private theorem theorem_application_open_sound
    {definitions : Definitions}
    {source : CheckedDiagram definitions.signatures}
    (input : TheoremApplication.{u} (definitions := definitions) source)
    (sourceCompilation : OpenCompilation input.sourceFragment)
    (sourceCompilationAccepted :
      compileOpen input.sourceFragment = some sourceCompilation)
    (targetCompilation : OpenCompilation input.targetFragment)
    (targetCompilationAccepted :
      compileOpen input.targetFragment = some targetCompilation)
    (sourceAttachment : SpliceAttachment sourceCompilation.openDiagram target)
    (targetAttachment : SpliceAttachment targetCompilation.openDiagram target)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions definitionEnv)
    (env : Env model.toPreModel target)
    (argumentValues :
      input.sourceBoundary ▸ Vars.denote env sourceAttachment.positions =
        input.targetBoundary ▸ Vars.denote env targetAttachment.positions) :
    TheoremSideEntails input.direction
      (denoteOpen model.toPreModel definitionEnv sourceCompilation.openDiagram
        (Vars.denote env sourceAttachment.positions))
      (denoteOpen model.toPreModel definitionEnv targetCompilation.openDiagram
        (Vars.denote env targetAttachment.positions)) := by
  cases input with
  | forward statement orientation occurrence =>
      have sourceExact : sourceCompilation = statement.leftCompilation :=
        Option.some.inj
          (sourceCompilationAccepted.symm.trans
            statement.leftCompilationAccepted)
      have targetExact : targetCompilation = statement.rightCompilation :=
        Option.some.inj
          (targetCompilationAccepted.symm.trans
            statement.rightCompilationAccepted)
      subst sourceCompilation
      subst targetCompilation
      have sourceCast :
          denoteOpen model.toPreModel definitionEnv
              statement.leftCompilation.openDiagram
              (Vars.denote env sourceAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.leftBoundary ▸
                statement.leftCompilation.openDiagram)
              (statement.leftBoundary ▸
                Vars.denote env sourceAttachment.positions) := by
        exact denoteOpen_cast_boundary statement.leftBoundary
          statement.leftCompilation.openDiagram model.toPreModel definitionEnv
          (Vars.denote env sourceAttachment.positions)
      have targetCast :
          denoteOpen model.toPreModel definitionEnv
              statement.rightCompilation.openDiagram
              (Vars.denote env targetAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.rightBoundary ▸
                Vars.denote env targetAttachment.positions) := by
        exact denoteOpen_cast_boundary statement.rightBoundary
          statement.rightCompilation.openDiagram model.toPreModel definitionEnv
          (Vars.denote env targetAttachment.positions)
      have valid := statement.valid model definitionEnv lawful
        (statement.leftBoundary ▸
          Vars.denote env sourceAttachment.positions)
      have targetValues :
          denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.leftBoundary ▸
                Vars.denote env sourceAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.rightBoundary ▸
                Vars.denote env targetAttachment.positions) :=
        iff_of_eq (congrArg
          (denoteOpen model.toPreModel definitionEnv
            (statement.rightBoundary ▸
              statement.rightCompilation.openDiagram))
          argumentValues)
      intro sourceHolds
      exact targetCast.mpr (targetValues.mp (valid (sourceCast.mp sourceHolds)))
  | reverse statement orientation occurrence =>
      have sourceExact : sourceCompilation = statement.rightCompilation :=
        Option.some.inj
          (sourceCompilationAccepted.symm.trans
            statement.rightCompilationAccepted)
      have targetExact : targetCompilation = statement.leftCompilation :=
        Option.some.inj
          (targetCompilationAccepted.symm.trans
            statement.leftCompilationAccepted)
      subst sourceCompilation
      subst targetCompilation
      have sourceCast :
          denoteOpen model.toPreModel definitionEnv
              statement.rightCompilation.openDiagram
              (Vars.denote env sourceAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.rightBoundary ▸
                Vars.denote env sourceAttachment.positions) := by
        exact denoteOpen_cast_boundary statement.rightBoundary
          statement.rightCompilation.openDiagram model.toPreModel definitionEnv
          (Vars.denote env sourceAttachment.positions)
      have targetCast :
          denoteOpen model.toPreModel definitionEnv
              statement.leftCompilation.openDiagram
              (Vars.denote env targetAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.leftBoundary ▸
                statement.leftCompilation.openDiagram)
              (statement.leftBoundary ▸
                Vars.denote env targetAttachment.positions) := by
        exact denoteOpen_cast_boundary statement.leftBoundary
          statement.leftCompilation.openDiagram model.toPreModel definitionEnv
          (Vars.denote env targetAttachment.positions)
      have sourceValues :
          denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.rightBoundary ▸
                Vars.denote env sourceAttachment.positions) ↔
            denoteOpen model.toPreModel definitionEnv
              (statement.rightBoundary ▸
                statement.rightCompilation.openDiagram)
              (statement.leftBoundary ▸
                Vars.denote env targetAttachment.positions) :=
        iff_of_eq (congrArg
          (denoteOpen model.toPreModel definitionEnv
            (statement.rightBoundary ▸
              statement.rightCompilation.openDiagram))
          argumentValues)
      have valid := statement.valid model definitionEnv lawful
        (statement.leftBoundary ▸
          Vars.denote env targetAttachment.positions)
      intro targetHolds
      exact sourceCast.mpr
        (sourceValues.mpr (valid (targetCast.mp targetHolds)))

private theorem insertion_denotation_theorem_sound
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {leftFragment rightFragment : CheckedOpenDiagram definitions}
    {leftCompiled : OpenCompilation leftFragment}
    {rightCompiled : OpenCompilation rightFragment}
    {leftAttachment : ConcreteSpliceAttachment base site leftFragment}
    {rightAttachment : ConcreteSpliceAttachment base site rightFragment}
    (left : InsertionCompilation leftCompiled leftAttachment)
    (right : InsertionCompilation rightCompiled rightAttachment)
    (common : SiteCompilation base site)
    (orientation : Orientation)
    (direction : TheoremDirection)
    (parity : match orientation, direction with
      | .forward, .forward | .backward, .reverse =>
          common.frame.context.cutDepth % 2 = 0
      | .forward, .reverse | .backward, .forward =>
          common.frame.context.cutDepth % 2 = 1)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (openSound : ∀ env : Env pre common.frame.visible.sigs,
      TheoremSideEntails direction
        (denoteOpen pre definitionEnv leftCompiled.openDiagram
          (Vars.denote env (left.intrinsicAttachmentAt common).positions))
        (denoteOpen pre definitionEnv rightCompiled.openDiagram
          (Vars.denote env (right.intrinsicAttachmentAt common).positions))) :
    Directed orientation
      (denoteRegion pre definitionEnv Env.empty (left.insertedAt common))
      (denoteRegion pre definitionEnv Env.empty (right.insertedAt common)) := by
  let leftBody := Region.conjoin common.frame.siteBody
    (intrinsicSplice leftCompiled.openDiagram
      (left.intrinsicAttachmentAt common))
  let rightBody := Region.conjoin common.frame.siteBody
    (intrinsicSplice rightCompiled.openDiagram
      (right.intrinsicAttachmentAt common))
  rw [InsertionCompilation.insertedAt, InsertionCompilation.insertedAt]
  change Directed orientation
    (denoteRegion pre definitionEnv Env.empty
      (common.frame.context.fill leftBody))
    (denoteRegion pre definitionEnv Env.empty
      (common.frame.context.fill rightBody))
  cases direction with
  | forward =>
      have localSound : ∀ env : Env pre common.frame.visible.sigs,
          denoteRegion pre definitionEnv env leftBody →
            denoteRegion pre definitionEnv env rightBody := by
        intro env holds
        simp only [leftBody, rightBody, Region.denote_conjoin,
          denote_intrinsicSplice] at holds ⊢
        exact ⟨holds.1, openSound env holds.2⟩
      cases orientation with
      | forward =>
          exact context_mono common.frame.context pre definitionEnv
            leftBody rightBody parity localSound Env.empty
      | backward =>
          exact context_anti common.frame.context pre definitionEnv
            leftBody rightBody parity localSound Env.empty
  | reverse =>
      have localSound : ∀ env : Env pre common.frame.visible.sigs,
          denoteRegion pre definitionEnv env rightBody →
            denoteRegion pre definitionEnv env leftBody := by
        intro env holds
        simp only [leftBody, rightBody, Region.denote_conjoin,
          denote_intrinsicSplice] at holds ⊢
        exact ⟨holds.1, openSound env holds.2⟩
      cases orientation with
      | forward =>
          exact context_anti common.frame.context pre definitionEnv
            rightBody leftBody parity localSound Env.empty
      | backward =>
          exact context_mono common.frame.context pre definitionEnv
            rightBody leftBody parity localSound Env.empty

private theorem directed_of_iff (orientation : Orientation)
    {source target : Prop} (equivalent : source ↔ target) :
    Directed orientation source target := by
  cases orientation with
  | forward => exact equivalent.mp
  | backward => exact equivalent.mpr

/-- A checked pinned theorem replacement has the replay direction certified by
the cited theorem, including repeated ordered boundary attachments. -/
theorem theorem_application_sound
    {definitions : Definitions}
    (source : CheckedDiagram definitions.signatures)
    (input : TheoremApplication.{u} (definitions := definitions) source)
    (applied : AppliedTheorem.{u} definitions source input)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel definitions.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions definitionEnv) :
    Directed input.orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  have appliedParity := applied.siteDepth_parity
  induction applied using AppliedTheorem.rec
  rename_i sourceCompilation sourceCompilationAccepted targetCompilation
    targetCompilationAccepted removed removedAccepted
    reconstruction reconstructionAccepted reconstructionIso
    reconstructionIsoAccepted reconstructionCompilation
    reconstructionCompilationAccepted legal attachment boundaryTargets
    insertion insertionAccepted result resultAccepted
  change Directed input.orientation
    (denoteChecked model.toPreModel definitionEnv source)
    (denoteChecked model.toPreModel definitionEnv result.checked)
  let reconstructionChecked : CheckedDiagram definitions.signatures :=
    ⟨reconstruction.diagram, reconstructionCompilation.generated_wellFormed⟩
  have sourceInserted :
      denoteChecked model.toPreModel definitionEnv source ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          reconstructionCompilation.inserted :=
    (iso_denotation (left := reconstructionChecked) (right := source)
      reconstructionIso model.toPreModel definitionEnv).symm.trans
        (reconstructionCompilation.generated_checked_denotes_inserted
          model.toPreModel definitionEnv)
  have targetInserted :
      denoteChecked model.toPreModel definitionEnv result.checked ↔
        denoteRegion model.toPreModel definitionEnv Env.empty
          insertion.inserted := by
    rw [spliceRaw_success_checked resultAccepted]
    exact insertion.generated_checked_denotes_inserted
      model.toPreModel definitionEnv
  have signatures : checkedBoundarySigs input.sourceFragment =
      checkedBoundarySigs input.targetFragment :=
    input.sourceBoundary.trans input.targetBoundary.symm
  have boundaryLength : input.sourceFragment.val.boundary.length =
      input.targetFragment.val.boundary.length :=
    input.boundaryLength.symm
  have targets : ∀ position : Fin input.sourceFragment.val.boundary.length,
      reconstruction.target position =
        attachment.target (Fin.cast boundaryLength position) := by
    intro position
    have exactTarget :=
      (boundaryTargets (Fin.cast input.boundaryLength.symm position)).symm
    simpa only [Fin.cast_cast] using exactTarget
  let common := reconstructionCompilation.site
  have positions := insertion_positions_eq reconstructionCompilation insertion
    common signatures boundaryLength targets
  have commonParity : match input.orientation, input.direction with
      | .forward, .forward | .backward, .reverse =>
          common.frame.context.cutDepth % 2 = 0
      | .forward, .reverse | .backward, .forward =>
          common.frame.context.cutDepth % 2 = 1 := by
    simpa [AppliedTheorem.siteDepth] using appliedParity
  have replacementSound : Directed input.orientation
      (denoteRegion model.toPreModel definitionEnv Env.empty
        reconstructionCompilation.inserted)
      (denoteRegion model.toPreModel definitionEnv Env.empty
        insertion.inserted) := by
    rw [reconstructionCompilation.inserted_eq_insertedAt common,
      insertion.inserted_eq_insertedAt common]
    exact insertion_denotation_theorem_sound reconstructionCompilation insertion
      common input.orientation input.direction commonParity model.toPreModel
      definitionEnv (fun env =>
        theorem_application_open_sound input sourceCompilation
          sourceCompilationAccepted targetCompilation targetCompilationAccepted
          (reconstructionCompilation.intrinsicAttachmentAt common)
          (insertion.intrinsicAttachmentAt common) model definitionEnv lawful env
          (boundary_argument_values_eq signatures input.sourceBoundary
            input.targetBoundary
            (reconstructionCompilation.intrinsicAttachmentAt common).positions
            (insertion.intrinsicAttachmentAt common).positions positions env))
  cases orientation : input.orientation with
  | forward =>
      simp only [orientation, Directed] at replacementSound ⊢
      exact fun sourceHolds =>
        targetInserted.mpr (replacementSound (sourceInserted.mp sourceHolds))
  | backward =>
      simp only [orientation, Directed] at replacementSound ⊢
      exact fun targetHolds =>
        sourceInserted.mpr (replacementSound (targetInserted.mp targetHolds))

private theorem directed_trans_equiv (orientation : Orientation)
    {source rawTarget target : Prop}
    (rawSound : Directed orientation source rawTarget)
    (normalized : rawTarget ↔ target) :
    Directed orientation source target := by
  cases orientation with
  | forward => exact fun sourceHolds => normalized.mp (rawSound sourceHolds)
  | backward => exact fun targetHolds => rawSound (normalized.mpr targetHolds)

/-- Every constructor of the exact 34-step language delegates raw semantics to
its owning theorem, then composes the independent deterministic normalization. -/
theorem applyStep_sound
    (definitions : CheckedDefinitions)
    {orientation : Orientation}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    (step : ProofStep.{u} definitions orientation source)
    (model : Model.{u})
    (definitionEnv : DefinitionEnv model.toPreModel
      definitions.intrinsic.signatures)
    (lawful : DefinitionLawful model.toPreModel definitions.intrinsic
      definitionEnv) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv (applyStep step).result) := by
  have rawSound : Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv step.rawTarget) := by
    cases step with
    | refSpawn primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | atomSpawn primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | identityInsert primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | wireJoin primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | erasure primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | wireSever primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | iteration input checked receipt =>
        exact directed_of_iff orientation
          (checked.equivalence model.toPreModel definitionEnv)
    | deiteration input checked receipt =>
        exact directed_of_iff orientation
          (checked.equivalence model.toPreModel definitionEnv)
    | doubleCutIntro input checked receipt =>
        exact directed_of_iff orientation
          (checked.equivalence model.toPreModel definitionEnv)
    | doubleCutElim input checked receipt =>
        exact directed_of_iff orientation
          (checked.equivalence model.toPreModel definitionEnv).symm
    | «theorem» input orientationExact applied receipt =>
        change Directed orientation
          (denoteChecked model.toPreModel definitionEnv source)
          (denoteChecked model.toPreModel definitionEnv applied.target)
        cases orientationExact
        exact theorem_application_sound source input applied model definitionEnv
          lawful
    | vacuousIntro primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | vacuousElim primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | unfold input applied receipt =>
        exact directed_of_iff orientation
          (unfold_sound definitions source input applied model
            definitionEnv lawful)
    | fold input applied receipt =>
        exact directed_of_iff orientation
          (fold_sound definitions source input applied model
            definitionEnv lawful)
    | cutWrap primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | cutAbsorb primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | parallelSplit primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | parallelFuse primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | endsDelete primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | endsSpawn primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | arityShift primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | arityUnshift primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | argPermute primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | argDuplicate primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | argContract primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | argDrop primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | argExtend primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | applyFormal primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | abstractFormal primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | identityLeaf primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | identityAbstract primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | refLeaf primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
    | refAbstract primitive tagExact receipt =>
        exact primitive.sound model definitionEnv
  have normalized :
      denoteChecked model.toPreModel definitionEnv step.rawTarget ↔
        denoteChecked model.toPreModel definitionEnv (applyStep step).result := by
    exact (ConcreteDiagram.normalizeIdentities_sound step.rawTarget
      model.toPreModel definitionEnv).symm
  exact directed_trans_equiv orientation rawSound normalized
