import VisualProof.Diagram.Context
import VisualProof.Diagram.Concrete.Elaborate
import VisualProof.Diagram.Concrete.Subgraph.Occurrence

namespace VisualProof

def mapRegion (map : Fin sourceCount → Fin targetCount) :
    CRegion sourceCount → CRegion targetCount
  | .sheet => .sheet
  | .cut parent => .cut (map parent)

def mapNode (map : Fin sourceCount → Fin targetCount) :
    CNode sourceCount definitionCount → CNode targetCount definitionCount
  | .atom region args => .atom (map region) args
  | .ref region definition args => .ref (map region) definition args
  | .identity region sig arity => .identity (map region) sig arity

namespace DenseList

/-- Executable dense index of a proved list member. -/
def index [DecidableEq α]
    (values : List α) (value : α) (member : value ∈ values) :
    Fin values.length :=
  (Data.Finite.indexOf? values value).get
    (Data.Finite.indexOf?_isSome_iff.mpr member)

theorem get_index [DecidableEq α]
    (values : List α) (value : α) (member : value ∈ values) :
    values.get (index values value member) = value := by
  unfold index
  let hsome : (Data.Finite.indexOf? values value).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr member
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    values.get ((Data.Finite.indexOf? values value).get _) =
        values.get found := congrArg values.get
          (Option.get_of_eq_some hsome hfound)
    _ = value := by
      simpa only [List.get_eq_getElem] using
        Data.Finite.indexOf?_sound hfound

theorem index_get [DecidableEq α]
    (values : List α) (nodup : values.Nodup)
    (position : Fin values.length) :
    index values (values.get position) (List.get_mem values position) =
      position := by
  unfold index
  let hsome :
      (Data.Finite.indexOf? values (values.get position)).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr (List.get_mem values position)
  exact Option.get_of_eq_some hsome
    (Data.Finite.indexOf?_get_eq_some_of_nodup nodup position)

end DenseList

namespace Occurrence

/-- Pull one selected host endpoint back to the dense extracted node carrier. -/
def pullEndpoint?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount) :
    Option (CEndpoint pattern.val.nodeCount) :=
  if selected : endpoint.node ∈ occurrence.selection.nodes then
    some ⟨occurrence.nodeInverse endpoint.node selected, endpoint.port⟩
  else
    none

def pushEndpoint
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint pattern.val.nodeCount) :
    CEndpoint host.val.nodeCount :=
  ⟨occurrence.nodeMap endpoint.node, endpoint.port⟩

@[simp] theorem pushEndpoint_pull
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount)
    (selected : endpoint.node ∈ occurrence.selection.nodes) :
    occurrence.pushEndpoint
        ⟨occurrence.nodeInverse endpoint.node selected, endpoint.port⟩ =
      endpoint := by
  cases endpoint
  simp [pushEndpoint, occurrence.node_right_inverse]

/--
The extracted region table is read from the host. The selected root becomes the
new sheet; every other selected cut pulls its parent back through the supplied
inverse. Impossible malformed branches remain visible to `checkWellFormed`
instead of being hidden behind proof fields.
-/
def extractedRegion
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (region : pattern.val.RegionId) : CRegion pattern.val.regionCount :=
  if region = pattern.val.root then
    .sheet
  else
    match host.val.regions (occurrence.regionMap region) with
    | .sheet => .sheet
    | .cut parent =>
        if selected : parent ∈ occurrence.selection.regions then
          .cut (occurrence.regionInverse parent selected)
        else
          .sheet

/-- Pull a selected node's host-owned home region back densely. -/
def extractedNodeRegion
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.NodeId) : pattern.val.RegionId :=
  occurrence.regionInverse
    (host.val.nodes (occurrence.nodeMap node)).region
    ((occurrence.selection.nodes_exact
      (occurrence.nodeMap node)).mp (occurrence.node_mem node))

/-- Pull a selected node's host-owned constructor and home region back densely. -/
def extractedNode
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : pattern.val.NodeId) :
    CNode pattern.val.regionCount definitions.length :=
  match host.val.nodes (occurrence.nodeMap node) with
  | .atom _ args => .atom (extractedNodeRegion occurrence node) args
  | .ref _ definition args =>
      .ref (extractedNodeRegion occurrence node) definition args
  | .identity _ sig arity =>
      .identity (extractedNodeRegion occurrence node) sig arity

theorem extractedNode_rename
    (occurrence : Occurrence pattern host)
    (node : pattern.val.NodeId) :
    host.val.nodes (occurrence.nodeMap node) =
      mapNode occurrence.regionMap
        (occurrence.extractedNode node) := by
  cases nodeData :
      host.val.nodes (occurrence.nodeMap node) with
  | atom region args =>
      simp [extractedNode, extractedNodeRegion, nodeData, mapNode,
        CNode.region,
        occurrence.region_right_inverse]
  | ref region definition args =>
      simp [extractedNode, extractedNodeRegion, nodeData, mapNode,
        CNode.region,
        occurrence.region_right_inverse]
  | identity region sig arity =>
      simp [extractedNode, extractedNodeRegion, nodeData, mapNode,
        CNode.region,
        occurrence.region_right_inverse]

/--
Pull a selected wire from the host. Only endpoints on selected nodes survive.
Internal scopes are pulled back; every genuinely external scope is pinned to
the extracted sheet.
-/
def extractedWire
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId) :
    CWire pattern.val.regionCount pattern.val.nodeCount :=
  let source := occurrence.wireMap wire
  let hostWire := host.val.wires source
  { sig := hostWire.sig
    scope :=
      if selected : hostWire.scope ∈ occurrence.selection.regions then
        occurrence.regionInverse hostWire.scope selected
      else
        pattern.val.root
    endpoints := hostWire.endpoints.filterMap occurrence.pullEndpoint? }

theorem extractedWire_signature
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId) :
    (host.val.wires (occurrence.wireMap wire)).sig =
      (occurrence.extractedWire wire).sig :=
  rfl

theorem extractedWire_scope_rename
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId)
    (internal :
      (host.val.wires (occurrence.wireMap wire)).scope ∈
        occurrence.selection.regions) :
    (host.val.wires (occurrence.wireMap wire)).scope =
      occurrence.regionMap (occurrence.extractedWire wire).scope := by
  unfold extractedWire
  dsimp only
  rw [occurrence.scope_preserved_internal wire internal]
  simp [occurrence.region_mem,
    occurrence.region_left_inverse]

theorem extractedEndpoint_mem_iff
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId)
    (endpoint : CEndpoint pattern.val.nodeCount) :
    endpoint ∈ (occurrence.extractedWire wire).endpoints ↔
      occurrence.pushEndpoint endpoint ∈
        (host.val.wires (occurrence.wireMap wire)).endpoints := by
  constructor
  · intro member
    have filtered :
        ∃ candidate,
          candidate ∈
              (host.val.wires (occurrence.wireMap wire)).endpoints ∧
            ∃ selected :
                candidate.node ∈ occurrence.selection.nodes,
              (⟨occurrence.nodeInverse candidate.node selected,
                  candidate.port⟩ :
                CEndpoint pattern.val.nodeCount) = endpoint := by
      simpa [extractedWire, pullEndpoint?] using member
    rcases filtered with
      ⟨candidate, incident, selected, equality⟩
    have inverseNode :
        occurrence.nodeInverse candidate.node selected = endpoint.node :=
      congrArg CEndpoint.node equality
    have nodeEquality :
        candidate.node = occurrence.nodeMap endpoint.node := by
      calc
        candidate.node =
            occurrence.nodeMap
              (occurrence.nodeInverse candidate.node selected) :=
          (occurrence.node_right_inverse candidate.node selected).symm
        _ = occurrence.nodeMap endpoint.node :=
          congrArg occurrence.nodeMap inverseNode
    have portEquality : candidate.port = endpoint.port :=
      congrArg CEndpoint.port equality
    simpa [pushEndpoint, ← nodeEquality, ← portEquality] using incident
  · intro incident
    have selected :
        (occurrence.pushEndpoint endpoint).node ∈
          occurrence.selection.nodes := by
      simpa [pushEndpoint] using occurrence.node_mem endpoint.node
    have equality :
        (⟨occurrence.nodeInverse
              (occurrence.pushEndpoint endpoint).node selected,
            (occurrence.pushEndpoint endpoint).port⟩ :
          CEndpoint pattern.val.nodeCount) = endpoint := by
      cases endpoint
      simp [pushEndpoint, occurrence.node_left_inverse]
    have filtered :
        ∃ candidate,
          candidate ∈
              (host.val.wires (occurrence.wireMap wire)).endpoints ∧
            ∃ selected :
                candidate.node ∈ occurrence.selection.nodes,
              (⟨occurrence.nodeInverse candidate.node selected,
                  candidate.port⟩ :
                CEndpoint pattern.val.nodeCount) = endpoint :=
      ⟨occurrence.pushEndpoint endpoint, incident, selected, equality⟩
    simpa [extractedWire, pullEndpoint?] using filtered

/--
Dense host-derived extraction. Counts are the exact occurrence carrier counts,
while every table entry is read through the occurrence maps from the host.
-/
def extractedDiagram
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    ConcreteDiagram definitions.length where
  regionCount := pattern.val.regionCount
  nodeCount := pattern.val.nodeCount
  wireCount := pattern.val.wireCount
  root := pattern.val.root
  regions := occurrence.extractedRegion
  nodes := occurrence.extractedNode
  wires := occurrence.extractedWire

theorem extractedRegion_rename
    (occurrence : Occurrence pattern host)
    (region : pattern.val.RegionId)
    (nonroot : region ≠ pattern.val.root) :
    host.val.regions (occurrence.regionMap region) =
      mapRegion occurrence.regionMap
        (occurrence.extractedRegion region) := by
  cases patternData : pattern.val.regions region with
  | sheet =>
      have checked :=
        (List.all_eq_true.mp pattern.property.only_root_is_sheet)
          region (Data.Finite.mem_allFin region)
      have root : region = pattern.val.root :=
        (of_decide_eq_true checked) patternData
      exact False.elim (nonroot root)
  | cut parent =>
      have hostData :=
        occurrence.parentage region parent patternData
      simp [extractedRegion, nonroot, hostData,
        occurrence.region_mem parent, occurrence.region_left_inverse,
        mapRegion]

/-- Ordered boundary positions are the source wires of genuine crossings. -/
def extractedOpen
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    OpenConcreteDiagram definitions.length where
  diagram := occurrence.extractedDiagram
  boundary := occurrence.boundarySources

def boundarySourceAt
    (occurrence : Occurrence pattern host)
    (position : Fin occurrence.boundarySources.length) :
    pattern.val.WireId :=
  occurrence.boundarySources.get position

theorem boundarySource_external
    (occurrence : Occurrence pattern host)
    (position : Fin occurrence.boundarySources.length) :
    (host.val.wires
      (occurrence.wireMap (occurrence.boundarySourceAt position))).scope ∉
        occurrence.selection.regions := by
  let crossingPosition : Fin occurrence.boundary.length :=
    ⟨position.val, by
      simpa [Occurrence.boundarySources] using position.isLt⟩
  let crossing := occurrence.boundary.get crossingPosition
  have source :
      occurrence.boundarySourceAt position =
        occurrence.wireInverse crossing.wire crossing.wire_selected := by
    unfold boundarySourceAt Occurrence.boundarySources
    simp only [List.get_eq_getElem, List.getElem_map]
    rfl
  rw [source, occurrence.wire_right_inverse]
  exact crossing.scope_external

end Occurrence

/-- Extraction exposes graph-checker and boundary-pinning failures separately. -/
inductive ExtractionError
  | graph (error : WFError)
  | boundaryNotRootScoped
  deriving Repr, DecidableEq

/--
Generate and check a concrete open graph from host tables. This is the sole
public extraction path; malformed generated data is rejected rather than
replaced with the supplied pattern.
-/
def extract {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    Except ExtractionError (CheckedOpenDiagram definitions) := by
  let raw := occurrence.extractedOpen
  match accepted :
      ConcreteDiagram.checkWellFormed definitions raw.diagram with
  | .error error =>
      exact .error (.graph error)
  | .ok checked =>
      if boundary :
          raw.boundary.all (fun wire =>
            decide ((raw.diagram.wires wire).scope =
              raw.diagram.root)) = true then
        apply Except.ok
        refine ⟨raw, ⟨?_, boundary⟩⟩
        have same :=
          ConcreteDiagram.checkWellFormed_preserves_input accepted
        rw [← same]
        exact checked.property
      else
        exact .error .boundaryNotRootScoped

theorem extract_preserves_generated
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (checked : CheckedOpenDiagram definitions)
    (accepted : extract occurrence = .ok checked) :
    checked.val = occurrence.extractedOpen := by
  simp only [extract] at accepted
  split at accepted
  · contradiction
  · split at accepted
    · exact congrArg Subtype.val (Except.ok.inj accepted.symm)
    · contradiction

/-- Ordered signatures exposed by a checked concrete boundary. -/
def checkedBoundarySigs
    (checked : CheckedOpenDiagram definitions) : List Sig :=
  checked.val.boundary.map fun wire =>
    (checked.val.diagram.wires wire).sig

private def resolveExtractedWireIn?
    (diagram : ConcreteDiagram definitionCount) :
    (classes : List diagram.WireId) → (wire : diagram.WireId) →
      Option (Var (classes.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig)
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveExtractedWireIn? diagram tail wire).map .there

namespace ExtractedBoundaryCompiler

@[simp] theorem entries_length
    (variables : Vars ctx args) :
    variables.entries.length = args.length := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp [Vars.entries, induction]

/-- Recover the concrete class wire named by one intrinsic boundary variable. -/
def wireOfVar
    (diagram : ConcreteDiagram definitionCount) :
    {classes : List diagram.WireId} →
      Var (classes.map fun id => (diagram.wires id).sig) sig →
      diagram.WireId
  | head :: _, .here => head
  | _ :: _, .there value => wireOfVar diagram value

/-- Recover a class wire after forgetting a variable's signature index. -/
def wireOfPacked
    (diagram : ConcreteDiagram definitionCount)
    (classes : List diagram.WireId) :
    PackedVar (classes.map fun id => (diagram.wires id).sig) →
      diagram.WireId
  | ⟨_, value⟩ => wireOfVar diagram value

private def liftPacked
    (headSig : Sig) :
    PackedVar ctx → PackedVar (headSig :: ctx)
  | ⟨_, value⟩ => ⟨_, .there value⟩

theorem wireOfVar_member
    (diagram : ConcreteDiagram definitionCount)
    {classes : List diagram.WireId}
    (value : Var
      (classes.map fun id => (diagram.wires id).sig) sig) :
    wireOfVar diagram value ∈ classes := by
  induction classes with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          change head ∈ head :: tail
          exact List.mem_cons_self
      | there tailValue =>
          exact List.mem_cons_of_mem head (induction tailValue)

theorem wireOfPacked_injective
    (diagram : ConcreteDiagram definitionCount)
    (classes : List diagram.WireId)
    (nodup : classes.Nodup) :
    Function.Injective (wireOfPacked diagram classes) := by
  induction classes with
  | nil =>
      intro left
      rcases left with ⟨_, value⟩
      nomatch value
  | cons head tail induction =>
      intro left right same
      rcases left with ⟨leftSig, leftValue⟩
      rcases right with ⟨rightSig, rightValue⟩
      have nodupParts := List.nodup_cons.mp nodup
      cases leftValue with
      | here =>
          cases rightValue with
          | here => rfl
          | there rightTail =>
              exfalso
              apply nodupParts.1
              have equality :
                  head = wireOfVar diagram rightTail := by
                exact same
              rw [equality]
              exact wireOfVar_member diagram rightTail
      | there leftTail =>
          cases rightValue with
          | here =>
              exfalso
              apply nodupParts.1
              have equality :
                  wireOfVar diagram leftTail = head := by
                exact same
              rw [← equality]
              exact wireOfVar_member diagram leftTail
          | there rightTail =>
              have tailSame :
                  wireOfPacked diagram tail
                      (⟨_, leftTail⟩ : PackedVar
                        (tail.map fun id => (diagram.wires id).sig)) =
                    wireOfPacked diagram tail
                      (⟨_, rightTail⟩ : PackedVar
                        (tail.map fun id => (diagram.wires id).sig)) := by
                exact same
              have packedEquality :=
                induction nodupParts.2 tailSame
              exact congrArg
                (liftPacked (diagram.wires head).sig) packedEquality

private theorem resolve_origin
    (diagram : ConcreteDiagram definitionCount)
    (classes : List diagram.WireId)
    (wire : diagram.WireId)
    (value : Var
      (classes.map fun id => (diagram.wires id).sig)
      (diagram.wires wire).sig)
    (compiled :
      resolveExtractedWireIn? diagram classes wire = some value) :
    wireOfVar diagram value = wire := by
  induction classes with
  | nil =>
      simp [resolveExtractedWireIn?] at compiled
  | cons head tail induction =>
      unfold resolveExtractedWireIn? at compiled
      split at compiled
      · rename_i equality
        subst head
        have same : (.here :
            Var ((wire :: tail).map fun id =>
              (diagram.wires id).sig)
              (diagram.wires wire).sig) = value :=
          Option.some.inj compiled
        subst value
        rfl
      · cases recursive :
            resolveExtractedWireIn? diagram tail wire with
        | none =>
            simp [recursive] at compiled
        | some tailValue =>
            have same : Var.there tailValue = value :=
              Option.some.inj (by simpa [recursive] using compiled)
            subst value
            exact induction tailValue recursive

end ExtractedBoundaryCompiler

private def compileExtractedBoundaryFor?
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions) :
    (boundary : List checked.val.diagram.WireId) →
      Option (Vars
        (ConcreteElaboration.openBoundaryClassSigs checked.val)
        (boundary.map fun wire =>
          (checked.val.diagram.wires wire).sig))
  | [] => some .nil
  | wire :: tail => do
      let head ← resolveExtractedWireIn? checked.val.diagram
        (ConcreteElaboration.openBoundaryWires checked.val)
        wire
      let rest ← compileExtractedBoundaryFor? checked tail
      pure (.cons head rest)

private theorem compileExtractedBoundaryFor?_origins
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions) :
    ∀ boundary positions,
      compileExtractedBoundaryFor? checked boundary = some positions →
        positions.entries.map
            (ExtractedBoundaryCompiler.wireOfPacked checked.val.diagram
              (ConcreteElaboration.openBoundaryWires checked.val)) =
          boundary := by
  intro boundary
  induction boundary with
  | nil =>
      intro positions compiled
      simp [compileExtractedBoundaryFor?] at compiled
      subst positions
      rfl
  | cons wire tail induction =>
      intro positions compiled
      unfold compileExtractedBoundaryFor? at compiled
      cases headEquation :
          resolveExtractedWireIn? checked.val.diagram
            (ConcreteElaboration.openBoundaryWires checked.val) wire with
      | none =>
          simp [headEquation] at compiled
      | some head =>
          cases tailEquation :
              compileExtractedBoundaryFor? checked tail with
          | none =>
              simp [headEquation, tailEquation] at compiled
          | some rest =>
              have positionsEquality : (.cons head rest :
                  Vars
                    (ConcreteElaboration.openBoundaryClassSigs checked.val)
                    ((wire :: tail).map fun source =>
                      (checked.val.diagram.wires source).sig)) =
                    positions :=
                Option.some.inj
                  (by simpa [headEquation, tailEquation] using compiled)
              subst positions
              simp only [Vars.entries, List.map_cons]
              change
                ExtractedBoundaryCompiler.wireOfVar
                    checked.val.diagram head ::
                    rest.entries.map
                      (ExtractedBoundaryCompiler.wireOfPacked
                        checked.val.diagram
                        (ConcreteElaboration.openBoundaryWires checked.val)) =
                  wire :: tail
              rw [ExtractedBoundaryCompiler.resolve_origin
                checked.val.diagram
                (ConcreteElaboration.openBoundaryWires checked.val)
                wire head headEquation,
                induction rest tailEquation]

/-- Compile every ordered generated boundary position to its intrinsic class. -/
def compileExtractedBoundary?
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions) :
    Option (Vars
      (ConcreteElaboration.openBoundaryClassSigs checked.val)
      (checkedBoundarySigs checked)) :=
  compileExtractedBoundaryFor? checked checked.val.boundary

theorem compileExtractedBoundary?_origins
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions)
    (positions : Vars
      (ConcreteElaboration.openBoundaryClassSigs checked.val)
      (checkedBoundarySigs checked))
    (compiled :
      compileExtractedBoundary? checked = some positions) :
    positions.entries.map
        (ExtractedBoundaryCompiler.wireOfPacked checked.val.diagram
          (ConcreteElaboration.openBoundaryWires checked.val)) =
      checked.val.boundary := by
  exact compileExtractedBoundaryFor?_origins checked
    checked.val.boundary positions compiled

/--
Structural evidence that the executable concrete compilers accepted extraction.
It stores compiler outputs, never semantic or isomorphism conclusions.
-/
def checkedExtraction
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (wellFormed : occurrence.extractedOpen.WellFormed definitions) :
    CheckedOpenDiagram definitions :=
  ⟨occurrence.extractedOpen, wellFormed⟩

structure ExtractionCompilation
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) where
  wellFormed : occurrence.extractedOpen.WellFormed definitions
  boundary : Vars
    (ConcreteElaboration.openBoundaryClassSigs occurrence.extractedOpen)
    (checkedBoundarySigs (checkedExtraction occurrence wellFormed))
  boundary_compiles :
    compileExtractedBoundary? (checkedExtraction occurrence wellFormed) =
      some boundary
  boundary_surjective :
    ∀ sig
      (fiber : Var
        (ConcreteElaboration.openBoundaryClassSigs occurrence.extractedOpen) sig),
      boundary.Contains fiber
  body : Region definitions
    (ConcreteElaboration.openBoundaryClassSigs occurrence.extractedOpen)
  body_compiles :
    ConcreteElaboration.compileOpenRoot? definitions
      occurrence.extractedOpen = some body

namespace ExtractionCompilation

def checked
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (compiled : ExtractionCompilation occurrence) :
    CheckedOpenDiagram definitions :=
  checkedExtraction occurrence compiled.wellFormed

def openDiagram
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (compiled : ExtractionCompilation occurrence) :
    OpenDiagram definitions (checkedBoundarySigs compiled.checked) where
  classes :=
    ConcreteElaboration.openBoundaryClassSigs occurrence.extractedOpen
  boundary := compiled.boundary
  boundary_surjective := compiled.boundary_surjective
  body := compiled.body

/-- The intrinsic boundary occurrence at one concrete generated position. -/
def boundaryPackedAt
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (compiled : ExtractionCompilation occurrence)
    (position : Fin compiled.checked.val.boundary.length) :
    PackedVar
      (ConcreteElaboration.openBoundaryClassSigs
        occurrence.extractedOpen) :=
  compiled.boundary.entries.get
    ⟨position.val, by
      rw [ExtractedBoundaryCompiler.entries_length]
      simpa only [checkedBoundarySigs, List.length_map] using
        position.isLt⟩

theorem boundaryPackedAt_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (compiled : ExtractionCompilation occurrence)
    (position : Fin compiled.checked.val.boundary.length) :
    ExtractedBoundaryCompiler.wireOfPacked
        compiled.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires compiled.checked.val)
        (compiled.boundaryPackedAt position) =
      compiled.checked.val.boundary.get position := by
  have origins :=
    compileExtractedBoundary?_origins compiled.checked compiled.boundary
      compiled.boundary_compiles
  have atPosition :=
    congrArg (fun values => values[position.val]?) origins
  dsimp at atPosition
  have entriesBound :
      position.val < compiled.boundary.entries.length := by
    rw [ExtractedBoundaryCompiler.entries_length]
    simpa only [checkedBoundarySigs, List.length_map] using
      position.isLt
  have mappedBound :
      position.val <
        (compiled.boundary.entries.map
          (ExtractedBoundaryCompiler.wireOfPacked
            compiled.checked.val.diagram
            (ConcreteElaboration.openBoundaryWires
          compiled.checked.val))).length := by
    simpa only [List.length_map] using entriesBound
  have leftLookup :=
    List.getElem?_eq_getElem mappedBound
  have rightLookup :=
    List.getElem?_eq_getElem position.isLt
  have exactPosition := Option.some.inj
    (leftLookup.symm.trans (atPosition.trans rightLookup))
  simpa only [boundaryPackedAt, List.get_eq_getElem,
    List.getElem_map] using exactPosition

/--
The compiled intrinsic boundary classes reflect exactly the concrete equality
classes at every ordered generated position.
-/
theorem boundaryPackedAt_eq_iff
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (compiled : ExtractionCompilation occurrence)
    (left right : Fin compiled.checked.val.boundary.length) :
    compiled.boundaryPackedAt left =
        compiled.boundaryPackedAt right ↔
      compiled.checked.val.boundary.get left =
        compiled.checked.val.boundary.get right := by
  constructor
  · intro same
    have mapped := congrArg
      (ExtractedBoundaryCompiler.wireOfPacked
        compiled.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires compiled.checked.val))
      same
    simpa [compiled.boundaryPackedAt_origin left,
      compiled.boundaryPackedAt_origin right] using mapped
  · intro same
    apply ExtractedBoundaryCompiler.wireOfPacked_injective
      compiled.checked.val.diagram
      (ConcreteElaboration.openBoundaryWires compiled.checked.val)
      (Data.Finite.eraseDups_nodup _)
    rw [compiled.boundaryPackedAt_origin left,
      compiled.boundaryPackedAt_origin right, same]

end ExtractionCompilation

namespace Removal

/-- Regions retained by removal: the outside frame plus the selected root site. -/
def regions (occurrence : Occurrence pattern host) :
    List host.val.RegionId :=
  host.val.regionsList.filter fun region =>
    decide (region ∉ occurrence.selection.regions ∨
      region = occurrence.selection.root)

/-- Nodes retained by removal are exactly those outside the closed selection. -/
def nodes (occurrence : Occurrence pattern host) :
    List host.val.NodeId :=
  host.val.nodesList.filter fun node =>
    decide (node ∉ occurrence.selection.nodes)

/-- Wires quantified outside the selection form the complement and its pins. -/
def wires (occurrence : Occurrence pattern host) :
    List host.val.WireId :=
  host.val.wiresList.filter fun wire =>
    decide ((host.val.wires wire).scope ∉ occurrence.selection.regions)

theorem boundarySource_retained
    (occurrence : Occurrence pattern host)
    (position : Fin occurrence.boundarySources.length) :
    occurrence.wireMap (occurrence.boundarySourceAt position) ∈
      wires occurrence := by
  simp [wires, ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
    occurrence.boundarySource_external position]

theorem regions_nodup (occurrence : Occurrence pattern host) :
    (regions occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.regionCount |>.filter _

theorem nodes_nodup (occurrence : Occurrence pattern host) :
    (nodes occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.nodeCount |>.filter _

theorem wires_nodup (occurrence : Occurrence pattern host) :
    (wires occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.wireCount |>.filter _

theorem selected_root_mem
    (occurrence : Occurrence pattern host) :
    occurrence.selection.root ∈ regions occurrence := by
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin, occurrence.selection.root_mem]

theorem host_root_mem
    (occurrence : Occurrence pattern host) :
    host.val.root ∈ regions occurrence := by
  simp only [regions, List.mem_filter]
  refine ⟨Data.Finite.mem_allFin _, ?_⟩
  apply decide_eq_true
  exact occurrence.selection.host_root_retained

def regionIndex (occurrence : Occurrence pattern host)
    (region : host.val.RegionId)
    (member : region ∈ regions occurrence) :
    Fin (regions occurrence).length :=
  DenseList.index (regions occurrence) region member

def nodeIndex (occurrence : Occurrence pattern host)
    (node : host.val.NodeId)
    (member : node ∈ nodes occurrence) :
    Fin (nodes occurrence).length :=
  DenseList.index (nodes occurrence) node member

def wireIndex (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (member : wire ∈ wires occurrence) :
    Fin (wires occurrence).length :=
  DenseList.index (wires occurrence) wire member

def sourceRegion (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) : host.val.RegionId :=
  (regions occurrence).get region

def sourceNode (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) : host.val.NodeId :=
  (nodes occurrence).get node

def sourceWire (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) : host.val.WireId :=
  (wires occurrence).get wire

@[simp] theorem sourceRegion_regionIndex
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId)
    (member : region ∈ regions occurrence) :
    sourceRegion occurrence (regionIndex occurrence region member) = region :=
  DenseList.get_index _ _ _

@[simp] theorem sourceNode_nodeIndex
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId)
    (member : node ∈ nodes occurrence) :
    sourceNode occurrence (nodeIndex occurrence node member) = node :=
  DenseList.get_index _ _ _

@[simp] theorem sourceWire_wireIndex
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (member : wire ∈ wires occurrence) :
    sourceWire occurrence (wireIndex occurrence wire member) = wire :=
  DenseList.get_index _ _ _

@[simp] theorem regionIndex_sourceRegion
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    regionIndex occurrence (sourceRegion occurrence region)
      (List.get_mem _ region) = region :=
  DenseList.index_get _ (regions_nodup occurrence) region

@[simp] theorem nodeIndex_sourceNode
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    nodeIndex occurrence (sourceNode occurrence node)
      (List.get_mem _ node) = node :=
  DenseList.index_get _ (nodes_nodup occurrence) node

@[simp] theorem wireIndex_sourceWire
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    wireIndex occurrence (sourceWire occurrence wire)
      (List.get_mem _ wire) = wire :=
  DenseList.index_get _ (wires_nodup occurrence) wire

theorem parent_mem_of_sourceRegion_cut
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length)
    (parent : host.val.RegionId)
    (regionData :
      host.val.regions (sourceRegion occurrence region) = .cut parent) :
    parent ∈ regions occurrence := by
  have member := List.get_mem (regions occurrence) region
  have retainedCase :
      sourceRegion occurrence region ∉ occurrence.selection.regions ∨
        sourceRegion occurrence region = occurrence.selection.root :=
    of_decide_eq_true (List.mem_filter.mp member).2
  have parentOutside : parent ∉ occurrence.selection.regions := by
    rcases retainedCase with outside | root
    · intro parentSelected
      have childMember :
          sourceRegion occurrence region ∈ host.val.childrenOf parent := by
        simp [ConcreteDiagram.childrenOf, ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin, regionData]
      exact outside
        (occurrence.selection.descendants_closed parent parentSelected
          (sourceRegion occurrence region) childMember)
    · exact occurrence.selection.root_parent_external parent
        (root ▸ regionData)
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin, parentOutside]

private def endpoint?
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount) :
    Option (CEndpoint (nodes occurrence).length) :=
  if retained : endpoint.node ∈ nodes occurrence then
    some ⟨nodeIndex occurrence endpoint.node retained, endpoint.port⟩
  else
    none

def sourceEndpoint
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint (nodes occurrence).length) :
    CEndpoint host.val.nodeCount :=
  ⟨sourceNode occurrence endpoint.node, endpoint.port⟩

@[simp] theorem sourceEndpoint_index
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount)
    (retained : endpoint.node ∈ nodes occurrence) :
    sourceEndpoint occurrence
        ⟨nodeIndex occurrence endpoint.node retained, endpoint.port⟩ =
      endpoint := by
  cases endpoint
  simp [sourceEndpoint, sourceNode_nodeIndex]

private def regionTable
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    CRegion (regions occurrence).length :=
  match host.val.regions (sourceRegion occurrence region) with
  | .sheet => .sheet
  | .cut parent =>
      if retained : parent ∈ regions occurrence then
        .cut (regionIndex occurrence parent retained)
      else
        .sheet

private theorem sourceNode_region_mem
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    (host.val.nodes (sourceNode occurrence node)).region ∈
      regions occurrence := by
  have outside :
      sourceNode occurrence node ∉ occurrence.selection.nodes :=
    of_decide_eq_true
      (List.mem_filter.mp (List.get_mem (nodes occurrence) node)).2
  have regionOutside :
      (host.val.nodes (sourceNode occurrence node)).region ∉
        occurrence.selection.regions := by
    intro selected
    exact outside
      ((occurrence.selection.nodes_exact
        (sourceNode occurrence node)).mpr selected)
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin, regionOutside]

private def nodeRegion
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    Fin (regions occurrence).length :=
  regionIndex occurrence
    (host.val.nodes (sourceNode occurrence node)).region
    (sourceNode_region_mem occurrence node)

private def nodeTable
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    CNode (regions occurrence).length definitions.length :=
  match host.val.nodes (sourceNode occurrence node) with
  | .atom _ args => .atom (nodeRegion occurrence node) args
  | .ref _ definition args =>
      .ref (nodeRegion occurrence node) definition args
  | .identity _ sig arity =>
      .identity (nodeRegion occurrence node) sig arity

private theorem sourceWire_scope_mem
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).scope ∈
      regions occurrence := by
  have external :
      (host.val.wires (sourceWire occurrence wire)).scope ∉
        occurrence.selection.regions :=
    of_decide_eq_true
      (List.mem_filter.mp (List.get_mem (wires occurrence) wire)).2
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin, external]

private def wireScope
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    Fin (regions occurrence).length :=
  regionIndex occurrence
    (host.val.wires (sourceWire occurrence wire)).scope
    (sourceWire_scope_mem occurrence wire)

private def wireTable
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    CWire (regions occurrence).length (nodes occurrence).length :=
  let source := sourceWire occurrence wire
  let hostWire := host.val.wires source
  { sig := hostWire.sig
    scope := wireScope occurrence wire
    endpoints := hostWire.endpoints.filterMap (endpoint? occurrence) }

/-- The generated host complement with a retained, emptied region as splice site. -/
def diagram
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    ConcreteDiagram definitions.length where
  regionCount := (regions occurrence).length
  nodeCount := (nodes occurrence).length
  wireCount := (wires occurrence).length
  root := regionIndex occurrence host.val.root (host_root_mem occurrence)
  regions := regionTable occurrence
  nodes := nodeTable occurrence
  wires := wireTable occurrence

theorem diagramRegion_rename
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    host.val.regions (sourceRegion occurrence region) =
      mapRegion (sourceRegion occurrence)
        ((diagram occurrence).regions region) := by
  cases regionData :
      host.val.regions (sourceRegion occurrence region) with
  | sheet =>
      simp [diagram, regionTable, regionData, mapRegion]
  | cut parent =>
      have retained :=
        parent_mem_of_sourceRegion_cut occurrence region parent regionData
      simp [diagram, regionTable, regionData, retained, mapRegion]

theorem diagramNode_rename
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    host.val.nodes (sourceNode occurrence node) =
      mapNode (sourceRegion occurrence)
        ((diagram occurrence).nodes node) := by
  cases nodeData :
      host.val.nodes (sourceNode occurrence node) with
  | atom region args =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]
  | ref region definition args =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]
  | identity region sig arity =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]

theorem diagramWire_signature
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).sig =
      ((diagram occurrence).wires wire).sig :=
  rfl

theorem diagramWire_scope_rename
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).scope =
      sourceRegion occurrence ((diagram occurrence).wires wire).scope := by
  simp [diagram, wireTable, wireScope, sourceRegion_regionIndex]

theorem diagramEndpoint_mem_iff
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length)
    (endpoint : CEndpoint (nodes occurrence).length) :
    endpoint ∈ ((diagram occurrence).wires wire).endpoints ↔
      sourceEndpoint occurrence endpoint ∈
        (host.val.wires (sourceWire occurrence wire)).endpoints := by
  constructor
  · intro member
    change
      endpoint ∈
        List.filterMap (endpoint? occurrence)
          (host.val.wires
            (sourceWire occurrence wire)).endpoints at member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, incident, mapped⟩
    unfold endpoint? at mapped
    split at mapped
    · rename_i retained
      have equality :
          (⟨nodeIndex occurrence candidate.node retained,
              candidate.port⟩ :
            CEndpoint (nodes occurrence).length) = endpoint :=
        Option.some.inj mapped
      exact (by
        have indexEquality :
            nodeIndex occurrence candidate.node retained = endpoint.node :=
          congrArg CEndpoint.node equality
        have nodeEquality :
            candidate.node = sourceNode occurrence endpoint.node := by
          calc
            candidate.node =
                sourceNode occurrence
                  (nodeIndex occurrence candidate.node retained) :=
              (sourceNode_nodeIndex occurrence candidate.node retained).symm
            _ = sourceNode occurrence endpoint.node :=
              congrArg (sourceNode occurrence) indexEquality
        have portEquality : candidate.port = endpoint.port :=
          congrArg CEndpoint.port equality
        simpa [sourceEndpoint, ← nodeEquality, ← portEquality] using incident)
    · contradiction
  · intro incident
    have retained :
        (sourceEndpoint occurrence endpoint).node ∈ nodes occurrence := by
      change sourceNode occurrence endpoint.node ∈ nodes occurrence
      exact List.get_mem (nodes occurrence) endpoint.node
    have equality :
        (⟨nodeIndex occurrence
              (sourceEndpoint occurrence endpoint).node retained,
            (sourceEndpoint occurrence endpoint).port⟩ :
          CEndpoint (nodes occurrence).length) = endpoint := by
      cases endpoint
      simp [sourceEndpoint, nodeIndex_sourceNode]
    change
      endpoint ∈
        List.filterMap (endpoint? occurrence)
          (host.val.wires
            (sourceWire occurrence wire)).endpoints
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint occurrence endpoint, incident, ?_⟩
    unfold endpoint?
    simp only [retained, dite_true]
    exact congrArg some equality

/-- Dense identifier of the retained concrete hole region. -/
def site (occurrence : Occurrence pattern host) :
    (diagram occurrence).RegionId :=
  regionIndex occurrence occurrence.selection.root
    (selected_root_mem occurrence)

end Removal

/-- Successful removal certifies only the generated complement candidate. -/
structure RemovalResult
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) : Type where
  wellFormed : (Removal.diagram occurrence).WellFormed definitions

namespace RemovalResult

def complement
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    CheckedDiagram definitions :=
  ⟨Removal.diagram occurrence, result.wellFormed⟩

def site
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    (Removal.diagram occurrence).RegionId :=
  Removal.site occurrence

end RemovalResult

/-- Generate and validate the actual host complement. -/
def remove
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    Except WFError (RemovalResult occurrence) := by
  match accepted :
      ConcreteDiagram.checkWellFormed definitions (Removal.diagram occurrence) with
  | .error error => exact .error error
  | .ok checked =>
      apply Except.ok
      refine ⟨?_⟩
      have same :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      rw [← same]
      exact checked.property

end VisualProof
