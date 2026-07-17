import VisualProof.Diagram.Concrete.Subgraph.Splice.Removal

namespace VisualProof.Diagram

namespace Splice

namespace Examples

open DecompositionExamples
open ConcreteExamples

def wireFrame : ConcreteDiagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 3
  root := 0
  regions := fun _ => .sheet
  nodes := nofun
  wires := fun _ => { scope := 0, endpoints := [] }

theorem wireFrame_check :
    ∃ checked, checkWellFormed [] wireFrame = .ok checked ∧
      checked.val = wireFrame := by
  refine ⟨_, rfl, rfl⟩

def checkedWireFrame : CheckedDiagram [] :=
  ⟨wireFrame, checkWellFormed_iff.mp wireFrame_check⟩

def aliasPattern : OpenConcreteDiagram where
  diagram := {
    regionCount := 1
    nodeCount := 0
    wireCount := 2
    root := 0
    regions := fun _ => .sheet
    nodes := nofun
    wires := fun _ => { scope := 0, endpoints := [] }
  }
  boundary := [0, 0, 1, 1]

theorem aliasPatternDiagram_check :
    ∃ checked, checkWellFormed [] aliasPattern.diagram = .ok checked ∧
      checked.val = aliasPattern.diagram := by
  refine ⟨_, rfl, rfl⟩

def checkedAliasPattern : CheckedOpenDiagram [] :=
  ⟨aliasPattern, {
    diagram_well_formed := checkWellFormed_iff.mp aliasPatternDiagram_check
    boundary_is_root_scoped := by
      intro wire hwire
      simp [aliasPattern]
  }⟩

def aliasSpine : BinderSpine aliasPattern.diagram where
  proxyCount := 0
  proxy := nofun
  arity := nofun
  bodyContainer := ⟨0, by simp [aliasPattern]⟩
  proxy_injective := nofun
  proxy_ne_root := nofun
  body_eq_root_of_empty := by intro; rfl
  body_eq_terminal_of_nonempty := by intro h; contradiction
  proxy_region := nofun

def aliasTerminalBody : aliasSpine.TerminalBodyContract aliasPattern where
  root_direct_child := by intro h; contradiction
  nonterminal_direct_child := nofun
  root_has_no_nodes := by intro h; contradiction
  nonterminal_has_no_nodes := nofun
  root_has_no_nonboundary_wires := by intro h; contradiction
  nonterminal_has_no_nonboundary_wires := nofun
  boundary_is_root_scoped := by
    intro wire hwire
    simp [aliasPattern]

def transitiveInput : Input [] where
  frame := checkedWireFrame
  pattern := checkedAliasPattern
  site := ⟨0, by simp [checkedWireFrame, wireFrame]⟩
  attachment := fun position =>
    if position.val = 0 then ⟨0, by simp [checkedWireFrame, wireFrame]⟩
    else if position.val = 1 then ⟨1, by simp [checkedWireFrame, wireFrame]⟩
    else if position.val = 2 then ⟨1, by simp [checkedWireFrame, wireFrame]⟩
    else ⟨2, by simp [checkedWireFrame, wireFrame]⟩
  binderSpine := aliasSpine
  terminalBody := aliasTerminalBody
  binderTarget := nofun

theorem transitiveInput_admissible : transitiveInput.Admissible := by
  native_decide

/-- Repeated positions for the first boundary identity coalesce host wires 0/1. -/
theorem repeated_alias_coalesces :
    transitiveInput.attachmentPartition.related
      ⟨0, by native_decide⟩ ⟨1, by native_decide⟩ = true := by
  native_decide

/-- The second repeated identity shares host wire 1, closing 0/1/2 transitively. -/
theorem transitive_alias_closure :
    transitiveInput.attachmentPartition.related
        ⟨0, by native_decide⟩ ⟨2, by native_decide⟩ = true ∧
      transitiveInput.wireQuotient.count = 1 := by
  native_decide

def sharedPattern : OpenConcreteDiagram where
  diagram := aliasPattern.diagram
  boundary := [⟨0, by simp [aliasPattern]⟩, ⟨1, by simp [aliasPattern]⟩]

def checkedSharedPattern : CheckedOpenDiagram [] :=
  ⟨sharedPattern, {
    diagram_well_formed := checkWellFormed_iff.mp aliasPatternDiagram_check
    boundary_is_root_scoped := by
      intro wire hwire
      simp [sharedPattern, aliasPattern]
  }⟩

def sharedSpine : BinderSpine sharedPattern.diagram := aliasSpine

def sharedTerminalBody : sharedSpine.TerminalBodyContract sharedPattern where
  root_direct_child := by intro h; contradiction
  nonterminal_direct_child := nofun
  root_has_no_nodes := by intro h; contradiction
  nonterminal_has_no_nodes := nofun
  root_has_no_nonboundary_wires := by intro h; contradiction
  nonterminal_has_no_nonboundary_wires := nofun
  boundary_is_root_scoped := by
    intro wire hwire
    simp [sharedPattern, aliasPattern]

def sharedHostInput : Input [] where
  frame := checkedWireFrame
  pattern := checkedSharedPattern
  site := ⟨0, by simp [checkedWireFrame, wireFrame]⟩
  attachment := fun _ => ⟨0, by simp [checkedWireFrame, wireFrame]⟩
  binderSpine := sharedSpine
  terminalBody := sharedTerminalBody
  binderTarget := nofun

/-- Distinct pattern identities may share host wire 0 without relating host 0/1. -/
theorem shared_host_adds_no_cross_identity_equation :
    sharedHostInput.attachmentPartition.related
      ⟨0, by native_decide⟩ ⟨1, by native_decide⟩ = false := by
  native_decide

theorem transitive_splice_succeeds :
    ∃ result, Input.spliceChecked [] transitiveInput = .ok result :=
  transitiveInput.spliceChecked_complete transitiveInput_admissible

def nestedPattern : CheckedOpenDiagram [] :=
  ⟨validNested.extractOpenRaw nestedSelection nestedLayout,
    ConcreteDiagram.extractOpenRaw_wellFormed
      nestedHost nestedSelection nestedLayout⟩

def nestedSpliceInput : Input [] where
  frame := nestedHost
  pattern := nestedPattern
  site := nestedRegion 2
  attachment := fun _ => nestedWire
  binderSpine := nestedSpine
  terminalBody := ConcreteDiagram.extractedBinderSpine_terminalBodyContract
    validNested nestedSelection nestedLayout
  binderTarget := fun _ => nestedRegion 1

theorem nestedSpliceInput_admissible : nestedSpliceInput.Admissible := by
  native_decide

def nestedPlugLayout : Input.PlugLayout nestedSpliceInput :=
  nestedSpliceInput.plugLayout

/-- The extracted proxy binder is reattached to its aligned host bubble. -/
theorem proxy_binder_reattached :
    nestedPlugLayout.plugRaw.nodes
        (nestedPlugLayout.patternNode (nestedNode 1)) =
      CNode.atom (nestedPlugLayout.frameRegion (nestedRegion 2))
        (nestedPlugLayout.frameRegion (nestedRegion 1)) := by
  simp only [Input.PlugLayout.plugRaw]
  rw [nestedPlugLayout.plugNode_patternNode]
  change nestedPlugLayout.mapPatternNode
    ((validNested.extractDiagramRaw nestedSelection nestedLayout).nodes
      (nestedNode 1)) = _
  rw [nested_terminal_proxy_contract.2.2]
  simp only [Input.PlugLayout.mapPatternNode]
  change CNode.atom
      (nestedPlugLayout.bodyRegion
        nestedSpliceInput.binderSpine.bodyContainer)
      (nestedPlugLayout.binderRegion
        (nestedSpliceInput.binderSpine.proxy ⟨0, by decide⟩)) = _
  rw [nestedPlugLayout.bodyRegion_bodyContainer,
    nestedPlugLayout.binderRegion_proxy]
  rfl

theorem proxy_binder_splice_succeeds :
    ∃ result, Input.spliceChecked [] nestedSpliceInput = .ok result :=
  nestedSpliceInput.spliceChecked_complete nestedSpliceInput_admissible

end Examples

end Splice

end VisualProof.Diagram
