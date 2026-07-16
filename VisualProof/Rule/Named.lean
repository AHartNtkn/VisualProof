import VisualProof.Rule.Comprehension

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

def relationArguments? (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (arity : Nat) :
    Option (Fin arity → Fin input.val.wireCount) :=
  sequenceFin fun index =>
    ConcreteElaboration.endpointOwner? input.val
      { node := node, port := .arg index }

private def namedSpliceError : Diagram.Splice.Input.Error → StepError
  | .attachmentNotVisible => .boundaryMismatch
  | .duplicateBinderTarget => .binderEscape
  | .binderKindOrArityMismatch => .binderKindOrArityMismatch
  | .binderDoesNotEncloseSite => .binderDoesNotEnclose
  | .resultNotWellFormed error => .resultNotWellFormed error

def relUnfoldInput (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (payload : RelUnfoldPayload input node)
    (arguments : Fin payload.arity → Fin input.val.wireCount) :
    Diagram.Splice.Input signature where
  frame := input
  pattern := payload.body
  site := payload.region
  attachment := fun position =>
    arguments (Fin.cast payload.body_arity position)
  binderSpine := payload.binderSpine
  terminalBody := payload.terminalBody
  binderTarget := fun index =>
    Fin.elim0 (Fin.cast payload.closed index)

def singletonNodeRequest {signature : List Nat}
    (spliceInput : Diagram.Splice.Input signature)
    (layout : Diagram.Splice.Input.PlugLayout spliceInput)
    (region : Fin spliceInput.frame.val.regionCount)
    (node : Fin spliceInput.frame.val.nodeCount) :
    SelectionRequest layout.plugRaw where
  anchor := layout.frameRegion region
  childRoots := []
  directNodes := [layout.frameNode node]
  explicitWires := []

/-- Inline the checked body of one named-reference node, then remove the node. -/
def applyRelUnfold (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (payload : RelUnfoldPayload input node) :
    Except StepError (StepReceipt input) :=
  match relationArguments? input node payload.arity with
  | none => .error .boundaryMismatch
  | some arguments =>
      let spliceInput := relUnfoldInput input node payload arguments
      match hinput : Diagram.Splice.Input.checkInput spliceInput with
      | .error error => .error (namedSpliceError error)
      | .ok checkedInput =>
          have hadmissible : spliceInput.Admissible :=
            (Diagram.Splice.Input.checkInput_sound hinput).2
          let layout := spliceInput.plugLayout
          let spliced : CheckedDiagram signature :=
            ⟨layout.plugRaw,
              Diagram.Splice.Input.PlugLayout.plugRaw_wellFormed
                signature spliceInput layout
                hadmissible⟩
          match checkSelection
              (singletonNodeRequest spliceInput layout payload.region node) with
          | .error _ => .error .operationRejected
          | .ok selection =>
              let result : CheckedDiagram signature :=
                ⟨spliced.val.removeRaw selection {},
                  ConcreteDiagram.removeRaw_wellFormed spliced selection {}⟩
              .ok {
                result := result
                provenance := (spliceFrameWireProvenance spliceInput).compose
                  (removeWireProvenance spliced selection)
                interface := (spliceFrameInterfaceTransport spliceInput).compose
                  (removeWireInterfaceTransport spliced selection)
              }

theorem applyRelUnfold_success {signature : List Nat}
    {input : CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : RelUnfoldPayload input node}
    {result : StepReceipt input}
    (happly : applyRelUnfold input node payload = .ok result) :
    ∃ arguments : Fin payload.arity → Fin input.val.wireCount,
      relationArguments? input node payload.arity = some arguments ∧
      let spliceInput := relUnfoldInput input node payload arguments
      spliceInput.Admissible ∧
        ∃ mapped : CheckedSelection spliceInput.plugLayout.plugRaw,
          checkSelection (singletonNodeRequest spliceInput
              spliceInput.plugLayout payload.region node) = .ok mapped ∧
            result.result.val =
              spliceInput.plugLayout.plugRaw.removeRaw mapped {} := by
  unfold applyRelUnfold at happly
  split at happly <;> try contradiction
  rename_i arguments harguments
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i checkedInput hinput
  split at happly <;> try contradiction
  rename_i mapped hmapped
  cases happly
  refine ⟨arguments, harguments,
    (Diagram.Splice.Input.checkInput_sound hinput).2, mapped, hmapped, ?_⟩
  rfl

theorem applyRelUnfold_realizes {signature : List Nat}
    {input : CheckedDiagram signature}
    {node : Fin input.val.nodeCount}
    {payload : RelUnfoldPayload input node}
    {result : StepReceipt input}
    (happly : applyRelUnfold input node payload = .ok result) :
    ∃ arguments : Fin payload.arity → Fin input.val.wireCount,
      relationArguments? input node payload.arity = some arguments ∧
      let spliceInput := relUnfoldInput input node payload arguments
      ∃ checkedInput,
        ∃ hinput : Diagram.Splice.Input.checkInput spliceInput =
            .ok checkedInput,
          let hadmissible : spliceInput.Admissible :=
            (Diagram.Splice.Input.checkInput_sound hinput).2
          let layout := spliceInput.plugLayout
          let spliced : CheckedDiagram signature :=
            ⟨layout.plugRaw,
              Diagram.Splice.Input.PlugLayout.plugRaw_wellFormed
                signature spliceInput layout hadmissible⟩
          ∃ mapped : CheckedSelection layout.plugRaw,
            checkSelection (singletonNodeRequest spliceInput layout
                payload.region node) = .ok mapped ∧
              result.Realizes (spliced.val.removeRaw mapped {})
                ((spliceFrameWireProvenance spliceInput).compose
                  (removeWireProvenance spliced mapped))
                ((spliceFrameInterfaceTransport spliceInput).compose
                  (removeWireInterfaceTransport spliced mapped)) := by
  unfold applyRelUnfold at happly
  split at happly <;> try contradiction
  rename_i arguments harguments
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i checkedInput hinput
  split at happly <;> try contradiction
  rename_i mapped hmapped
  cases happly
  refine ⟨arguments, harguments, checkedInput, hinput, mapped, hmapped,
    rfl, ?_, ?_⟩
  · intro wire
    simp
  · intro wire
    simp

private def foldLiftEndpoint (endpoint : CEndpoint nodes) :
    CEndpoint (nodes + 1) :=
  { node := endpoint.node.castSucc, port := endpoint.port }

private def foldArgumentEndpoints (mapped : Fin arity → Fin wires)
    (wire : Fin wires) : List (CEndpoint (nodes + 1)) :=
  (allFin arity).filterMap fun index =>
    if mapped index = wire then
      some { node := Fin.last nodes, port := .arg index }
    else none

private def relFoldRaw? (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (definition : Nat)
    (args : List (Fin input.val.wireCount)) :
    Option { raw : ConcreteDiagram //
      raw.wireCount = ({} : FrameDomains input.val selection).wires.count } := do
  let domains : FrameDomains input.val selection := {}
  let frame := input.val.removeRaw selection domains
  let region ← domains.regions.index? selection.val.anchor
  let mapped ← sequenceFin fun index =>
    domains.wires.index? (args.get index)
  pure ⟨{
    regionCount := frame.regionCount
    nodeCount := frame.nodeCount + 1
    wireCount := frame.wireCount
    root := frame.root
    regions := frame.regions
    nodes := Fin.lastCases (.named region definition args.length)
      (fun node => match frame.nodes node with
        | .term owner freePorts term =>
            .term owner freePorts term
        | .atom owner binder => .atom owner binder
        | .named owner prior arity => .named owner prior arity)
    wires := fun wire =>
      { scope := (frame.wires wire).scope
        endpoints := (frame.wires wire).endpoints.map foldLiftEndpoint ++
          foldArgumentEndpoints (nodes := frame.nodeCount) mapped wire }
  }, rfl⟩

private def relFoldWireProvenance (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (definition : Nat)
    (args : List (Fin input.val.wireCount)) (raw : ConcreteDiagram)
    (hraw : (relFoldRaw? input selection definition args).map Subtype.val =
      some raw) : WireProvenance input.val raw :=
  let domains : FrameDomains input.val selection := {}
  WireProvenance.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

private def relFoldInterfaceTransport (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (definition : Nat)
    (args : List (Fin input.val.wireCount)) (raw : ConcreteDiagram)
    (hraw : (relFoldRaw? input selection definition args).map Subtype.val =
      some raw) : InterfaceTransport input.val raw :=
  let domains : FrameDomains input.val selection := {}
  InterfaceTransport.survivors input.val raw domains.wires (by
    rw [Option.map_eq_some_iff] at hraw
    obtain ⟨witness, _, equality⟩ := hraw
    subst raw
    exact witness.property)

/-- Contract an exact pinned occurrence to one named-reference node. -/
def applyRelFold (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) (definition : Nat)
    (args : List (Fin input.val.wireCount))
    (_payload : RelFoldPayload input selection definition args) :
    Except StepError (StepReceipt input) :=
  match hraw : (relFoldRaw? input selection definition args).map Subtype.val with
  | none => .error .boundaryMismatch
  | some raw =>
      match hcheck : checkWellFormed signature raw with
      | .error error => .error (.resultNotWellFormed error)
      | .ok result => .ok (StepReceipt.ofChecked input raw
          (relFoldWireProvenance input selection definition args raw hraw)
          (relFoldInterfaceTransport input selection definition args raw hraw)
          result hcheck)

theorem applyRelFold_success_shape
    (happly : applyRelFold input selection definition args payload = .ok result) :
    ∃ raw, (relFoldRaw? input selection definition args).map Subtype.val =
        some raw ∧ result.result.val = raw := by
  unfold applyRelFold at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, checkWellFormed_preserves_input hcheck⟩

theorem applyRelFold_realizes
    (happly : applyRelFold input selection definition args payload = .ok result) :
    ∃ raw,
      ∃ hraw : (relFoldRaw? input selection definition args).map Subtype.val =
        some raw,
        result.Realizes raw
          (relFoldWireProvenance input selection definition args raw hraw)
          (relFoldInterfaceTransport input selection definition args raw
            hraw) := by
  unfold applyRelFold at happly
  split at happly <;> try contradiction
  rename_i raw hraw
  split at happly <;> try contradiction
  rename_i checked hcheck
  cases happly
  exact ⟨raw, hraw, StepReceipt.ofChecked_realizes _ _ _ _ checked hcheck⟩

def citationPolarity (orientation : Orientation) (direction : Direction)
    (depth : Nat) : Prop :=
  match orientation, direction with
  | .forward, .forward | .backward, .reverse => depth % 2 = 0
  | .forward, .reverse | .backward, .forward => depth % 2 = 1

instance (orientation : Orientation) (direction : Direction) (depth : Nat) :
    Decidable (citationPolarity orientation direction depth) := by
  cases orientation <;> cases direction <;>
    simp [citationPolarity] <;> infer_instance

/-- Canonical remove-then-splice input for replacing one exact pinned
occurrence. The source occurrence's positional map is retained verbatim, so
repeated source positions remain repeated attachments in the replacement. -/
def PinnedOccurrence.replacementInput
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) : Splice.Input signature :=
  let original := Splice.Decomposition.originalFragmentInput decomposition
  {
    frame := original.frame
    pattern := replacement
    site := original.site
    attachment := fun position =>
      original.attachment (Fin.cast
        (input.val.extractBoundaryRaw_length selection
          decomposition.extraction.raw.layout).symm
        (occurrence.position (Fin.cast sameArity.symm position)))
    binderSpine := emptyBinderSpine replacement
    terminalBody := emptyTerminalBody replacement
    binderTarget := nofun
  }

/-- The source and replacement boundary quotients may differ only on retained
wires scoped exactly at the replacement site. This is the contextual interface
condition required before the local open-pattern implication can be lifted
through the surrounding host. -/
def PinnedOccurrence.ReplacementQuotientsLocal
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) : Prop :=
  let sourceInput := occurrence.replacementInput decomposition pattern rfl
  let targetInput := occurrence.replacementInput decomposition replacement
    sameArity
  Splice.Input.SiteLocalQuotientAgreement sourceInput targetInput rfl

instance
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    Decidable (occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity) := by
  unfold PinnedOccurrence.ReplacementQuotientsLocal
  infer_instance

/-- Every canonical pinned replacement input is executable. Attachment
visibility is inherited from canonical decomposition reassembly; the empty
binder spine discharges the remaining admissibility fields. -/
theorem PinnedOccurrence.replacementInput_admissible
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    (occurrence.replacementInput decomposition replacement
      sameArity).Admissible := by
  let original := Splice.Decomposition.originalFragmentInput decomposition
  have hadmissible :=
    Splice.Decomposition.originalFragmentInput_admissible decomposition
  constructor
  · intro position
    exact hadmissible.attachments_visible
      (Fin.cast
        (input.val.extractBoundaryRaw_length selection
          decomposition.extraction.raw.layout).symm
        (occurrence.position (Fin.cast sameArity.symm position)))
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index
  · intro index
    exact Fin.elim0 index

/-- Replace one exact theorem-side occurrence by the cited opposite side. -/
def applyTheorem (orientation : Orientation)
    (input : CheckedDiagram signature) (theoremIndex : Nat)
    (selection : CheckedSelection input.val)
    (args : List (Fin input.val.wireCount)) (direction : Direction)
    (payload : TheoremPayload input selection args) :
    Except StepError (StepReceipt input) :=
  if citationPolarity orientation direction
      (concreteCutDepth input.val selection.val.anchor) then
    match decomposeChecked signature input selection with
    | .error _ => .error .operationRejected
    | .ok decomposition =>
        if payload.occurrence.ReplacementQuotientsLocal decomposition
            payload.target payload.sameBoundaryArity then
          let spliceInput := payload.occurrence.replacementInput decomposition
            payload.target payload.sameBoundaryArity
          match hsplice : Splice.Input.spliceChecked signature spliceInput with
          | .error error => .error (namedSpliceError error)
          | .ok checked =>
              have hresult : checked.val = spliceInput.plugLayout.plugRaw :=
                (Splice.Input.spliceChecked_sound hsplice).1
              let provenance :=
                (removeWireProvenance input selection
                  decomposition.frameDomains).compose
                  (spliceFrameWireProvenance spliceInput)
              let interface :=
                (removeWireInterfaceTransport input selection
                  decomposition.frameDomains).compose
                  (spliceFrameInterfaceTransport spliceInput)
              .ok {
                result := checked
                provenance := provenance.castTarget hresult.symm
                interface := interface.castTarget hresult.symm
              }
        else
          .error .boundaryMismatch
  else
    .error .wrongPolarity

theorem applyTheorem_success {signature : List Nat}
    {orientation : Orientation}
    {input : CheckedDiagram signature}
    {theoremIndex : Nat}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    {direction : Direction}
    {payload : TheoremPayload input selection args}
    {result : StepReceipt input}
    (happly : applyTheorem orientation input theoremIndex selection args
      direction payload = .ok result) :
    citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor) ∧
      ∃ decomposition : Decomposition signature input selection,
        decomposeChecked signature input selection = .ok decomposition ∧
          payload.occurrence.ReplacementQuotientsLocal decomposition
            payload.target payload.sameBoundaryArity ∧
          let spliceInput := payload.occurrence.replacementInput decomposition
            payload.target payload.sameBoundaryArity
          ∃ checked : CheckedDiagram signature,
            Splice.Input.spliceChecked signature spliceInput = .ok checked ∧
              result.result = checked := by
  have hpolarity : citationPolarity orientation direction
      (concreteCutDepth input.val selection.val.anchor) := by
    by_cases h : citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor)
    · exact h
    · simp [applyTheorem, h] at happly
  refine ⟨hpolarity, ?_⟩
  unfold applyTheorem at happly
  rw [if_pos hpolarity] at happly
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i hlocal
  split at happly <;> try contradiction
  rename_i checked hsplice
  cases happly
  exact ⟨decomposition, hdecomposition, hlocal, checked, hsplice, rfl⟩

theorem applyTheorem_realizes {signature : List Nat}
    {orientation : Orientation}
    {input : CheckedDiagram signature}
    {theoremIndex : Nat}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    {direction : Direction}
    {payload : TheoremPayload input selection args}
    {result : StepReceipt input}
    (happly : applyTheorem orientation input theoremIndex selection args
      direction payload = .ok result) :
    citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor) ∧
      ∃ decomposition : Decomposition signature input selection,
        ∃ hdecomposition : decomposeChecked signature input selection =
            .ok decomposition,
          payload.occurrence.ReplacementQuotientsLocal decomposition
              payload.target payload.sameBoundaryArity ∧
          let spliceInput := payload.occurrence.replacementInput decomposition
            payload.target payload.sameBoundaryArity
          ∃ checked : CheckedDiagram signature,
            ∃ hsplice : Splice.Input.spliceChecked signature spliceInput =
                .ok checked,
              result.Realizes spliceInput.plugLayout.plugRaw
                ((removeWireProvenance input selection
                    decomposition.frameDomains).compose
                  (spliceFrameWireProvenance spliceInput))
                ((removeWireInterfaceTransport input selection
                    decomposition.frameDomains).compose
                  (spliceFrameInterfaceTransport spliceInput)) := by
  have hpolarity : citationPolarity orientation direction
      (concreteCutDepth input.val selection.val.anchor) := by
    by_cases h : citationPolarity orientation direction
        (concreteCutDepth input.val selection.val.anchor)
    · exact h
    · simp [applyTheorem, h] at happly
  refine ⟨hpolarity, ?_⟩
  unfold applyTheorem at happly
  rw [if_pos hpolarity] at happly
  split at happly <;> try contradiction
  rename_i decomposition hdecomposition
  dsimp only at happly
  split at happly <;> try contradiction
  rename_i hlocal
  split at happly <;> try contradiction
  rename_i checked hsplice
  have hresult : checked.val =
      (payload.occurrence.replacementInput decomposition payload.target
        payload.sameBoundaryArity).plugLayout.plugRaw :=
    (Splice.Input.spliceChecked_sound hsplice).1
  cases happly
  rcases checked with ⟨diagram, wellFormed⟩
  dsimp only at hresult hsplice ⊢
  subst diagram
  refine ⟨decomposition, hdecomposition, hlocal, ⟨_, wellFormed⟩, hsplice, ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro wire
    simp [WireProvenance.castTarget]
  · intro wire
    simp [InterfaceTransport.castTarget]

/-- The ordered concrete occurrence certified by a `PinnedOccurrence`, exposed
as an open proof state without collapsing repeated boundary positions. -/
def PinnedOccurrence.openState
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {args : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern args) :
    OpenProofState signature where
  diagram :=
    ⟨(pinnedSelectedFragment input selection pattern.val.boundary.length
        occurrence.position).diagram,
      (pinnedSelectedFragment_wellFormed input selection
        pattern.val.boundary.length occurrence.position).diagram_well_formed⟩
  boundary :=
    (pinnedSelectedFragment input selection pattern.val.boundary.length
      occurrence.position).boundary
  boundary_root_scoped :=
    (pinnedSelectedFragment_wellFormed input selection
      pattern.val.boundary.length occurrence.position).boundary_is_root_scoped

/-- Exact pinned occurrences preserve intrinsic open denotation positionwise.
The boundary cast is induced by the certified ordered open isomorphism, so
aliases and repeated positions are retained rather than deduplicated. -/
theorem PinnedOccurrence.openState_denote_iff
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin occurrence.openState.boundary.length → model.Carrier) :
    occurrence.openState.denote model named args ↔
      pattern.denote model named
        (args ∘ Fin.cast occurrence.occurrence.boundary_length_eq.symm) := by
  exact occurrence.occurrence.denote_iff
    (pinnedSelectedFragment_wellFormed input selection
      pattern.val.boundary.length occurrence.position)
    pattern.property model named args

/-- Checked canonical replacement exists for every pinned occurrence and
same-arity replacement, without a boundary-injectivity premise. -/
theorem PinnedOccurrence.replacement_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length) :
    ∃ result, Splice.Input.spliceChecked signature
      (occurrence.replacementInput decomposition replacement sameArity) =
        .ok result :=
  (occurrence.replacementInput decomposition replacement sameArity)
    |>.spliceChecked_complete
      (occurrence.replacementInput_admissible decomposition replacement
        sameArity)

/-- The canonical replacement attachment at each ordered position is exactly
the caller-pinned host argument at that position.  This is positional and
therefore also covers repeated arguments. -/
theorem PinnedOccurrence.replacementInput_attachment_origin
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (position : Fin replacement.val.boundary.length) :
    decomposition.frameDomains.wires.origin
        ((occurrence.replacementInput decomposition replacement sameArity)
          |>.attachment position) =
      hostArgs.get (Fin.cast occurrence.args_length.symm
        (Fin.cast sameArity.symm position)) := by
  simp only [PinnedOccurrence.replacementInput,
    Splice.Decomposition.originalFragmentInput,
    Splice.Decomposition.originalAttachment]
  rw [decomposition.frameDomains.wires.origin_index]
  simpa using occurrence.argument_alignment
    (Fin.cast sameArity.symm position)

/-- The source-side and replacement-side canonical inputs share one retained
frame, splice site, ordered arity, positional attachment presentation, and the
contextual locality condition on quotient changes. -/
def PinnedOccurrence.twoInputPresentation
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {pattern : CheckedOpenDiagram signature}
    {hostArgs : List (Fin input.val.wireCount)}
    (occurrence : PinnedOccurrence input selection pattern hostArgs)
    (decomposition : Decomposition signature input selection)
    (replacement : CheckedOpenDiagram signature)
    (sameArity : pattern.val.boundary.length =
      replacement.val.boundary.length)
    (locality : occurrence.ReplacementQuotientsLocal decomposition replacement
      sameArity) :
    Splice.Input.TwoInputPresentation
      (occurrence.replacementInput decomposition pattern rfl)
      (occurrence.replacementInput decomposition replacement sameArity) where
  frame_eq := rfl
  site_eq := rfl
  boundary_arity_eq := sameArity
  attachment_eq := by
    intro position
    apply Fin.ext
    rfl
  site_local_quotients := locality

/-- A theorem-citation payload determines an accepted canonical
remove-then-splice replacement before any operational commuting argument. -/
theorem TheoremPayload.canonicalReplacement_complete
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {args : List (Fin input.val.wireCount)}
    (payload : TheoremPayload input selection args) :
    ∃ decomposition : Decomposition signature input selection,
      decomposeChecked signature input selection = .ok decomposition ∧
        ∃ canonical, Splice.Input.spliceChecked signature
          (payload.occurrence.replacementInput decomposition payload.target
            payload.sameBoundaryArity) = .ok canonical := by
  obtain ⟨decomposition, hdecomposition⟩ :=
    decomposeChecked_complete signature input selection
  obtain ⟨canonical, hcanonical⟩ :=
    payload.occurrence.replacement_complete decomposition payload.target
      payload.sameBoundaryArity
  exact ⟨decomposition, hdecomposition, canonical, hcanonical⟩

theorem relUnfold_equiv
    (definitions : VerifiedDefinitions signature)
    (index : Fin signature.length)
    (args : Fin (definitions.entry index).body.val.boundary.length →
      Lambda.Individual) :
    (interpretDefinitions definitions)
        (definitions.entry index).body.val.boundary.length
        (definitions.entry index).namedRelation args ↔
      (definitions.entry index).body.denote Lambda.canonicalModel
        (interpretDefinitions definitions) args :=
  interpretDefinitions_entry_equation definitions index args

theorem relFold_equiv
    (definitions : VerifiedDefinitions signature)
    (index : Fin signature.length)
    (args : Fin (definitions.entry index).body.val.boundary.length →
      Lambda.Individual) :
    (definitions.entry index).body.denote Lambda.canonicalModel
        (interpretDefinitions definitions) args ↔
      (interpretDefinitions definitions)
        (definitions.entry index).body.val.boundary.length
        (definitions.entry index).namedRelation args :=
  (interpretDefinitions_entry_equation definitions index args).symm

theorem theoremCitation_positive
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (positive : ctx.cutDepth % 2 = 0)
    (valid : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv source →
        denoteRegion model named holeEnv holeRelEnv target) :
    denoteRegion model named env rels (ctx.fill source) →
      denoteRegion model named env rels (ctx.fill target) :=
  context_mono model named env rels positive valid

theorem theoremCitation_negative
    (ctx : DiagramContext signature outerWires holeWires outerRels holeRels)
    (source target : Region signature holeWires holeRels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (rels : RelEnv model.Carrier outerRels)
    (negative : ctx.cutDepth % 2 = 1)
    (valid : ∀ holeEnv holeRelEnv,
      denoteRegion model named holeEnv holeRelEnv source →
        denoteRegion model named holeEnv holeRelEnv target) :
    denoteRegion model named env rels (ctx.fill target) →
      denoteRegion model named env rels (ctx.fill source) :=
  context_anti model named env rels negative valid

end VisualProof.Rule
