import VisualProof.Diagram.Concrete.OpenCompilation
import VisualProof.Diagram.Concrete.Subgraph.Extract
import VisualProof.Diagram.Concrete.Subgraph.FactorizationInsertion
import VisualProof.Diagram.Concrete.Subgraph.Reconstruction
import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw
import VisualProof.Rule.Tag
import VisualProof.Theory.Semantics

namespace VisualProof

/-- Canonical concrete syntax for one folded reference. Each ordered argument
position has its own fragment boundary wire; host attachment may alias them. -/
def referenceFragmentRaw
    (definitions : List (List Sig))
    (definition : Fin definitions.length) :
    OpenConcreteDiagram definitions.length where
  diagram :=
    { regionCount := 1
      nodeCount := 1
      wireCount := (definitions.get definition).length
      root := ⟨0, by omega⟩
      regions := fun _ => .sheet
      nodes := fun _ =>
        .ref ⟨0, by omega⟩ definition (definitions.get definition)
      wires := fun wire =>
        { sig := (definitions.get definition).get wire
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .arg wire.val⟩] } }
  boundary := Data.Finite.allFin (definitions.get definition).length

/-- Checked canonical folded-reference fragment. -/
structure CheckedReferenceFragment
    (definitions : List (List Sig))
    (definition : Fin definitions.length) : Type where
  wellFormed :
    (referenceFragmentRaw definitions definition).WellFormed definitions

namespace CheckedReferenceFragment

def fragment
    (checked : CheckedReferenceFragment definitions definition) :
    CheckedOpenDiagram definitions :=
  ⟨referenceFragmentRaw definitions definition, checked.wellFormed⟩

@[simp] theorem generated
    (checked : CheckedReferenceFragment definitions definition) :
    checked.fragment.val = referenceFragmentRaw definitions definition :=
  rfl

@[simp] theorem boundaryLength
    (checked : CheckedReferenceFragment definitions definition) :
    checked.fragment.val.boundary.length =
      (definitions.get definition).length := by
  simp [fragment, referenceFragmentRaw, Data.Finite.allFin_eq_finRange]

@[simp] theorem boundarySignatures
    (checked : CheckedReferenceFragment definitions definition) :
    checkedBoundarySigs checked.fragment = definitions.get definition := by
  change
    (Data.Finite.allFin (definitions.get definition).length).map
        (definitions.get definition).get =
      definitions.get definition
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := definitions.get definition))

end CheckedReferenceFragment

/-- Validate canonical folded-reference syntax through the ordinary concrete
checker. This is the exact pattern consumed by unfold and produced by fold. -/
def checkReferenceFragment
    (definitions : List (List Sig))
    (definition : Fin definitions.length) :
    Except WFError (CheckedReferenceFragment definitions definition) := by
  let raw := referenceFragmentRaw definitions definition
  match accepted : ConcreteDiagram.checkWellFormed definitions raw.diagram with
  | .error error => exact .error error
  | .ok checked =>
      have generatedDiagram : checked.val = raw.diagram :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      exact .ok
        ⟨{ diagram := generatedDiagram ▸ checked.property
           boundary_root_scoped := by
             simp [raw, referenceFragmentRaw,
               Data.Finite.allFin_eq_finRange] }⟩

namespace ConcreteDefinitionWeakening

/-- Shift every stored definition reference through one chronological snoc. -/
def node : CNode regionCount definitions.length →
    CNode regionCount (newArgs :: definitions).length
  | .atom region args => .atom region args
  | .ref region definition args => .ref region definition.succ args
  | .identity region sig arity => .identity region sig arity

/-- The same concrete carrier in a definition context extended at its head. -/
abbrev diagram (source : ConcreteDiagram definitions.length) :
    ConcreteDiagram (newArgs :: definitions).length where
  regionCount := source.regionCount
  nodeCount := source.nodeCount
  wireCount := source.wireCount
  root := source.root
  regions := source.regions
  nodes := fun sourceNode => node (source.nodes sourceNode)
  wires := source.wires

/-- Preserve the ordered boundary while weakening every reference in the body. -/
abbrev openDiagram (source : OpenConcreteDiagram definitions.length) :
    OpenConcreteDiagram (newArgs :: definitions).length where
  diagram := diagram source.diagram
  boundary := source.boundary

end ConcreteDefinitionWeakening

/-- Stable failures while transporting a checked definition body through a
later chronological definition. -/
inductive DefinitionBodyError
  | weakeningRejected (error : WFError)
  | compilationRejected
  deriving Repr, DecidableEq

/-- A rechecked concrete body after one chronological definition snoc. -/
structure WeakenedDefinitionBody
    (newArgs : List Sig) (source : CheckedOpenDiagram definitions) : Type where
  private mk ::
  wellFormed :
    (ConcreteDefinitionWeakening.openDiagram
      (newArgs := newArgs) source.val).WellFormed (newArgs :: definitions)

namespace WeakenedDefinitionBody

/-- The uniquely generated weakened body; only its well-formedness is checked. -/
def body
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    CheckedOpenDiagram (newArgs :: definitions) :=
  ⟨ConcreteDefinitionWeakening.openDiagram
    (newArgs := newArgs) source.val, weakened.wellFormed⟩

@[simp] theorem generated
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    weakened.body.val =
      ConcreteDefinitionWeakening.openDiagram
        (newArgs := newArgs) source.val :=
  rfl

end WeakenedDefinitionBody

/-- Recheck the weakened body with the ordinary concrete well-formedness
authority. Only definition indices change; boundary order and aliases do not. -/
def weakenDefinitionBody
    (newArgs : List Sig) (source : CheckedOpenDiagram definitions) :
    Except DefinitionBodyError (WeakenedDefinitionBody newArgs source) := by
  let raw :=
    ConcreteDefinitionWeakening.openDiagram (newArgs := newArgs) source.val
  match accepted : ConcreteDiagram.checkWellFormed
      (newArgs :: definitions) raw.diagram with
  | .error error => exact .error (.weakeningRejected error)
  | .ok checked =>
      have generatedDiagram : checked.val = raw.diagram :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      exact .ok ⟨
        { diagram := generatedDiagram ▸ checked.property
          boundary_root_scoped := by
            simpa [raw, ConcreteDefinitionWeakening.openDiagram,
              ConcreteDefinitionWeakening.diagram] using
              source.property.boundary_root_scoped }⟩

@[simp] theorem weakened_checkedBoundarySigs
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    checkedBoundarySigs weakened.body = checkedBoundarySigs source := by
  simp only [checkedBoundarySigs]
  rw [weakened.generated]

namespace WeakenedDefinitionBody

/-- Compile the weakened body through the sole concrete-to-intrinsic authority. -/
def compile?
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    Except DefinitionBodyError (OpenCompilation weakened.body) :=
  match compileOpen weakened.body with
  | none => .error .compilationRejected
  | some compiled => .ok compiled

end WeakenedDefinitionBody

/-- Chronological concrete definition data indexed by the intrinsic store it
generates. The intrinsic body is never supplied independently: it is exactly
the output of the checked concrete compiler. -/
inductive CheckedDefinitionData : (definitions : Definitions) → Type
  | nil : CheckedDefinitionData Definitions.nil
  | snoc {prior : Definitions}
      (priorData : CheckedDefinitionData prior)
      {body : CheckedOpenDiagram prior.signatures}
      (compiled : OpenCompilation body) :
      CheckedDefinitionData
        (Definitions.snoc prior (checkedBoundarySigs body)
          compiled.openDiagram)

/-- The sole paired concrete/intrinsic chronological definition authority. -/
structure CheckedDefinitions where
  intrinsic : Definitions
  data : CheckedDefinitionData intrinsic

namespace CheckedDefinitions

/-- Empty concrete and intrinsic definition stores. -/
def nil : CheckedDefinitions :=
  ⟨Definitions.nil, .nil⟩

/-- Append one checked concrete body, deriving the intrinsic entry exclusively
from its successful open compilation. -/
def snoc (prior : CheckedDefinitions)
    (body : CheckedOpenDiagram prior.intrinsic.signatures) :
    Except DefinitionBodyError CheckedDefinitions :=
  match compileOpen body with
  | none => .error .compilationRejected
  | some compiled =>
      .ok
        ⟨Definitions.snoc prior.intrinsic (checkedBoundarySigs body)
            compiled.openDiagram,
          .snoc prior.data compiled⟩

end CheckedDefinitions

/-- A concrete stored body resolved in the complete current definition
context, with its exact ordered signature retained in the type. -/
structure ResolvedDefinitionBody
    (definitions : Definitions) (args : List Sig) where
  body : CheckedOpenDiagram definitions.signatures
  compilation : OpenCompilation body
  boundarySignatures : checkedBoundarySigs body = args

private def bodyBoundaryLength
    {definitions : Definitions} {args : List Sig}
    (body : ResolvedDefinitionBody definitions args) :
    body.body.val.boundary.length = args.length := by
  have exact := congrArg List.length body.boundarySignatures
  simpa [checkedBoundarySigs] using exact

private theorem removalWireIndex_congr
    (occurrence : Occurrence pattern host)
    (left right : host.val.WireId)
    (leftRetained : left ∈ Removal.wires occurrence)
    (rightRetained : right ∈ Removal.wires occurrence)
    (same : left = right) :
    Removal.wireIndex occurrence left leftRetained =
      Removal.wireIndex occurrence right rightRetained := by
  subst right
  rfl

namespace CheckedDefinitionData

/-- Resolve a typed definition reference and weaken its concrete body through
every later chronological entry. This is index traversal, never graph search. -/
def resolveBody :
    {definitions : Definitions} →
      CheckedDefinitionData definitions →
      DefVar definitions.signatures args →
      Except DefinitionBodyError (ResolvedDefinitionBody definitions args)
  | _, .nil, reference => nomatch reference
  | _, @CheckedDefinitionData.snoc prior _ body compiled, .here => do
      let weakened ← weakenDefinitionBody (checkedBoundarySigs body) body
      let compilation ← weakened.compile?
      pure
        { body := weakened.body
          compilation := compilation
          boundarySignatures := weakened_checkedBoundarySigs weakened }
  | _, @CheckedDefinitionData.snoc prior priorData body compiled,
      .there earlier => do
      let resolved ← resolveBody priorData earlier
      let weakened ←
        weakenDefinitionBody (checkedBoundarySigs body) resolved.body
      let compilation ← weakened.compile?
      pure
        { body := weakened.body
          compilation := compilation
          boundarySignatures :=
            (weakened_checkedBoundarySigs weakened).trans
              resolved.boundarySignatures }

theorem resolveBody_here_eq
    {prior : Definitions}
    (priorData : CheckedDefinitionData prior)
    {body : CheckedOpenDiagram prior.signatures}
    (compiled : OpenCompilation body) :
    resolveBody (.snoc priorData compiled) (DefVar.here) = (do
      let weakened ← weakenDefinitionBody (checkedBoundarySigs body) body
      let compilation ← weakened.compile?
      pure
        { body := weakened.body
          compilation := compilation
          boundarySignatures := weakened_checkedBoundarySigs weakened }) := by
  rfl

theorem resolveBody_there_eq
    {prior : Definitions}
    (priorData : CheckedDefinitionData prior)
    {body : CheckedOpenDiagram prior.signatures}
    (compiled : OpenCompilation body)
    (earlier : DefVar prior.signatures args) :
    resolveBody (.snoc priorData compiled) (.there earlier) = (do
      let resolved ← resolveBody priorData earlier
      let weakened ← weakenDefinitionBody (checkedBoundarySigs body) resolved.body
      let compilation ← weakened.compile?
      pure
        { body := weakened.body
          compilation := compilation
          boundarySignatures :=
            (weakened_checkedBoundarySigs weakened).trans
              resolved.boundarySignatures }) := by
  rfl

end CheckedDefinitionData

namespace CheckedDefinitions

/-- Resolve one typed stored body in the current full definition context. -/
def resolveBody (definitions : CheckedDefinitions)
    (reference : DefVar definitions.intrinsic.signatures args) :
    Except DefinitionBodyError
      (ResolvedDefinitionBody definitions.intrinsic args) :=
  definitions.data.resolveBody reference

end CheckedDefinitions

/-- Stable refusal outcomes of the concrete unfold checker. -/
inductive DefinitionRuleError
  | selectedNodeNotReference
  | referenceFragmentRejected (error : WFError)
  | argumentOwnerMissing
  | referenceOccurrenceRejected (error : OccurrenceError)
  | referenceRemovalRejected (error : WFError)
  | referenceCompilationRejected
  | reconstructionRejected
  | reconstructionIsoRejected
  | reconstructionCompilationRejected
  | bodyRejected (error : DefinitionBodyError)
  | attachmentWireRemoved
  | bodyAttachmentRejected
  | bodyInsertionCompilationRejected
  | bodySpliceRejected (error : WFError)
  deriving Repr, DecidableEq

/-- Durable unfold input: the exact folded reference node to replace. -/
structure UnfoldInput
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures) where
  node : source.val.NodeId

/-- Opaque receipt for exact concrete replacement of one folded reference by
its chronologically stored definition body. -/
structure AppliedUnfold
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : UnfoldInput definitions source) where
  private mk ::
  private definition : Fin definitions.intrinsic.signatures.length
  private region : source.val.RegionId
  private arguments : List Sig
  private sourceNode :
    source.val.nodes input.node = .ref region definition arguments
  private reference :
    CheckedReferenceFragment definitions.intrinsic.signatures definition
  private occurrence : Occurrence reference.fragment source
  private removed : RemovalResult occurrence
  private referenceCompilation : OpenCompilation reference.fragment
  private referenceCompilationAccepted :
    compileOpen reference.fragment = some referenceCompilation
  private reconstruction : ConcreteSpliceAttachment removed.complement
    removed.site reference.fragment
  private reconstructionAccepted :
    reconstructionAttachment? occurrence removed = some reconstruction
  private reconstructionIso : ConcreteIso reconstruction.diagram source.val
  private reconstructionIsoAccepted :
    Reconstruction.extract_splice_iso? occurrence removed reconstruction
      reconstructionAccepted = some reconstructionIso
  private reconstructionCompilation :
    InsertionCompilation referenceCompilation reconstruction
  private reconstructionCompilationAccepted :
    compileInsertion? referenceCompilation reconstruction =
      some reconstructionCompilation
  private body : ResolvedDefinitionBody definitions.intrinsic
    (definitions.intrinsic.signatures.get definition)
  private bodyAccepted :
    definitions.resolveBody
        (ConcreteElaboration.Internal.definitionVarAt
          definitions.intrinsic.signatures definition) =
      .ok body
  private attachment : ConcreteSpliceAttachment removed.complement
    removed.site body.body
  private boundaryTargets :
    ∀ position : Fin
        (definitions.intrinsic.signatures.get definition).length,
      attachment.target
          (Fin.cast (bodyBoundaryLength body).symm position) =
        reconstruction.target
          (Fin.cast reference.boundaryLength.symm position)
  private bodyInsertion : InsertionCompilation body.compilation attachment
  private bodyInsertionAccepted :
    compileInsertion? body.compilation attachment = some bodyInsertion
  private result : RawConcreteSpliceResult attachment
  private resultAccepted : spliceRaw attachment = .ok result

namespace AppliedUnfold

def source
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : UnfoldInput definitions source}
    (_applied : AppliedUnfold definitions source input) :
    CheckedDiagram definitions.intrinsic.signatures :=
  source

/-- The checked splice result. Splice normalization, if any, belongs to the
splice owner and is not part of compiler adequacy. -/
def target
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : UnfoldInput definitions source}
    (applied : AppliedUnfold definitions source input) :
    CheckedDiagram definitions.intrinsic.signatures :=
  applied.result.checked

def tag
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : UnfoldInput definitions source}
    (_applied : AppliedUnfold definitions source input) : StepTag :=
  .unfold

end AppliedUnfold

/-- Durable fold input: one exact occurrence of the checker-resolved stored
body.  The concrete definition index selects both the chronological body and
the canonical folded reference. -/
structure FoldInput
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures) where
  definition : Fin definitions.intrinsic.signatures.length
  body : ResolvedDefinitionBody definitions.intrinsic
    (definitions.intrinsic.signatures.get definition)
  bodyAccepted :
    definitions.resolveBody
        (ConcreteElaboration.Internal.definitionVarAt
          definitions.intrinsic.signatures definition) =
      .ok body
  occurrence : Occurrence body.body source

/-- Opaque receipt for exact concrete replacement of one stored-body
occurrence by its canonical folded reference. -/
structure AppliedFold
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : FoldInput definitions source) where
  private mk ::
  private removed : RemovalResult input.occurrence
  private removedAccepted : remove input.occurrence = .ok removed
  private bodyReconstruction : ConcreteSpliceAttachment removed.complement
    removed.site input.body.body
  private bodyReconstructionAccepted :
    reconstructionAttachment? input.occurrence removed =
      some bodyReconstruction
  private bodyReconstructionIso :
    ConcreteIso bodyReconstruction.diagram source.val
  private bodyReconstructionIsoAccepted :
    Reconstruction.extract_splice_iso? input.occurrence removed
        bodyReconstruction bodyReconstructionAccepted =
      some bodyReconstructionIso
  private bodyReconstructionCompilation :
    InsertionCompilation input.body.compilation bodyReconstruction
  private bodyReconstructionCompilationAccepted :
    compileInsertion? input.body.compilation bodyReconstruction =
      some bodyReconstructionCompilation
  private reference : CheckedReferenceFragment
    definitions.intrinsic.signatures input.definition
  private referenceCompilation : OpenCompilation reference.fragment
  private referenceCompilationAccepted :
    compileOpen reference.fragment = some referenceCompilation
  private attachment : ConcreteSpliceAttachment removed.complement
    removed.site reference.fragment
  private boundaryTargets :
    ∀ position : Fin
        (definitions.intrinsic.signatures.get input.definition).length,
      attachment.target
          (Fin.cast reference.boundaryLength.symm position) =
        bodyReconstruction.target
          (Fin.cast (bodyBoundaryLength input.body).symm position)
  private insertion : InsertionCompilation referenceCompilation attachment
  private insertionAccepted :
    compileInsertion? referenceCompilation attachment = some insertion
  private result : RawConcreteSpliceResult attachment
  private resultAccepted : spliceRaw attachment = .ok result

namespace AppliedFold

def source
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : FoldInput definitions source}
    (_applied : AppliedFold definitions source input) :
    CheckedDiagram definitions.intrinsic.signatures :=
  source

def target
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : FoldInput definitions source}
    (applied : AppliedFold definitions source input) :
    CheckedDiagram definitions.intrinsic.signatures :=
  applied.result.checked

def tag
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    {input : FoldInput definitions source}
    (_applied : AppliedFold definitions source input) : StepTag :=
  .fold

end AppliedFold

private theorem referenceBodyBoundaryLength
    {definitions : CheckedDefinitions}
    {source : CheckedDiagram definitions.intrinsic.signatures}
    (input : FoldInput definitions source)
    (reference : CheckedReferenceFragment
      definitions.intrinsic.signatures input.definition) :
    reference.fragment.val.boundary.length =
      input.body.body.val.boundary.length := by
  exact reference.boundaryLength.trans (bodyBoundaryLength input.body).symm

/-- Deterministically unfold one folded reference. The checker never searches
for an isomorphic graph and accepts no semantic premise. -/
def applyUnfold
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : UnfoldInput definitions source) :
    Except DefinitionRuleError (AppliedUnfold definitions source input) := by
  match sourceNode : source.val.nodes input.node with
  | .atom .. | .identity .. =>
      exact .error .selectedNodeNotReference
  | .ref region definition arguments =>
      match referenceAccepted :
          checkReferenceFragment definitions.intrinsic.signatures definition with
      | .error error =>
          exact .error (.referenceFragmentRejected error)
      | .ok reference =>
          let storedArgs := definitions.intrinsic.signatures.get definition
          have referenceWireCount :
              reference.fragment.val.diagram.wireCount = storedArgs.length := by
            rw [reference.generated]
            rfl
          let argumentOwner? (position : Fin storedArgs.length) :=
            source.val.endpointOwner?
              ⟨input.node, .arg position.val⟩
          if owners : ∀ position, (argumentOwner? position).isSome = true then
            let argumentOwner (position : Fin storedArgs.length) :
                source.val.WireId :=
              (argumentOwner? position).get (owners position)
            let occurrenceInput :
                OccurrenceInput reference.fragment source :=
              { region := region
                regionMap := fun _ => region
                nodeMap := fun _ => input.node
                wireMap := fun wire =>
                  argumentOwner (Fin.cast referenceWireCount wire) }
            match occurrenceAccepted : checkOccurrence occurrenceInput with
            | .error error =>
                exact .error (.referenceOccurrenceRejected error)
            | .ok occurrence =>
                match removalAccepted : remove occurrence with
                | .error error =>
                    exact .error (.referenceRemovalRejected error)
                | .ok removed =>
                    match referenceCompilationAccepted :
                        compileOpen reference.fragment with
                    | none =>
                        exact .error .referenceCompilationRejected
                    | some referenceCompilation =>
                        match reconstructionAccepted :
                            reconstructionAttachment? occurrence removed with
                        | none =>
                            exact .error .reconstructionRejected
                        | some reconstruction =>
                            match reconstructionIsoAccepted :
                                Reconstruction.extract_splice_iso? occurrence
                                  removed reconstruction
                                  reconstructionAccepted with
                            | none =>
                                exact .error .reconstructionIsoRejected
                            | some reconstructionIso =>
                                match reconstructionCompilationAccepted :
                                    compileInsertion? referenceCompilation
                                      reconstruction with
                                | none =>
                                    exact .error
                                      .reconstructionCompilationRejected
                                | some reconstructionCompilation =>
                                    let referenceVar :=
                                      ConcreteElaboration.Internal.definitionVarAt
                                        definitions.intrinsic.signatures definition
                                    match bodyAccepted :
                                        definitions.resolveBody referenceVar with
                                    | .error error =>
                                        exact .error (.bodyRejected error)
                                    | .ok body =>
                                        let bodyCompilation := body.compilation
                                        let sourceAttachment
                                            (position : Fin
                                              body.body.val.boundary.length) :
                                            source.val.WireId :=
                                          argumentOwner
                                            (Fin.cast
                                              (bodyBoundaryLength body)
                                              position)
                                        if retained : ∀ position,
                                            sourceAttachment position ∈
                                              Removal.wires occurrence then
                                          let target
                                              (position : Fin
                                                body.body.val.boundary.length) :
                                              removed.complement.val.WireId :=
                                            Removal.wireIndex occurrence
                                              (sourceAttachment position)
                                              (retained position)
                                          match attachmentAccepted :
                                              checkConcreteSpliceAttachment
                                                removed.complement removed.site
                                                body.body target with
                                          | none =>
                                              exact .error
                                                .bodyAttachmentRejected
                                          | some attachment =>
                                              match bodyInsertionAccepted :
                                                  compileInsertion?
                                                    bodyCompilation attachment with
                                              | none =>
                                                  exact .error
                                                    .bodyInsertionCompilationRejected
                                              | some bodyInsertion =>
                                                  match resultAccepted :
                                                      spliceRaw attachment with
                                                  | .error error =>
                                                      exact .error
                                                        (.bodySpliceRejected error)
                                                  | .ok result =>
                                                      exact .ok
                                                        (AppliedUnfold.mk
                                                          definition region
                                                          arguments sourceNode
                                                          reference occurrence
                                                          removed
                                                          referenceCompilation
                                                    referenceCompilationAccepted
                                                    reconstruction
                                                    reconstructionAccepted
                                                    reconstructionIso
                                                    reconstructionIsoAccepted
                                                    reconstructionCompilation
                                                    reconstructionCompilationAccepted
                                                    body bodyAccepted attachment
                                                          (by
                                                            intro position
                                                            have attachmentExact :=
                                                              congrFun
                                                                (checkConcreteSpliceAttachment_target
                                                                  removed.complement
                                                                  removed.site
                                                                  body.body target
                                                                  attachment
                                                                  attachmentAccepted)
                                                                (Fin.cast
                                                                  (bodyBoundaryLength
                                                                    body).symm
                                                                  position)
                                                            have reconstructionExact :=
                                                              Reconstruction.attachment_target
                                                                occurrence removed
                                                                reconstruction
                                                                reconstructionAccepted
                                                                (Fin.cast
                                                                  reference.boundaryLength.symm
                                                                  position)
                                                            rw [attachmentExact,
                                                              reconstructionExact]
                                                            have inputExact :=
                                                              Occurrence.checkOccurrence_preserves_input
                                                                occurrenceInput
                                                                occurrence
                                                                occurrenceAccepted
                                                            have wireMapExact :=
                                                              congrArg
                                                                OccurrenceInput.wireMap
                                                                inputExact
                                                            have wireMapExact' :
                                                                occurrence.wireMap =
                                                                  occurrenceInput.wireMap :=
                                                              wireMapExact
                                                            have sourceWireExact :
                                                                sourceAttachment
                                                                    (Fin.cast
                                                                      (bodyBoundaryLength
                                                                        body).symm
                                                                      position) =
                                                                  Reconstruction.boundaryHostWire
                                                                    occurrence
                                                                    (Fin.cast
                                                                      reference.boundaryLength.symm
                                                                      position) := by
                                                              unfold sourceAttachment
                                                                Reconstruction.boundaryHostWire
                                                              rw [wireMapExact']
                                                              simp [occurrenceInput,
                                                                referenceFragmentRaw,
                                                                Data.Finite.allFin_eq_finRange]
                                                            unfold target
                                                            exact
                                                              removalWireIndex_congr
                                                                occurrence _ _ _ _
                                                                sourceWireExact)
                                                          bodyInsertion
                                                          bodyInsertionAccepted result
                                                          resultAccepted)
                                        else
                                          exact .error
                                            .attachmentWireRemoved
          else
            exact .error .argumentOwnerMissing

/-- Deterministically fold one exact occurrence of a chronologically stored
body.  The checker removes that occurrence and inserts the canonical reference
at the same ordered boundary tuple; it performs no graph search. -/
def applyFold
    (definitions : CheckedDefinitions)
    (source : CheckedDiagram definitions.intrinsic.signatures)
    (input : FoldInput definitions source) :
    Except DefinitionRuleError (AppliedFold definitions source input) := by
  match removedAccepted : remove input.occurrence with
  | .error error =>
      exact .error (.referenceRemovalRejected error)
  | .ok removed =>
      match bodyReconstructionAccepted :
          reconstructionAttachment? input.occurrence removed with
      | none => exact .error .reconstructionRejected
      | some bodyReconstruction =>
          match bodyReconstructionIsoAccepted :
              Reconstruction.extract_splice_iso? input.occurrence removed
                bodyReconstruction bodyReconstructionAccepted with
          | none => exact .error .reconstructionIsoRejected
          | some bodyReconstructionIso =>
              match bodyReconstructionCompilationAccepted :
                  compileInsertion? input.body.compilation
                    bodyReconstruction with
              | none => exact .error .reconstructionCompilationRejected
              | some bodyReconstructionCompilation =>
                  match referenceAccepted :
                      checkReferenceFragment definitions.intrinsic.signatures
                        input.definition with
                  | .error error =>
                      exact .error (.referenceFragmentRejected error)
                  | .ok reference =>
                      match referenceCompilationAccepted :
                          compileOpen reference.fragment with
                      | none => exact .error .referenceCompilationRejected
                      | some referenceCompilation =>
                          let target
                              (position : Fin
                                reference.fragment.val.boundary.length) :
                              removed.complement.val.WireId :=
                            bodyReconstruction.target
                              (Fin.cast
                                (referenceBodyBoundaryLength input reference)
                                position)
                          match attachmentAccepted :
                              checkConcreteSpliceAttachment removed.complement
                                removed.site reference.fragment target with
                          | none => exact .error .bodyAttachmentRejected
                          | some attachment =>
                              match insertionAccepted :
                                  compileInsertion? referenceCompilation
                                    attachment with
                              | none =>
                                  exact .error
                                    .bodyInsertionCompilationRejected
                              | some insertion =>
                                  match resultAccepted : spliceRaw attachment with
                                  | .error error =>
                                      exact .error (.bodySpliceRejected error)
                                  | .ok result =>
                                      exact .ok
                                        (AppliedFold.mk removed removedAccepted
                                          bodyReconstruction
                                          bodyReconstructionAccepted
                                          bodyReconstructionIso
                                          bodyReconstructionIsoAccepted
                                          bodyReconstructionCompilation
                                          bodyReconstructionCompilationAccepted
                                          reference referenceCompilation
                                          referenceCompilationAccepted attachment
                                          (by
                                            intro position
                                            have exactTarget := congrFun
                                              (checkConcreteSpliceAttachment_target
                                                removed.complement removed.site
                                                reference.fragment target
                                                attachment attachmentAccepted)
                                              (Fin.cast
                                                reference.boundaryLength.symm
                                                position)
                                            simpa [target] using exactTarget)
                                          insertion insertionAccepted result
                                          resultAccepted)

end VisualProof
