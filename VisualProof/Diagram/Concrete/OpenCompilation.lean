import VisualProof.Diagram.Concrete.ElaborationKernel
import VisualProof.Diagram.Open

namespace VisualProof

/-- Ordered signatures exposed by a checked concrete boundary. -/
def checkedBoundarySigs
    (checked : CheckedOpenDiagram definitions) : List Sig :=
  checked.val.boundary.map fun wire =>
    (checked.val.diagram.wires wire).sig

private def resolveExtractedWireIn?
    (signature : Fin wireCount → Sig) :
    (classes : List (Fin wireCount)) → (wire : Fin wireCount) →
      Option (Var (classes.map signature) (signature wire))
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveExtractedWireIn? signature tail wire).map .there

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
      resolveExtractedWireIn? (fun id => (diagram.wires id).sig)
        classes wire = some value) :
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
            resolveExtractedWireIn?
              (fun id => (diagram.wires id).sig) tail wire with
        | none =>
            simp [recursive] at compiled
        | some tailValue =>
            have same : Var.there tailValue = value :=
              Option.some.inj (by simpa [recursive] using compiled)
            subst value
            exact induction tailValue recursive

end ExtractedBoundaryCompiler

private def compileExtractedBoundaryFor?
    (signature : Fin wireCount → Sig)
    (classes : List (Fin wireCount)) :
    (boundary : List (Fin wireCount)) →
      Option (Vars (classes.map signature) (boundary.map signature))
  | [] => some .nil
  | wire :: tail => do
      let head ← resolveExtractedWireIn? signature classes wire
      let rest ← compileExtractedBoundaryFor? signature classes tail
      pure (.cons head rest)

private theorem compileExtractedBoundaryFor?_origins
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions) :
    ∀ boundary positions,
      compileExtractedBoundaryFor?
          (fun wire => (checked.val.diagram.wires wire).sig)
          (ConcreteElaboration.openBoundaryWires checked.val) boundary =
        some positions →
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
          resolveExtractedWireIn?
            (fun source => (checked.val.diagram.wires source).sig)
            (ConcreteElaboration.openBoundaryWires checked.val) wire with
      | none =>
          simp [headEquation] at compiled
      | some head =>
          cases tailEquation :
              compileExtractedBoundaryFor?
                (fun source => (checked.val.diagram.wires source).sig)
                (ConcreteElaboration.openBoundaryWires checked.val) tail with
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

/-- Compile every ordered boundary position to its intrinsic wire class. -/
def compileExtractedBoundary?
    {definitions : List (List Sig)}
    (checked : CheckedOpenDiagram definitions) :
  Option (Vars
      (ConcreteElaboration.openBoundaryClassSigs checked.val)
      (checkedBoundarySigs checked)) :=
  compileExtractedBoundaryFor?
    (fun wire => (checked.val.diagram.wires wire).sig)
    (ConcreteElaboration.openBoundaryWires checked.val)
    checked.val.boundary

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
The sole checked-open-to-intrinsic compilation receipt. Its evidence is limited
to outputs of the executable boundary and body compilers.
-/
structure OpenCompilation
    {definitions : List (List Sig)}
    (fragment : CheckedOpenDiagram definitions) where
  private mk ::
  boundary : Vars
    (ConcreteElaboration.openBoundaryClassSigs fragment.val)
    (checkedBoundarySigs fragment)
  private boundary_compiles :
    compileExtractedBoundary? fragment = some boundary
  private boundary_surjective :
    ∀ sig
      (fiber : Var
        (ConcreteElaboration.openBoundaryClassSigs fragment.val) sig),
      boundary.Contains fiber
  body : Region definitions
    (ConcreteElaboration.openBoundaryClassSigs fragment.val)
  bodyOrigins :
    ConcreteElaboration.OpenRootOrigins definitions fragment.val body
  private body_with_origins_compiles :
    ConcreteElaboration.compileOpenRootWithOrigins? definitions fragment.val =
      some ⟨body, bodyOrigins⟩

namespace OpenCompilation

/-- The checked concrete fragment indexed by this receipt. -/
def checked
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (_compiled : OpenCompilation fragment) :
    CheckedOpenDiagram definitions :=
  fragment

/-- The exact ordered boundary compiler equation owned by the receipt. -/
theorem boundary_generated
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    compileExtractedBoundary? fragment = some compiled.boundary :=
  compiled.boundary_compiles

/-- The exact open-body compiler equation owned by the receipt. -/
theorem body_generated
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    ConcreteElaboration.compileOpenRoot? definitions fragment.val =
      some compiled.body :=
  by
    unfold ConcreteElaboration.compileOpenRoot?
    rw [compiled.body_with_origins_compiles]
    rfl

/-- The exact dependent body-and-origin compiler equation owned by the
receipt. Every intrinsic constructor can therefore be traced back to the
concrete carrier that generated it. -/
theorem bodyWithOrigins_generated
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    ConcreteElaboration.compileOpenRootWithOrigins? definitions fragment.val =
      some ⟨compiled.body, compiled.bodyOrigins⟩ :=
  compiled.body_with_origins_compiles

/-- The intrinsic open diagram generated by the two executable compilers. -/
def openDiagram
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment) :
    OpenDiagram definitions (checkedBoundarySigs fragment) where
  classes := ConcreteElaboration.openBoundaryClassSigs fragment.val
  boundary := compiled.boundary
  boundary_surjective := compiled.boundary_surjective
  body := compiled.body

/-- The intrinsic boundary occurrence at one concrete ordered position. -/
def boundaryPackedAt
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment)
    (position : Fin fragment.val.boundary.length) :
    PackedVar
      (ConcreteElaboration.openBoundaryClassSigs fragment.val) :=
  compiled.boundary.entries.get
    ⟨position.val, by
      rw [ExtractedBoundaryCompiler.entries_length]
      simpa only [checkedBoundarySigs, List.length_map] using
        position.isLt⟩

/-- Every intrinsic boundary position recovers its exact concrete class wire. -/
theorem boundaryPackedAt_origin
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment)
    (position : Fin fragment.val.boundary.length) :
    ExtractedBoundaryCompiler.wireOfPacked
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val)
        (compiled.boundaryPackedAt position) =
      fragment.val.boundary.get position := by
  have origins :=
    compileExtractedBoundary?_origins fragment compiled.boundary
      compiled.boundary_compiles
  have atPosition :=
    congrArg (fun values => values[position.val]?) origins
  have entriesBound :
      position.val < compiled.boundary.entries.length := by
    rw [ExtractedBoundaryCompiler.entries_length]
    simpa only [checkedBoundarySigs, List.length_map] using
      position.isLt
  have mappedBound :
      position.val <
        (compiled.boundary.entries.map
          (ExtractedBoundaryCompiler.wireOfPacked
            fragment.val.diagram
            (ConcreteElaboration.openBoundaryWires
              fragment.val))).length := by
    simpa only [List.length_map] using entriesBound
  have exactPosition := Option.some.inj
    ((List.getElem?_eq_getElem mappedBound).symm.trans
      (atPosition.trans (List.getElem?_eq_getElem position.isLt)))
  simpa only [boundaryPackedAt, List.get_eq_getElem,
    List.getElem_map] using exactPosition

/--
Intrinsic boundary-position equality is exactly concrete boundary-class
equality; no alias information is lost or invented by compilation.
-/
theorem boundaryPackedAt_eq_iff
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (compiled : OpenCompilation fragment)
    (left right : Fin fragment.val.boundary.length) :
    compiled.boundaryPackedAt left =
        compiled.boundaryPackedAt right ↔
      fragment.val.boundary.get left =
        fragment.val.boundary.get right := by
  constructor
  · intro same
    have mapped := congrArg
      (ExtractedBoundaryCompiler.wireOfPacked
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val))
      same
    simpa [compiled.boundaryPackedAt_origin left,
      compiled.boundaryPackedAt_origin right] using mapped
  · intro same
    apply ExtractedBoundaryCompiler.wireOfPacked_injective
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
      (Data.Finite.eraseDups_nodup _)
    rw [compiled.boundaryPackedAt_origin left,
      compiled.boundaryPackedAt_origin right, same]

end OpenCompilation

private theorem compiledBoundary_surjective
    {definitions : List (List Sig)}
    (fragment : CheckedOpenDiagram definitions)
    (boundary : Vars
      (ConcreteElaboration.openBoundaryClassSigs fragment.val)
      (checkedBoundarySigs fragment))
    (compiled :
      compileExtractedBoundary? fragment = some boundary) :
    ∀ sig
      (fiber : Var
        (ConcreteElaboration.openBoundaryClassSigs fragment.val) sig),
      boundary.Contains fiber := by
  intro sig fiber
  let origin :=
    ExtractedBoundaryCompiler.wireOfPacked
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
  let packed :
      PackedVar
        (ConcreteElaboration.openBoundaryClassSigs fragment.val) :=
    ⟨sig, fiber⟩
  have inClasses :
      origin packed ∈
        ConcreteElaboration.openBoundaryWires fragment.val := by
    exact ExtractedBoundaryCompiler.wireOfVar_member
      fragment.val.diagram fiber
  have inBoundary : origin packed ∈ fragment.val.boundary := by
    simpa [ConcreteElaboration.openBoundaryWires] using inClasses
  have origins :=
    compileExtractedBoundary?_origins fragment boundary compiled
  have inMapped : origin packed ∈ boundary.entries.map origin := by
    rw [origins]
    exact inBoundary
  obtain ⟨candidate, candidateMember, candidateOrigin⟩ :=
    List.mem_map.mp inMapped
  have same : candidate = packed :=
    ExtractedBoundaryCompiler.wireOfPacked_injective
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
      (Data.Finite.eraseDups_nodup _)
      candidateOrigin
  simpa [Vars.Contains, packed, same] using candidateMember

/--
Run both proof-independent compilers. A successful result is the only public
constructor path for a generic checked-open compilation receipt.
-/
def compileOpen
    {definitions : List (List Sig)}
    (fragment : CheckedOpenDiagram definitions) :
    Option (OpenCompilation fragment) := by
  match boundaryAccepted : compileExtractedBoundary? fragment with
  | none => exact none
  | some boundary =>
      match bodyAccepted :
          ConcreteElaboration.compileOpenRootWithOrigins?
            definitions fragment.val with
      | none => exact none
      | some bodyWithOrigins =>
          let ⟨body, origins⟩ := bodyWithOrigins
          exact some
            (OpenCompilation.mk boundary boundaryAccepted
              (compiledBoundary_surjective
                fragment boundary boundaryAccepted)
              body origins bodyAccepted)

/-- A returned receipt exposes exactly the supplied checked fragment. -/
example
    (fragment : CheckedOpenDiagram definitions)
    (compiled : OpenCompilation fragment)
    (_accepted : compileOpen fragment = some compiled) :
    compiled.checked = fragment :=
  rfl

end VisualProof
