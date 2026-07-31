import VisualProof.Diagram.Concrete.ElaborationSupport
import VisualProof.Diagram.Concrete.IdentityIncidence
namespace VisualProof
universe u

namespace ConcreteElaboration

namespace Internal

def resolveWireIn? (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) → (wire : diagram.WireId) →
      Option (Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig)
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveWireIn? diagram tail wire).map .there

def resolveWire? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId) :
    Option (Var context.sigs (diagram.wires wire).sig) :=
  resolveWireIn? diagram context.ids wire

def resolveExpected? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) : Option (Var context.sigs expected) :=
  if equality : (diagram.wires wire).sig = expected then
    (resolveWire? diagram context wire).map fun resolved =>
      equality ▸ resolved
  else
    none

def resolvePort? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId)
    (port : CPort) (expected : Sig) :
    Option (Var context.sigs expected) := do
  let wire ← diagram.endpointOwner? ⟨node, port⟩
  resolveExpected? diagram context wire expected

def resolveArgs? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) :
    (args : List Sig) → (index : Nat) → Option (Vars context.sigs args)
  | [], _ => some .nil
  | sig :: rest, index => do
      let head ← resolvePort? diagram context node (.arg index) sig
      let tail ← resolveArgs? diagram context node rest (index + 1)
      pure (.cons head tail)

def resolveIdentityPorts? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig) :
    (remaining index : Nat) →
      Option { ports : List (Var context.sigs sig) //
        ports.length = remaining }
  | 0, _ => some ⟨[], rfl⟩
  | remaining + 1, index => do
      let head ← resolvePort? diagram context node (.identity index) sig
      let tail ← resolveIdentityPorts? diagram context node sig remaining (index + 1)
      pure ⟨head :: tail.val, by simp [tail.property]⟩

theorem resolveIdentityPorts?_at
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig)
    (remaining index : Nat)
    (ports : { values : List (Var context.sigs sig) //
      values.length = remaining })
    (compiled :
      resolveIdentityPorts? diagram context node sig remaining index =
        some ports)
    (offset : Nat) (bound : offset < remaining) :
    ∃ resolved,
      resolvePort? diagram context node (.identity (index + offset)) sig =
        some resolved ∧
      resolved ∈ ports.val := by
  induction remaining generalizing index offset with
  | zero => omega
  | succ remaining induction =>
      cases headEquation :
          resolvePort? diagram context node (.identity index) sig with
      | none =>
          simp [resolveIdentityPorts?, headEquation] at compiled
      | some head =>
          cases tailEquation :
              resolveIdentityPorts? diagram context node sig remaining
                (index + 1) with
          | none =>
              simp [resolveIdentityPorts?, headEquation, tailEquation] at compiled
          | some tail =>
              have packedEquality :
                  (⟨head :: tail.val, by simp [tail.property]⟩ :
                    { values : List (Var context.sigs sig) //
                      values.length = remaining + 1 }) = ports := by
                exact Option.some.inj (by
                  simpa [resolveIdentityPorts?, headEquation, tailEquation]
                    using compiled)
              have valuesEquality : head :: tail.val = ports.val :=
                congrArg Subtype.val packedEquality
              cases offset with
              | zero =>
                  refine ⟨head, ?_, ?_⟩
                  · simpa using headEquation
                  · rw [← valuesEquality]
                    simp
              | succ offset =>
                  obtain ⟨resolved, resolvedEquation, member⟩ :=
                    induction (index := index + 1) (ports := tail)
                      tailEquation offset (by omega)
                  refine ⟨resolved, ?_, ?_⟩
                  · simpa only [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using resolvedEquation
                  · exact valuesEquality ▸
                      List.mem_cons_of_mem head member

theorem resolveIdentityPorts?_mem
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig)
    (remaining index : Nat)
    (ports : { values : List (Var context.sigs sig) //
      values.length = remaining })
    (compiled :
      resolveIdentityPorts? diagram context node sig remaining index =
        some ports)
    (resolved : Var context.sigs sig) (member : resolved ∈ ports.val) :
    ∃ offset, offset < remaining ∧
      resolvePort? diagram context node (.identity (index + offset)) sig =
        some resolved := by
  induction remaining generalizing index with
  | zero =>
      have empty : ports.val = [] := List.length_eq_zero_iff.mp ports.property
      simp [empty] at member
  | succ remaining induction =>
      cases headEquation :
          resolvePort? diagram context node (.identity index) sig with
      | none =>
          simp [resolveIdentityPorts?, headEquation] at compiled
      | some head =>
          cases tailEquation :
              resolveIdentityPorts? diagram context node sig remaining
                (index + 1) with
          | none =>
              simp [resolveIdentityPorts?, headEquation, tailEquation] at compiled
          | some tail =>
              have packedEquality :
                  (⟨head :: tail.val, by simp [tail.property]⟩ :
                    { values : List (Var context.sigs sig) //
                      values.length = remaining + 1 }) = ports := by
                exact Option.some.inj (by
                  simpa [resolveIdentityPorts?, headEquation, tailEquation]
                    using compiled)
              have valuesEquality : head :: tail.val = ports.val :=
                congrArg Subtype.val packedEquality
              rw [← valuesEquality] at member
              simp only [List.mem_cons] at member
              rcases member with headEquality | tailMember
              · subst head
                exact ⟨0, by omega, by simpa using headEquation⟩
              · obtain ⟨offset, bound, resolvedEquation⟩ :=
                  induction (index := index + 1) (ports := tail)
                    tailEquation tailMember
                refine ⟨offset + 1, by omega, ?_⟩
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  resolvedEquation

theorem resolveIdentityPorts?_member_of_resolved
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig)
    (remaining index : Nat)
    (ports : { values : List (Var context.sigs sig) //
      values.length = remaining })
    (compiled :
      resolveIdentityPorts? diagram context node sig remaining index =
        some ports)
    (offset : Nat) (bound : offset < remaining)
    (resolved : Var context.sigs sig)
    (resolvedEquation :
      resolvePort? diagram context node (.identity (index + offset)) sig =
        some resolved) :
    resolved ∈ ports.val := by
  obtain ⟨candidate, candidateEquation, member⟩ :=
    resolveIdentityPorts?_at diagram context node sig remaining index ports
      compiled offset bound
  have equality : candidate = resolved :=
    Option.some.inj (candidateEquation.symm.trans resolvedEquation)
  simpa [equality] using member

theorem identity_resolved_index_bound
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram)
    (node : diagram.NodeId) (region : diagram.RegionId)
    (sig : Sig) (arity index : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (resolved : Var context.sigs sig)
    (resolvedEquation :
      resolvePort? diagram context node (.identity index) sig =
        some resolved) :
    index < arity := by
  cases ownerEquation :
      diagram.endpointOwner? ⟨node, .identity index⟩ with
  | none =>
      simp [resolvePort?, ownerEquation] at resolvedEquation
  | some wire =>
      have incident :=
        ConcreteDiagram.endpointOwner?_incident diagram
          ⟨node, .identity index⟩ wire ownerEquation
      have required :=
        ConcreteDiagram.incident_port_required definitions diagram wellFormed
          wire ⟨node, .identity index⟩ incident
      simpa [ConcreteDiagram.requiredPorts, nodeData] using required

def definitionVarAt :
    (definitions : List (List Sig)) → (index : Fin definitions.length) →
      DefVar definitions (definitions.get index)
  | _ :: _, ⟨0, _⟩ => .here
  | _ :: rest, ⟨index + 1, bound⟩ =>
      .there (definitionVarAt rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩)

def compileNode? (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) (node : diagram.NodeId) :
    Option (Item definitions context.sigs) :=
  match diagram.nodes node with
  | .atom _ args => do
      let head ← resolvePort? diagram context node .head (.rel args)
      let arguments ← resolveArgs? diagram context node args 0
      pure (.atom head arguments)
  | .ref _ definition args =>
      if signature : definitions.get definition = args then do
        let arguments ← resolveArgs? diagram context node args 0
        let reference := definitionVarAt definitions definition
        pure (.named (signature ▸ reference) arguments)
      else
        none
  | .identity _ sig arity =>
      if arityWitness : 2 ≤ arity then do
        let ports ← resolveIdentityPorts? diagram context node sig arity 0
        pure (.identity sig ports.val (by
          simpa only [ports.property] using arityWitness))
      else
        none

end Internal

open Internal

def compileNodes? (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) :
    List diagram.NodeId → Option (ItemSeq definitions context.sigs)
  | [] => some .nil
  | node :: tail => do
      let head ← compileNode? definitions diagram context node
      let rest ← compileNodes? definitions diagram context tail
      pure (.cons head rest)

def compileChildrenWith?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : WireContext diagram) :
    List diagram.RegionId → Option (ItemSeq definitions context.sigs)
  | [] => some .nil
  | child :: tail => do
      let body ← recurse child context
      let rest ← compileChildrenWith? definitions diagram recurse context tail
      pure (.cons (.cut body) rest)

/-- Discharge one ordered block of local signatures as nested binders.  The
finisher is intentionally independent of concrete wire identifiers. -/
def finishRegionSignatures (outer : List Sig) :
    (localSigs : List Sig) →
    Region definitions (localSigs ++ outer) → Region definitions outer
  | [], body => body
  | head :: tail, body =>
      finishRegionSignatures outer tail
        (.mk (.cons (.bind head body) .nil))

private def appendSignaturesExact
    {targetOuter sourceOuter targetLocal sourceLocal : List Sig}
    (outerExact : targetOuter = sourceOuter)
    (localExact : targetLocal = sourceLocal) :
    targetLocal ++ targetOuter = sourceLocal ++ sourceOuter := by
  cases outerExact
  cases localExact
  rfl

/-- Reindexing both signature blocks commutes exactly with region finishing. -/
theorem finishRegionSignatures_reindex
    (outerExact : targetOuter = sourceOuter)
    (localExact : targetLocal = sourceLocal)
    (sourceBody : Region definitions (sourceLocal ++ sourceOuter))
    (targetBody : Region definitions (targetLocal ++ targetOuter))
    (bodyExact :
      appendSignaturesExact outerExact localExact ▸ targetBody =
        sourceBody) :
    outerExact ▸
        finishRegionSignatures targetOuter targetLocal targetBody =
      finishRegionSignatures sourceOuter sourceLocal sourceBody := by
  cases outerExact
  cases localExact
  have targetExact : targetBody = sourceBody := by
    simpa using bodyExact
  subst targetBody
  rfl

private def finishRegionFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
    Region definitions
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig) →
    Region definitions
      (outerIds.map fun wire => (diagram.wires wire).sig)
  | [], body => body
  | head :: tail, body =>
      finishRegionFor diagram outerIds tail
        (.mk (.cons (.bind (diagram.wires head).sig body) .nil))

def finishRegion (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId)
    (body : Region definitions (context.extend region).sigs) :
    Region definitions context.sigs :=
  finishRegionFor diagram context.ids (diagram.wiresAt region) body

private theorem cast_bound_region
    (head : Sig)
    (same : sourceTail = targetTail)
    (body : Region definitions (head :: sourceTail)) :
    same ▸
        (.mk (.cons (.bind head body) .nil) : Region definitions sourceTail) =
      (.mk (.cons
        (.bind head (congrArg (List.cons head) same ▸ body)) .nil) :
        Region definitions targetTail) := by
  cases same
  rfl

private theorem finishRegionFor_eq_signatures
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    ∀ (localIds : List diagram.WireId)
      (body : Region definitions
        ((localIds ++ outerIds).map
          (fun wire => (diagram.wires wire).sig))),
      finishRegionFor diagram outerIds localIds body =
        finishRegionSignatures
          (outerIds.map fun wire => (diagram.wires wire).sig)
          (localIds.map fun wire => (diagram.wires wire).sig)
          (List.map_append ▸ body)
  | [], body => rfl
  | head :: tail, body => by
      simp only [finishRegionFor, List.map_cons, finishRegionSignatures]
      rw [finishRegionFor_eq_signatures diagram outerIds tail]
      let tailProof :
          (tail ++ outerIds).map
              (fun wire => (diagram.wires wire).sig) =
            tail.map (fun wire => (diagram.wires wire).sig) ++
              outerIds.map (fun wire => (diagram.wires wire).sig) :=
        List.map_append
      have fullProofExact :
          (List.map_append :
            ((head :: tail ++ outerIds).map
                (fun wire => (diagram.wires wire).sig) =
              (diagram.wires head).sig ::
                (tail.map (fun wire => (diagram.wires wire).sig) ++
                  outerIds.map (fun wire => (diagram.wires wire).sig)))) =
            congrArg (List.cons (diagram.wires head).sig) tailProof :=
        Subsingleton.elim _ _
      rw [fullProofExact]
      rw [cast_bound_region]
      congr 4

/-- Concrete region finishing is exactly the signature-only finisher. -/
theorem finishRegion_eq_signatures
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram)
    (region : diagram.RegionId)
    (body : Region definitions (context.extend region).sigs) :
    finishRegion diagram context region body =
      finishRegionSignatures context.sigs
        ((diagram.wiresAt region).map
          (fun wire => (diagram.wires wire).sig))
        (WireContext.sigs_extend context region ▸ body) := by
  unfold finishRegion
  rw [finishRegionFor_eq_signatures]
  have proofExact :
      (List.map_append :
        ((diagram.wiresAt region ++ context.ids).map
          (fun wire => (diagram.wires wire).sig) = _)) =
        WireContext.sigs_extend context region :=
    Subsingleton.elim _ _
  rw [proofExact]
  rfl

def compileRegion? (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    Nat → (region : diagram.RegionId) → (context : WireContext diagram) →
      Option (Region definitions context.sigs)
  | 0, _, _ => none
  | fuel + 1, region, context => do
      let extended := context.extend region
      let nodes ← compileNodes? definitions diagram extended
        (diagram.nodesAt region)
      let children ← compileChildrenWith? definitions diagram
        (compileRegion? definitions diagram fuel) extended
        (diagram.childrenOf region)
      pure (finishRegion diagram context region
        (.mk (nodes.append children)))

/-- The proof-independent kernel is exposed only through this computation theorem. -/
def compileRoot? (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :
    Option (Region definitions []) :=
  compileRegion? definitions diagram (diagram.regionCount + 1)
    diagram.root (WireContext.empty diagram)

/-- Deduplicated open-wire classes in first boundary-occurrence order. -/
def openBoundaryWires
    (openDiagram : OpenConcreteDiagram definitionCount) :
    List openDiagram.diagram.WireId :=
  openDiagram.boundary.eraseDups

/-- Signatures of the deduplicated open-wire classes. -/
def openBoundaryClassSigs
    (openDiagram : OpenConcreteDiagram definitionCount) : List Sig :=
  (openBoundaryWires openDiagram).map fun wire =>
    (openDiagram.diagram.wires wire).sig

/--
Root-scoped wires not exposed at the open boundary remain local existential
binders. Boundary wires are excluded from this list.
-/
def openRootLocalWires
    (openDiagram : OpenConcreteDiagram definitionCount) :
    List openDiagram.diagram.WireId :=
  (openDiagram.diagram.wiresAt openDiagram.diagram.root).filter fun wire =>
    !decide (wire ∈ openBoundaryWires openDiagram)

/--
Compile an open root with boundary classes already visible. Root-local wires
are prepended only for content compilation and are the only wires discharged
as binders; boundary wires remain free in the resulting intrinsic region.
-/
def compileOpenRoot? (definitions : List (List Sig))
    (openDiagram : OpenConcreteDiagram definitions.length) :
    Option (Region definitions (openBoundaryClassSigs openDiagram)) := do
  let diagram := openDiagram.diagram
  let boundary := openBoundaryWires openDiagram
  let localWires := openRootLocalWires openDiagram
  let extended : WireContext diagram := ⟨localWires ++ boundary⟩
  let nodes ← compileNodes? definitions diagram extended
    (diagram.nodesAt diagram.root)
  let children ← compileChildrenWith? definitions diagram
    (compileRegion? definitions diagram diagram.regionCount) extended
    (diagram.childrenOf diagram.root)
  pure (finishRegionFor diagram boundary localWires
    (.mk (nodes.append children)))

private theorem resolveWireIn?_complete
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ∃ resolvedVar, resolveWireIn? diagram ids wire = some resolvedVar := by
  induction ids with
  | nil => simp at member
  | cons head tail ih =>
      by_cases equality : wire = head
      · subst wire
        exact ⟨.here, by simp [resolveWireIn?]⟩
      · have tailMember : wire ∈ tail := by simpa [equality] using member
        obtain ⟨resolvedVar, resolved⟩ := ih tailMember
        exact ⟨.there resolvedVar, by
          simp [resolveWireIn?, equality, resolved]⟩

private theorem resolveWireIn?_sound_member
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) (wire : diagram.WireId)
    {resolved :
      Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig}
    (equation : resolveWireIn? diagram ids wire = some resolved) :
    wire ∈ ids := by
  induction ids with
  | nil => simp [resolveWireIn?] at equation
  | cons head tail ih =>
      by_cases equality : wire = head
      · simp [equality]
      · cases tailEquation : resolveWireIn? diagram tail wire with
        | none => simp [resolveWireIn?, equality, tailEquation] at equation
        | some tailVar =>
            exact List.mem_cons_of_mem head (ih tailEquation)

theorem Internal.resolveWire?_complete
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (member : wire ∈ context.ids) :
    ∃ resolvedVar, resolveWire? diagram context wire = some resolvedVar :=
  resolveWireIn?_complete diagram context.ids wire member

private theorem resolveWire?_sound_member
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    {resolved : Var context.sigs (diagram.wires wire).sig}
    (equation : resolveWire? diagram context wire = some resolved) :
    wire ∈ context.ids :=
  resolveWireIn?_sound_member diagram context.ids wire equation

theorem Internal.resolveExpected?_sound_member
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) {resolved : Var context.sigs expected}
    (equation :
      resolveExpected? diagram context wire expected = some resolved) :
    wire ∈ context.ids := by
  unfold resolveExpected? at equation
  split at equation
  · rename_i signature
    cases wireEquation : resolveWire? diagram context wire with
    | none => simp [wireEquation] at equation
    | some wireVar =>
        exact resolveWire?_sound_member diagram context wire wireEquation
  · simp at equation

theorem Internal.resolveExpected?_sound_signature
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) {resolved : Var context.sigs expected}
    (equation :
      resolveExpected? diagram context wire expected = some resolved) :
    (diagram.wires wire).sig = expected := by
  unfold resolveExpected? at equation
  split at equation
  · assumption
  · simp at equation

/--
Extend an open root's boundary-class environment with values for precisely its
local root wires.  The private general-purpose environment constructor remains
an implementation detail of concrete elaboration.
-/
def extendOpenRootEnvironment
    (openDiagram : OpenConcreteDiagram definitionCount)
    {pre : PreModel}
    (values : WireValues pre
      ((openRootLocalWires openDiagram).map fun wire =>
        (openDiagram.diagram.wires wire).sig))
    (boundaryEnv : Env pre (openBoundaryClassSigs openDiagram)) :
    Env pre
      (((openRootLocalWires openDiagram) ++
          openBoundaryWires openDiagram).map fun wire =>
        (openDiagram.diagram.wires wire).sig) :=
  extendEnvironmentFor openDiagram.diagram
    (openBoundaryWires openDiagram)
    (openRootLocalWires openDiagram) values boundaryEnv

private theorem denote_finishRegionFor
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outerIds : List diagram.WireId)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre definitions)
    (outerEnv : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig)) :
    ∀ (localIds : List diagram.WireId)
      (body : Region definitions
        ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig)),
      denoteRegion pre definitionEnv outerEnv
          (finishRegionFor diagram outerIds localIds body) ↔
        ∃ values : WireValues pre
            (localIds.map fun wire => (diagram.wires wire).sig),
          denoteRegion pre definitionEnv
            (extendEnvironmentFor diagram outerIds localIds values outerEnv)
            body
  | [], body => by
      constructor
      · intro denotes
        exact ⟨.nil, denotes⟩
      · rintro ⟨values, denotes⟩
        cases values
        exact denotes
  | head :: tail, body => by
      rw [finishRegionFor, denote_finishRegionFor definitions diagram
        outerIds pre definitionEnv outerEnv tail]
      constructor
      · rintro ⟨tailValues, ⟨headValue, bodyDenotes⟩, _⟩
        exact ⟨.cons headValue tailValues, bodyDenotes⟩
      · rintro ⟨values, bodyDenotes⟩
        cases values with
        | cons headValue tailValues =>
            exact ⟨tailValues, ⟨headValue, bodyDenotes⟩, trivial⟩

theorem denote_finishRegion
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) (region : diagram.RegionId)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre definitions)
    (outerEnv : Env pre context.sigs)
    (body : Region definitions (context.extend region).sigs) :
    denoteRegion pre definitionEnv outerEnv
        (finishRegion diagram context region body) ↔
      ∃ values : WireValues pre
          ((diagram.wiresAt region).map fun wire =>
            (diagram.wires wire).sig),
        denoteRegion pre definitionEnv
          (extendEnvironment diagram context region values outerEnv) body :=
  denote_finishRegionFor definitions diagram context.ids pre definitionEnv
    outerEnv (diagram.wiresAt region) body

/--
Semantic characterization of a successfully compiled open root.  The theorem
exposes the deterministic node and child compilations and the fresh values for
root-local wires, while keeping the finishing implementation private.
-/
theorem denote_compileOpenRoot_components
    (definitions : List (List Sig))
    (openDiagram : OpenConcreteDiagram definitions.length)
    (body : Region definitions (openBoundaryClassSigs openDiagram))
    (compiled : compileOpenRoot? definitions openDiagram = some body)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre definitions)
    (boundaryEnv : Env pre (openBoundaryClassSigs openDiagram)) :
  denoteRegion pre definitionEnv boundaryEnv body ↔
      ∃ (nodes children : ItemSeq definitions
            (((openRootLocalWires openDiagram) ++
                openBoundaryWires openDiagram).map fun wire =>
              (openDiagram.diagram.wires wire).sig))
        (values : WireValues pre
          ((openRootLocalWires openDiagram).map fun wire =>
            (openDiagram.diagram.wires wire).sig)),
        compileNodes? definitions openDiagram.diagram
            ⟨openRootLocalWires openDiagram ++
              openBoundaryWires openDiagram⟩
            (openDiagram.diagram.nodesAt openDiagram.diagram.root) =
          some nodes ∧
        compileChildrenWith? definitions openDiagram.diagram
            (compileRegion? definitions openDiagram.diagram
              openDiagram.diagram.regionCount)
            ⟨openRootLocalWires openDiagram ++
              openBoundaryWires openDiagram⟩
            (openDiagram.diagram.childrenOf openDiagram.diagram.root) =
          some children ∧
        denoteRegion pre definitionEnv
          (extendOpenRootEnvironment openDiagram values boundaryEnv)
          (.mk (nodes.append children)) := by
  unfold compileOpenRoot? at compiled
  cases nodesOption :
      compileNodes? definitions openDiagram.diagram
        ⟨openRootLocalWires openDiagram ++ openBoundaryWires openDiagram⟩
        (openDiagram.diagram.nodesAt openDiagram.diagram.root) with
  | none =>
      simp [nodesOption] at compiled
  | some nodes =>
    cases childrenOption :
        compileChildrenWith? definitions openDiagram.diagram
          (compileRegion? definitions openDiagram.diagram
            openDiagram.diagram.regionCount)
          ⟨openRootLocalWires openDiagram ++ openBoundaryWires openDiagram⟩
          (openDiagram.diagram.childrenOf openDiagram.diagram.root) with
    | none =>
      simp [nodesOption, childrenOption] at compiled
    | some children =>
      have bodyEquality :
          finishRegionFor openDiagram.diagram
              (openBoundaryWires openDiagram)
              (openRootLocalWires openDiagram)
              (.mk (nodes.append children)) =
            body := by
        simpa [nodesOption, childrenOption] using compiled
      subst body
      have finishing :=
        denote_finishRegionFor definitions openDiagram.diagram
          (openBoundaryWires openDiagram) pre definitionEnv boundaryEnv
          (openRootLocalWires openDiagram) (.mk (nodes.append children))
      constructor
      · intro bodyDenotes
        obtain ⟨values, denotes⟩ := finishing.mp bodyDenotes
        exact ⟨nodes, children, values, rfl, rfl,
          denotes⟩
      · rintro ⟨otherNodes, otherChildren, values, otherNodesCompiled,
          otherChildrenCompiled, denotes⟩
        have nodesEquality : otherNodes = nodes :=
          Option.some.inj otherNodesCompiled |>.symm
        have childrenEquality : otherChildren = children :=
          Option.some.inj otherChildrenCompiled |>.symm
        subst otherNodes
        subst otherChildren
        exact finishing.mpr ⟨values, denotes⟩

end ConcreteElaboration

end VisualProof
