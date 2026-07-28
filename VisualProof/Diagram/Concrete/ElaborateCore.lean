import VisualProof.Diagram.Concrete.ElaborationSupport

namespace VisualProof

universe u

namespace ConcreteElaboration

private def resolveWireIn? (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) → (wire : diagram.WireId) →
      Option (Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig)
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveWireIn? diagram tail wire).map .there

private def resolveWire? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId) :
    Option (Var context.sigs (diagram.wires wire).sig) :=
  resolveWireIn? diagram context.ids wire

private def resolveExpected? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) : Option (Var context.sigs expected) :=
  if equality : (diagram.wires wire).sig = expected then
    (resolveWire? diagram context wire).map fun resolved =>
      equality ▸ resolved
  else
    none

private def EnvironmentsCorrespond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftContext : WireContext left)
    (rightContext : WireContext right)
    (leftEnv : Env pre leftContext.sigs)
    (rightEnv : Env pre rightContext.sigs) : Prop :=
  ∀ (wire : left.WireId) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (rightVar : Var rightContext.sigs expected),
    resolveExpected? left leftContext wire expected = some leftVar →
      resolveExpected? right rightContext (iso.wires wire) expected =
        some rightVar →
      leftEnv expected leftVar = rightEnv expected rightVar

private theorem empty_environments_correspond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right) (pre : PreModel) :
    EnvironmentsCorrespond iso
      (WireContext.empty left) (WireContext.empty right)
      (Env.empty : Env pre []) (Env.empty : Env pre []) := by
  intro wire expected leftVar rightVar leftResolved
  simp [resolveExpected?, resolveWire?, resolveWireIn?,
    WireContext.empty] at leftResolved

private def resolvePort? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId)
    (port : CPort) (expected : Sig) :
    Option (Var context.sigs expected) := do
  let wire ← diagram.endpointOwner? ⟨node, port⟩
  resolveExpected? diagram context wire expected

private def resolveArgs? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) :
    (args : List Sig) → (index : Nat) → Option (Vars context.sigs args)
  | [], _ => some .nil
  | sig :: rest, index => do
      let head ← resolvePort? diagram context node (.arg index) sig
      let tail ← resolveArgs? diagram context node rest (index + 1)
      pure (.cons head tail)

private def resolveIdentityPorts? (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig) :
    (remaining index : Nat) →
      Option { ports : List (Var context.sigs sig) //
        ports.length = remaining }
  | 0, _ => some ⟨[], rfl⟩
  | remaining + 1, index => do
      let head ← resolvePort? diagram context node (.identity index) sig
      let tail ← resolveIdentityPorts? diagram context node sig remaining (index + 1)
      pure ⟨head :: tail.val, by simp [tail.property]⟩

private theorem resolveIdentityPorts?_at
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

private theorem resolveIdentityPorts?_mem
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

private theorem resolveIdentityPorts?_member_of_resolved
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

private theorem identity_resolved_index_bound
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

private def definitionVarAt :
    (definitions : List (List Sig)) → (index : Fin definitions.length) →
      DefVar definitions (definitions.get index)
  | _ :: _, ⟨0, _⟩ => .here
  | _ :: rest, ⟨index + 1, bound⟩ =>
      .there (definitionVarAt rest ⟨index, Nat.lt_of_succ_lt_succ bound⟩)

private def compileNode? (definitions : List (List Sig))
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

inductive WireValues (pre : PreModel.{u}) : List Sig → Type u
  | nil : WireValues pre []
  | cons (head : pre.Domain sig) (tail : WireValues pre rest) :
      WireValues pre (sig :: rest)

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

private theorem resolveWire?_complete
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

private theorem resolveExpected?_sound_member
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

private theorem resolveExpected?_sound_signature
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

private abbrev wireOfVar (diagram : ConcreteDiagram definitionCount) :
    {ids : List diagram.WireId} → {sig : Sig} →
      Var (ids.map fun id => (diagram.wires id).sig) sig →
      diagram.WireId :=
  fun {ids} {_} value =>
    WireContext.origin diagram ids value

private def appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    {rightIds : List diagram.WireId} {sig : Sig} :
    (leftIds : List diagram.WireId) →
    Var (rightIds.map fun id => (diagram.wires id).sig) sig →
    Var ((leftIds ++ rightIds).map fun id => (diagram.wires id).sig) sig
  | [], value => value
  | _ :: tail, value => .there (appendRightVar diagram tail value)

private theorem wireOfVar_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (leftIds : List diagram.WireId)
    {rightIds : List diagram.WireId} {sig : Sig}
    (value : Var (rightIds.map fun id => (diagram.wires id).sig) sig) :
    wireOfVar diagram (appendRightVar diagram leftIds value) =
      wireOfVar diagram value := by
  induction leftIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [appendRightVar, wireOfVar,
        WireContext.origin] using induction

private def extendEnvironmentFor
    (diagram : ConcreteDiagram definitionCount)
    {pre : PreModel}
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
    WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig) →
    Env pre (outerIds.map fun wire => (diagram.wires wire).sig) →
    Env pre
      ((localIds ++ outerIds).map fun wire => (diagram.wires wire).sig)
  | [], .nil, outerEnv => outerEnv
  | _ :: tail, .cons head rest, outerEnv =>
      (extendEnvironmentFor diagram outerIds tail rest outerEnv).extend head

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

def extendEnvironment
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId)
    {pre : PreModel}
    (values : WireValues pre
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs) :
    Env pre (context.extend region).sigs :=
  extendEnvironmentFor diagram context.ids (diagram.wiresAt region)
    values outerEnv

private theorem extendEnvironmentFor_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    {pre : PreModel}
    (values : WireValues pre
      (localIds.map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre
      (outerIds.map fun wire => (diagram.wires wire).sig))
    {sig : Sig}
    (value : Var
      (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    extendEnvironmentFor diagram outerIds localIds values outerEnv sig
        (appendRightVar diagram localIds value) =
      outerEnv sig value := by
  induction localIds with
  | nil =>
      cases values
      rfl
  | cons head tail induction =>
      cases values with
      | cons headValue tailValues =>
          exact induction tailValues

def valuesFromEnvironmentFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
    Env pre ((localIds ++ outerIds).map fun wire =>
      (diagram.wires wire).sig) →
    WireValues pre (localIds.map fun wire => (diagram.wires wire).sig)
  | [], _ => .nil
  | _ :: tail, env =>
      .cons (env _ .here)
        (valuesFromEnvironmentFor diagram outerIds tail
          (fun sig value => env sig (.there value)))

theorem extendEnvironmentFor_from
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (env : Env pre ((localIds ++ outerIds).map fun wire =>
      (diagram.wires wire).sig))
    (outerEnv : Env pre (outerIds.map fun wire => (diagram.wires wire).sig))
    (agrees : ∀ sig (value : Var
      (outerIds.map fun wire => (diagram.wires wire).sig) sig),
      env sig (appendRightVar diagram localIds value) = outerEnv sig value) :
    extendEnvironmentFor diagram outerIds localIds
        (valuesFromEnvironmentFor diagram outerIds localIds env) outerEnv =
      env := by
  induction localIds with
  | nil =>
      funext sig value
      exact (agrees sig value).symm
  | cons head tail induction =>
      funext sig value
      cases value with
      | here => rfl
      | there value =>
          exact congrFun (congrFun
            (induction (fun sig value => env sig (.there value))
              (by
                intro sig outer
                exact agrees sig outer)) sig) value

private theorem extendEnvironment_appendRightVar
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId)
    {pre : PreModel}
    (values : WireValues pre
      ((diagram.wiresAt region).map fun wire => (diagram.wires wire).sig))
    (outerEnv : Env pre context.sigs)
    {sig : Sig} (value : Var context.sigs sig) :
    extendEnvironment diagram context region values outerEnv sig
        (appendRightVar diagram (diagram.wiresAt region) value) =
      outerEnv sig value := by
  exact extendEnvironmentFor_appendRightVar diagram context.ids
    (diagram.wiresAt region) values outerEnv value

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

private theorem wireOfVar_member
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    wireOfVar diagram value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail ih =>
      cases value with
      | here =>
          simp [wireOfVar, WireContext.origin]
      | there value =>
          simpa [wireOfVar, WireContext.origin] using
            List.mem_cons_of_mem head (ih value)

private theorem wireOfVar_signature
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    (diagram.wires (wireOfVar diagram value)).sig = sig := by
  induction ids with
  | nil => nomatch value
  | cons head tail ih =>
      cases value with
      | here =>
          simp [wireOfVar, WireContext.origin]
      | there value =>
          simpa [wireOfVar, WireContext.origin] using ih value

private theorem cast_var_there
    {left right : Sig} (equality : left = right)
    (value : Var context left) :
    Var.there (equality ▸ value) =
      equality ▸ (Var.there value : Var (head :: context) left) := by
  cases equality
  rfl

private theorem cast_var_cancel
    {left right : Sig} (equality : left = right)
    (value : Var context right) :
    equality ▸ (equality.symm ▸ value) = value := by
  cases equality
  rfl

private theorem wireOfVar_resolveWireIn
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) (wire : diagram.WireId)
    {resolved :
      Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig}
    (equation : resolveWireIn? diagram ids wire = some resolved) :
    wireOfVar diagram resolved = wire := by
  induction ids with
  | nil => simp [resolveWireIn?] at equation
  | cons head tail ih =>
      by_cases equality : wire = head
      · subst wire
        simp [resolveWireIn?] at equation
        subst resolved
        simp [wireOfVar, WireContext.origin]
      · cases tailEquation : resolveWireIn? diagram tail wire with
        | none =>
            simp [resolveWireIn?, equality, tailEquation] at equation
        | some tailVar =>
            have resolvedEquality : .there tailVar = resolved := by
              exact Option.some.inj (by
                simpa [resolveWireIn?, equality, tailEquation] using equation)
            subst resolved
            simpa [wireOfVar, WireContext.origin] using
              ih tailEquation

private theorem wireOfVar_resolveExpected
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) {resolved : Var context.sigs expected}
    (equation :
      resolveExpected? diagram context wire expected = some resolved) :
    wireOfVar diagram resolved = wire := by
  unfold resolveExpected? at equation
  split at equation
  · rename_i signature
    subst expected
    cases wireEquation : resolveWire? diagram context wire with
    | none => simp [wireEquation] at equation
    | some wireVar =>
        have variableEquality : wireVar = resolved := by
          exact Option.some.inj (by simpa [wireEquation] using equation)
        subst resolved
        exact wireOfVar_resolveWireIn diagram context.ids wire
          wireEquation
  · simp at equation

private theorem resolveWireIn?_wireOfVar
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} (nodup : ids.Nodup)
    {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    resolveWireIn? diagram ids (wireOfVar diagram value) =
      some ((wireOfVar_signature diagram value).symm ▸ value) := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          simp [resolveWireIn?, wireOfVar, WireContext.origin]
      | there value =>
          rw [List.nodup_cons] at nodup
          have tailNodup := nodup.2
          have tailMember := wireOfVar_member diagram value
          have notHead : wireOfVar diagram value ≠ head := by
            intro equality
            exact nodup.1 (by simpa [equality] using tailMember)
          have tailResolved := induction tailNodup value
          simp only [resolveWireIn?, wireOfVar, WireContext.origin,
            notHead, ↓reduceDIte, tailResolved, Option.map_some]
          congr 1
          exact cast_var_there
            (wireOfVar_signature diagram value).symm value

private theorem resolveExpected?_wireOfVar
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (nodup : context.ids.Nodup)
    {sig : Sig} (value : Var context.sigs sig) :
    resolveExpected? diagram context (wireOfVar diagram value) sig =
      some value := by
  have signature := wireOfVar_signature diagram value
  unfold resolveExpected?
  rw [dif_pos signature]
  simp only [resolveWire?]
  rw [resolveWireIn?_wireOfVar diagram nodup value]
  change some (signature ▸ (signature.symm ▸ value)) = some value
  rw [cast_var_cancel]

private theorem resolvePort?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    {port : CPort}
    {expected : Sig}
    (targetRequired : port ∈ right.requiredPorts rightNode)
    (forwardIncident : ∀ (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {resolved : Var leftContext.sigs expected}
    (sourceResolved :
      resolvePort? left leftContext leftNode port expected =
        some resolved) :
    resolvePort? right rightContext rightNode port expected =
      some (rho resolved) := by
  unfold resolvePort? at sourceResolved ⊢
  cases sourceOwner :
      left.endpointOwner? ⟨leftNode, port⟩ with
  | none =>
      simp [sourceOwner] at sourceResolved
  | some sourceWire =>
      have sourceExpected :
          resolveExpected? left leftContext sourceWire expected =
            some resolved := by
        simpa [sourceOwner] using sourceResolved
      have sourceIncident :=
        ConcreteDiagram.endpointOwner?_incident left
          ⟨leftNode, port⟩ sourceWire sourceOwner
      have targetIncident :=
        forwardIncident sourceWire sourceIncident
      have targetOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident definitions right
          rightWellFormed rightNode port targetRequired
          (wireMap sourceWire) targetIncident
      rw [targetOwner]
      have targetResolved :=
        resolveExpected?_wireOfVar right rightContext
          rightContextNodup (rho resolved)
      have sourceOrigin :=
        wireOfVar_resolveExpected left leftContext sourceWire expected
          sourceExpected
      have mappedOrigin := contextAction resolved
      change
        wireOfVar right (rho resolved) =
          wireMap (wireOfVar left resolved) at mappedOrigin
      rw [mappedOrigin, sourceOrigin] at targetResolved
      exact targetResolved

private theorem resolveArgs?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    (args : List Sig)
    (index : Nat)
    (targetRequired : ∀ offset (_bound : offset < args.length),
      CPort.arg (index + offset) ∈
        right.requiredPorts rightNode)
    {resolved : Vars leftContext.sigs args}
    (sourceResolved :
      resolveArgs? left leftContext leftNode args index =
        some resolved) :
    resolveArgs? right rightContext rightNode args index =
      some (resolved.rename rho) := by
  induction args generalizing index with
  | nil =>
      have resolvedEquality :
          (.nil : Vars leftContext.sigs []) = resolved :=
        Option.some.inj sourceResolved
      subst resolved
      rfl
  | cons sig rest induction =>
      cases headEquation :
          resolvePort? left leftContext leftNode (.arg index) sig with
      | none =>
          simp [resolveArgs?, headEquation] at sourceResolved
      | some head =>
          cases tailEquation :
              resolveArgs? left leftContext leftNode rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation]
                at sourceResolved
          | some tail =>
              have resolvedEquality :
                  (Vars.cons head tail :
                    Vars leftContext.sigs (sig :: rest)) =
                    resolved := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    sourceResolved)
              subst resolved
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (targetRequired 0 (by simp))
                  (forwardIncident (.arg index))
                  headEquation
              have targetTail :=
                induction (index := index + 1)
                  (resolved := tail)
                  (fun offset bound => by
                    have required :=
                      targetRequired (offset + 1) (by simp; omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  tailEquation
              have targetHead' :
                  resolvePort? right rightContext rightNode
                      (.arg index) sig =
                    some (rho head) := by
                simpa using targetHead
              simp [resolveArgs?, targetHead', targetTail, Vars.rename]

private theorem resolveIdentityPorts?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    (sig : Sig)
    (remaining index : Nat)
    (targetRequired : ∀ offset (_bound : offset < remaining),
      CPort.identity (index + offset) ∈
        right.requiredPorts rightNode)
    {resolved : { ports : List (Var leftContext.sigs sig) //
      ports.length = remaining }}
    (sourceResolved :
      resolveIdentityPorts? left leftContext leftNode sig remaining index =
        some resolved) :
    resolveIdentityPorts? right rightContext rightNode sig remaining index =
      some
        ⟨resolved.val.map (rho (sig := sig)), by
          simpa [resolved.property]⟩ := by
  induction remaining generalizing index with
  | zero =>
      have portsEmpty : resolved.val = [] :=
        List.length_eq_zero_iff.mp resolved.property
      apply congrArg some
      apply Subtype.ext
      simp [resolveIdentityPorts?, portsEmpty]
  | succ remaining induction =>
      cases headEquation :
          resolvePort? left leftContext leftNode
            (.identity index) sig with
      | none =>
          simp [resolveIdentityPorts?, headEquation] at sourceResolved
      | some head =>
          cases tailEquation :
              resolveIdentityPorts? left leftContext leftNode sig
                remaining (index + 1) with
          | none =>
              simp [resolveIdentityPorts?, headEquation, tailEquation]
                at sourceResolved
          | some tail =>
              have resolvedEquality :
                  (⟨head :: tail.val, by simp [tail.property]⟩ :
                    { ports : List (Var leftContext.sigs sig) //
                      ports.length = remaining + 1 }) =
                    resolved := by
                exact Option.some.inj (by
                  simpa [resolveIdentityPorts?, headEquation,
                    tailEquation] using sourceResolved)
              subst resolved
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (targetRequired 0 (by omega))
                  (forwardIncident (.identity index))
                  headEquation
              have targetTail :=
                induction (index := index + 1)
                  (resolved := tail)
                  (fun offset bound => by
                    have required :=
                      targetRequired (offset + 1) (by omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  tailEquation
              have targetHead' :
                  resolvePort? right rightContext rightNode
                      (.identity index) sig =
                    some (rho head) := by
                simpa using targetHead
              simp [resolveIdentityPorts?, targetHead', targetTail]

private theorem compileNode?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    (regionMap : left.RegionId → right.RegionId)
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (nodeShape :
      right.nodes rightNode =
        match left.nodes leftNode with
        | .atom region args =>
            .atom (regionMap region) args
        | .ref region definition args =>
            .ref (regionMap region) definition args
        | .identity region sig arity =>
            .identity (regionMap region) sig arity)
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {sourceItem : Item definitions leftContext.sigs}
    (sourceCompiled :
      compileNode? definitions left leftContext leftNode =
        some sourceItem) :
    compileNode? definitions right rightContext rightNode =
      some (sourceItem.renameWires rho) := by
  cases sourceNodeData : left.nodes leftNode with
  | atom sourceRegion args =>
      have targetNodeData :
          right.nodes rightNode =
            .atom (regionMap sourceRegion) args := by
        rw [nodeShape, sourceNodeData]
      cases headEquation :
          resolvePort? left leftContext leftNode .head (.rel args) with
      | none =>
          simp [compileNode?, sourceNodeData, headEquation]
            at sourceCompiled
      | some head =>
          cases argsEquation :
              resolveArgs? left leftContext leftNode args 0 with
          | none =>
              simp [compileNode?, sourceNodeData, headEquation,
                argsEquation] at sourceCompiled
          | some arguments =>
              have sourceItemEquality :
                  (Item.atom head arguments :
                    Item definitions leftContext.sigs) =
                    sourceItem := by
                exact Option.some.inj (by
                  simpa [compileNode?, sourceNodeData, headEquation,
                    argsEquation] using sourceCompiled)
              subst sourceItem
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (by
                    simp [ConcreteDiagram.requiredPorts,
                      targetNodeData])
                  (forwardIncident .head)
                  headEquation
              have targetArguments :=
                resolveArgs?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction forwardIncident
                  args 0
                  (by
                    intro offset bound
                    simp [ConcreteDiagram.requiredPorts,
                      targetNodeData, bound])
                  argsEquation
              simp [compileNode?, targetNodeData, targetHead,
                targetArguments, Item.renameWires]
  | ref sourceRegion definition args =>
      have targetNodeData :
          right.nodes rightNode =
            .ref (regionMap sourceRegion) definition args := by
        rw [nodeShape, sourceNodeData]
      simp only [compileNode?, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i signature
        cases argsEquation :
            resolveArgs? left leftContext leftNode args 0 with
        | none =>
            simp [argsEquation] at sourceCompiled
        | some arguments =>
            let reference : DefVar definitions args :=
              signature ▸ definitionVarAt definitions definition
            have sourceItemEquality :
                (Item.named reference arguments :
                  Item definitions leftContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [argsEquation, reference] using sourceCompiled)
            subst sourceItem
            have targetArguments :=
              resolveArgs?_map rightWellFormed rightContextNodup
                rho wireMap contextAction forwardIncident
                args 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    targetNodeData, bound])
                argsEquation
            simp only [compileNode?, targetNodeData]
            split
            · simp [targetArguments, reference,
                Item.renameWires]
            · contradiction
      · simp at sourceCompiled
  | identity sourceRegion sig arity =>
      have targetNodeData :
          right.nodes rightNode =
            .identity (regionMap sourceRegion) sig arity := by
        rw [nodeShape, sourceNodeData]
      simp only [compileNode?, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i arityWitness
        cases portsEquation :
            resolveIdentityPorts? left leftContext leftNode sig arity 0 with
        | none =>
            simp [portsEquation] at sourceCompiled
        | some ports =>
            have sourceItemEquality :
                (Item.identity sig ports.val (by
                  simpa [ports.property] using arityWitness) :
                  Item definitions leftContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [portsEquation] using sourceCompiled)
            subst sourceItem
            have targetPorts :=
              resolveIdentityPorts?_map rightWellFormed
                rightContextNodup rho wireMap contextAction
                forwardIncident sig arity 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    targetNodeData, bound])
                portsEquation
            simp [compileNode?, targetNodeData, arityWitness,
              targetPorts, Item.renameWires]
      · simp at sourceCompiled

/--
Compile one structurally copied node under an exact context renaming.  The
target compilation is generated by this theorem; callers provide only the
wire/node incidence facts that make the copied node visible.
-/
theorem compileNodes?_singleton_natural
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (_wireSignature : ∀ wire,
      (right.wires (wireMap wire)).sig =
        (left.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    (regionMap : left.RegionId → right.RegionId)
    (leftNode : left.NodeId)
    (rightNode : right.NodeId)
    (nodeShape :
      right.nodes rightNode =
        match left.nodes leftNode with
        | .atom region args =>
            .atom (regionMap region) args
        | .ref region definition args =>
            .ref (regionMap region) definition args
        | .identity region sig arity =>
            .identity (regionMap region) sig arity)
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {sourceItems : ItemSeq definitions leftContext.sigs}
    (sourceCompiled :
      compileNodes? definitions left leftContext [leftNode] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions rightContext.sigs,
      compileNodes? definitions right rightContext [rightNode] =
          some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  cases sourceNodeEquation :
      compileNode? definitions left leftContext leftNode with
  | none =>
      simp [compileNodes?, sourceNodeEquation] at sourceCompiled
  | some sourceItem =>
      have sourceItemsEquality :
          (ItemSeq.cons sourceItem .nil :
            ItemSeq definitions leftContext.sigs) =
            sourceItems := by
        exact Option.some.inj (by
          simpa [compileNodes?, sourceNodeEquation] using
            sourceCompiled)
      subst sourceItems
      have targetNodeEquation :=
        compileNode?_map rightWellFormed rightContextNodup
          rho wireMap contextAction regionMap nodeShape
          forwardIncident sourceNodeEquation
      refine
        ⟨.cons (sourceItem.renameWires rho) .nil, ?_, rfl⟩
      simp [compileNodes?, targetNodeEquation]

private def binaryIdentityTemplate (definitionCount : Nat) (sig : Sig) :
    ConcreteDiagram definitionCount where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := ⟨0, by omega⟩
  regions := fun _ => .sheet
  nodes := fun _ => .identity ⟨0, by omega⟩ sig 2
  wires
    | ⟨0, _⟩ =>
        { sig := sig
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := sig
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .identity 1⟩] }
private def binaryIdentityTemplateContext
    (definitionCount : Nat) (sig : Sig) :
    WireContext (binaryIdentityTemplate definitionCount sig) :=
  ⟨[⟨0, by simp [binaryIdentityTemplate]⟩,
      ⟨1, by simp [binaryIdentityTemplate]⟩]⟩
private theorem binaryIdentityTemplateContext_sigs
    (definitionCount : Nat) (sig : Sig) :
    (binaryIdentityTemplateContext definitionCount sig).sigs =
      [sig, sig] := by
  rfl
private def binaryIdentityRenaming
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {context : WireContext diagram}
    {sig : Sig}
    (first second : Var context.sigs sig) :
    WireRenaming [sig, sig] context.sigs :=
  fun {_} value =>
    match value with
    | .here => first
    | .there .here => second
theorem WireContext.origin_signature
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    (diagram.wires (WireContext.origin diagram ids value)).sig = sig := by
  induction ids with
  | nil => exact nomatch value
  | cons head tail induction =>
      cases value with
      | here => rfl
      | there rest => exact induction rest
private def binaryIdentityTemplateWireMap
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    (sig : Sig) (first second : diagram.WireId) :
    (binaryIdentityTemplate definitions.length sig).WireId →
      diagram.WireId
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
/--
Compile a binary concrete identity to the exact intrinsic binary identity
between the two supplied context variables. The executable compiler remains
the sole constructor of the result; the premises expose only checked shape,
incidence, and concrete-origin evidence.
-/
theorem compileNodes?_binaryIdentity_singleton
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    (wellFormed : diagram.WellFormed definitions)
    {context : WireContext diagram}
    (contextNodup : context.ids.Nodup)
    {sig : Sig}
    (first second : Var context.sigs sig)
    (firstWire secondWire : diagram.WireId)
    (firstOrigin : WireContext.origin diagram context.ids first = firstWire)
    (secondOrigin : WireContext.origin diagram context.ids second = secondWire)
    (region : diagram.RegionId)
    (node : diagram.NodeId)
    (nodeShape : diagram.nodes node = .identity region sig 2)
    (firstIncident : (⟨node, .identity 0⟩ :
      CEndpoint diagram.nodeCount) ∈ (diagram.wires firstWire).endpoints)
    (secondIncident : (⟨node, .identity 1⟩ :
      CEndpoint diagram.nodeCount) ∈ (diagram.wires secondWire).endpoints) :
    compileNodes? definitions diagram context [node] =
      some
        (.cons (Item.binaryIdentity sig first second) .nil) := by
  let template := binaryIdentityTemplate definitions.length sig
  let templateContext :=
    binaryIdentityTemplateContext definitions.length sig
  let rho : WireRenaming templateContext.sigs context.sigs :=
    fun {_} value =>
      binaryIdentityRenaming
        (definitions := definitions) (diagram := diagram)
        (context := context) (sig := sig) first second
        (binaryIdentityTemplateContext_sigs definitions.length sig ▸ value)
  let wireMap :=
    binaryIdentityTemplateWireMap
      (definitions := definitions) sig firstWire secondWire
  have firstSignature : (diagram.wires firstWire).sig = sig := by
    rw [← firstOrigin]
    exact WireContext.origin_signature diagram context.ids first
  have secondSignature : (diagram.wires secondWire).sig = sig := by
    rw [← secondOrigin]
    exact WireContext.origin_signature diagram context.ids second
  have sourceOwnerFirst : template.endpointOwner?
      ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, .identity 0⟩ =
        some ⟨0, by simp [template, binaryIdentityTemplate]⟩ := by
    unfold ConcreteDiagram.endpointOwner?
    change
      Option.map Prod.fst
          ([((⟨0, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)),
            ((⟨1, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))].find?
            (fun occurrence =>
              occurrence.2 ==
                (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1))) =
        some (⟨0, by omega⟩ : Fin 2)
    native_decide
  have sourceOwnerSecond : template.endpointOwner?
      ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, .identity 1⟩ =
        some ⟨1, by simp [template, binaryIdentityTemplate]⟩ := by
    unfold ConcreteDiagram.endpointOwner?
    change
      Option.map Prod.fst
          ([((⟨0, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)),
            ((⟨1, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))].find?
            (fun occurrence =>
              occurrence.2 ==
                (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))) =
        some (⟨1, by omega⟩ : Fin 2)
    native_decide
  have sourceResolveFirst : resolvePort? template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ (.identity 0) sig =
        some (.here : Var templateContext.sigs sig) := by
    unfold resolvePort?
    rw [sourceOwnerFirst]
    simp [resolveExpected?, resolveWire?, resolveWireIn?,
      template, templateContext, binaryIdentityTemplate,
      binaryIdentityTemplateContext]
  have sourceResolveSecond : resolvePort? template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ (.identity 1) sig =
        some (.there .here : Var templateContext.sigs sig) := by
    unfold resolvePort?
    rw [sourceOwnerSecond]
    simp [resolveExpected?, resolveWire?, resolveWireIn?,
      template, templateContext, binaryIdentityTemplate,
      binaryIdentityTemplateContext]
  have sourceNodeCompiled : compileNode? definitions template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ =
        some (Item.binaryIdentity sig .here (.there .here)) := by
    unfold compileNode?
    rw [show
      template.nodes
          ⟨0, by simp [template, binaryIdentityTemplate]⟩ =
        .identity ⟨0, by simp [template, binaryIdentityTemplate]⟩ sig 2 by
          rfl]
    simp only [Nat.reduceLeDiff, ↓reduceDIte]
    change
      (resolveIdentityPorts? template templateContext
          ⟨0, by simp [template, binaryIdentityTemplate]⟩ sig 2 0).bind
          (fun ports =>
            some (.identity sig ports.val (by
              exact Nat.le_of_eq ports.property.symm))) =
        some (Item.binaryIdentity sig .here (.there .here))
    simp only [resolveIdentityPorts?, sourceResolveFirst,
      sourceResolveSecond, Option.bind_some]
    unfold Item.binaryIdentity
    congr
  have sourceCompiled : compileNodes? definitions template templateContext
      [⟨0, by simp [template, binaryIdentityTemplate]⟩] =
        some
          (.cons (Item.binaryIdentity sig .here (.there .here)) .nil) := by
    unfold compileNodes?
    rw [sourceNodeCompiled]
    rfl
  obtain ⟨targetItems, targetCompiled, targetEquality⟩ :=
    compileNodes?_singleton_natural wellFormed contextNodup rho wireMap
      (by
        intro wire
        rcases wire with ⟨value, bound⟩
        have valueCases : value = 0 ∨ value = 1 := by
          simp [template, binaryIdentityTemplate] at bound
          omega
        rcases valueCases with rfl | rfl <;>
          simp [wireMap, binaryIdentityTemplateWireMap, template,
            binaryIdentityTemplate, firstSignature, secondSignature])
      (by
        intro mappedSig value
        change Var [sig, sig] mappedSig at value
        cases value with
        | here =>
            simpa [rho, binaryIdentityRenaming, wireMap,
              binaryIdentityTemplateWireMap, templateContext,
              binaryIdentityTemplateContext, template,
              binaryIdentityTemplate] using firstOrigin
        | there tail =>
            cases tail with
            | here =>
                simpa [rho, binaryIdentityRenaming, wireMap,
                  binaryIdentityTemplateWireMap, templateContext,
                  binaryIdentityTemplateContext, template,
                  binaryIdentityTemplate] using secondOrigin
            | there impossible => exact nomatch impossible)
      (fun _ => region)
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ node
      (by
        simpa [template, binaryIdentityTemplate] using nodeShape)
      (by
        intro port wire incident
        rcases wire with ⟨value, bound⟩
        have valueCases : value = 0 ∨ value = 1 := by
          simp [template, binaryIdentityTemplate] at bound
          omega
        rcases valueCases with rfl | rfl
        · have portEquality : port = .identity 0 := by
            have endpointEquality :
                (⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, port⟩ :
                    CEndpoint template.nodeCount) =
                  ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩,
                    .identity 0⟩ := by
              change
                (⟨⟨0, by omega⟩, port⟩ : CEndpoint 1) ∈
                  [(⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)]
                at incident
              exact List.mem_singleton.mp incident
            exact congrArg CEndpoint.port endpointEquality
          subst port
          simpa [wireMap, binaryIdentityTemplateWireMap] using firstIncident
        · have portEquality : port = .identity 1 := by
            have endpointEquality :
                (⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, port⟩ :
                    CEndpoint template.nodeCount) =
                  ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩,
                    .identity 1⟩ := by
              change
                (⟨⟨0, by omega⟩, port⟩ : CEndpoint 1) ∈
                  [(⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1)]
                at incident
              exact List.mem_singleton.mp incident
            exact congrArg CEndpoint.port endpointEquality
          subst port
          simpa [wireMap, binaryIdentityTemplateWireMap] using secondIncident)
      sourceCompiled
  rw [targetCompiled]
  congr 1
private theorem resolveExpected?_pair
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (wire : left.WireId) (expected : Sig)
    (member : wire ∈ leftContext.ids)
    (signature : (left.wires wire).sig = expected) :
    ∃ leftVar rightVar,
      resolveExpected? left leftContext wire expected = some leftVar ∧
        resolveExpected? right rightContext (iso.wires wire) expected =
          some rightVar := by
  obtain ⟨leftVar, leftResolved⟩ :=
    resolveWire?_complete left leftContext wire member
  obtain ⟨rightVar, rightResolved⟩ :=
    resolveWire?_complete right rightContext (iso.wires wire)
      (contexts.forward wire member)
  have targetSignature :
      (right.wires (iso.wires wire)).sig = expected :=
    (iso.wire_signature wire).trans signature
  refine ⟨signature ▸ leftVar, targetSignature ▸ rightVar, ?_, ?_⟩
  · simp [resolveExpected?, signature, leftResolved]
  · simp [resolveExpected?, targetSignature, rightResolved]

private theorem sourceVar_for_target_exists
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    ∃ leftVar,
      resolveExpected? left leftContext
          (iso.wires.symm (wireOfVar right rightVar)) sig =
        some leftVar := by
  let targetWire := wireOfVar right rightVar
  let sourceWire := iso.wires.symm targetWire
  have targetMember : targetWire ∈ rightContext.ids :=
    wireOfVar_member right rightVar
  have sourceMember : sourceWire ∈ leftContext.ids :=
    contexts.backward targetWire targetMember
  have targetSignature : (right.wires targetWire).sig = sig :=
    wireOfVar_signature right rightVar
  have mappedWire : iso.wires sourceWire = targetWire :=
    iso.wires.right_inv targetWire
  have signatureTransport := iso.wire_signature sourceWire
  rw [mappedWire] at signatureTransport
  have sourceSignature : (left.wires sourceWire).sig = sig :=
    signatureTransport.symm.trans targetSignature
  obtain ⟨leftVar, _, leftResolved, _⟩ :=
    resolveExpected?_pair iso contexts sourceWire sig sourceMember
      sourceSignature
  exact ⟨leftVar, leftResolved⟩

private noncomputable def pullVar
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    Var leftContext.sigs sig :=
  Classical.choose (sourceVar_for_target_exists iso contexts rightVar)

private theorem pullVar_resolves
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    resolveExpected? left leftContext
        (iso.wires.symm (wireOfVar right rightVar)) sig =
      some (pullVar iso contexts rightVar) :=
  Classical.choose_spec (sourceVar_for_target_exists iso contexts rightVar)

noncomputable def pullEnvironment
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel.{u}}
    (leftEnv : Env pre leftContext.sigs) :
    Env pre rightContext.sigs :=
  fun sig rightVar => leftEnv sig (pullVar iso contexts rightVar)

theorem pull_environments_correspond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (leftEnv : Env pre leftContext.sigs) :
    EnvironmentsCorrespond iso leftContext rightContext leftEnv
      (pullEnvironment iso contexts leftEnv) := by
  intro wire expected leftVar rightVar leftResolved rightResolved
  have targetWire :
      wireOfVar right rightVar = iso.wires wire :=
    wireOfVar_resolveExpected right rightContext (iso.wires wire) expected
      rightResolved
  have sourceWire :
      iso.wires.symm (wireOfVar right rightVar) = wire := by
    rw [targetWire]
    exact iso.wires.left_inv wire
  have pulledResolved := pullVar_resolves iso contexts rightVar
  rw [sourceWire] at pulledResolved
  have variableEquality : pullVar iso contexts rightVar = leftVar :=
    Option.some.inj (pulledResolved.symm.trans leftResolved)
  simp only [pullEnvironment]
  exact congrArg (leftEnv expected) variableEquality.symm

theorem pullEnvironment_roundtrip
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (leftNodup : leftContext.ids.Nodup)
    {pre : PreModel.{u}}
    (leftEnv : Env pre leftContext.sigs) :
    pullEnvironment iso.symm contexts.symm
        (pullEnvironment iso contexts leftEnv) = leftEnv := by
  funext sig leftVar
  let rightVar := pullVar iso.symm contexts.symm leftVar
  have rightResolved := pullVar_resolves iso.symm contexts.symm leftVar
  have rightWire :
      wireOfVar right rightVar = iso.wires (wireOfVar left leftVar) := by
    simpa [ConcreteIso.symm] using
      wireOfVar_resolveExpected right rightContext
        (iso.wires (wireOfVar left leftVar)) sig rightResolved
  have forwardResolved := pullVar_resolves iso contexts rightVar
  have sourceWire :
      iso.wires.symm (wireOfVar right rightVar) =
        wireOfVar left leftVar := by
    rw [rightWire]
    exact iso.wires.left_inv _
  rw [sourceWire] at forwardResolved
  have originalResolved :=
    resolveExpected?_wireOfVar left leftContext leftNodup leftVar
  have variableEquality : pullVar iso contexts rightVar = leftVar :=
    Option.some.inj (forwardResolved.symm.trans originalResolved)
  simp only [pullEnvironment]
  exact congrArg (leftEnv sig) variableEquality

theorem pullEnvironment_extend_agrees
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (region : left.RegionId)
    (leftExtendedNodup : (leftContext.extend region).ids.Nodup)
    {pre : PreModel}
    (leftOuter : Env pre leftContext.sigs)
    (leftValues : WireValues pre
      ((left.wiresAt region).map fun wire => (left.wires wire).sig))
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    pullEnvironment iso (extend_contexts_correspond iso contexts region)
        (extendEnvironment left leftContext region leftValues leftOuter) sig
        (appendRightVar right
          (right.wiresAt (iso.regions region)) rightVar) =
      pullEnvironment iso contexts leftOuter sig rightVar := by
  let extendedContexts := extend_contexts_correspond iso contexts region
  let rightExtendedVar :=
    appendRightVar right (right.wiresAt (iso.regions region)) rightVar
  let leftOuterVar := pullVar iso contexts rightVar
  let leftExtendedVar :=
    appendRightVar left (left.wiresAt region) leftOuterVar
  have rightWire :
      wireOfVar right rightExtendedVar = wireOfVar right rightVar :=
    wireOfVar_appendRightVar right
      (right.wiresAt (iso.regions region)) rightVar
  have leftWire :
      wireOfVar left leftExtendedVar = wireOfVar left leftOuterVar :=
    wireOfVar_appendRightVar left (left.wiresAt region) leftOuterVar
  have leftOuterResolved := pullVar_resolves iso contexts rightVar
  have leftOuterWire :
      wireOfVar left leftOuterVar =
        iso.wires.symm (wireOfVar right rightVar) :=
    wireOfVar_resolveExpected left leftContext
      (iso.wires.symm (wireOfVar right rightVar)) sig leftOuterResolved
  have correspondingWire :
      iso.wires.symm (wireOfVar right rightExtendedVar) =
        wireOfVar left leftExtendedVar := by
    rw [rightWire, leftWire, leftOuterWire]
  have pulledResolved :=
    pullVar_resolves iso extendedContexts rightExtendedVar
  have appendedResolved :=
    resolveExpected?_wireOfVar left (leftContext.extend region)
      leftExtendedNodup leftExtendedVar
  have pulledResolved' :
      resolveExpected? left (leftContext.extend region)
          (wireOfVar left leftExtendedVar) sig =
        some (pullVar iso extendedContexts rightExtendedVar) := by
    calc
      resolveExpected? left (leftContext.extend region)
          (wireOfVar left leftExtendedVar) sig =
          resolveExpected? left (leftContext.extend region)
            (iso.wires.symm (wireOfVar right rightExtendedVar)) sig :=
        congrArg
          (fun wire =>
            resolveExpected? left (leftContext.extend region) wire sig)
          correspondingWire.symm
      _ = some (pullVar iso extendedContexts rightExtendedVar) :=
        pulledResolved
  have variableEquality :
      pullVar iso extendedContexts rightExtendedVar = leftExtendedVar :=
    Option.some.inj (pulledResolved'.symm.trans appendedResolved)
  simp only [pullEnvironment]
  rw [variableEquality]
  exact extendEnvironment_appendRightVar left leftContext region leftValues
    leftOuter leftOuterVar

private theorem resolveExpected?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    (wire : left.WireId) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolveExpected? left leftContext wire expected = some leftVar) :
    ∃ rightVar,
      resolveExpected? right rightContext (iso.wires wire) expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  have member :=
    resolveExpected?_sound_member left leftContext wire expected leftResolved
  have signature :=
    resolveExpected?_sound_signature left leftContext wire expected leftResolved
  obtain ⟨leftVar', rightVar, leftEquation, rightEquation⟩ :=
    resolveExpected?_pair iso contexts wire expected member signature
  have variableEquality : leftVar' = leftVar := by
    exact Option.some.inj (leftEquation.symm.trans leftResolved)
  subst leftVar'
  exact ⟨rightVar, rightEquation,
    envs wire expected leftVar rightVar leftResolved rightEquation⟩

private theorem resolveIdentityPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (index : Nat) (leftVar : Var leftContext.sigs sig)
    (leftResolved :
      resolvePort? left leftContext node (.identity index) sig =
        some leftVar) :
    ∃ targetIndex rightVar,
      resolvePort? right rightContext (iso.nodes node)
          (.identity targetIndex) sig = some rightVar ∧
      leftEnv sig leftVar = rightEnv sig rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, .identity index⟩ with
  | none =>
      simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire sig = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      obtain ⟨targetIndex, targetOwner⟩ :=
        iso.identity_owner_forward rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire sig
          leftVar expectedEquation
      refine ⟨targetIndex, rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

private theorem resolveIdentityPort?_backward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (targetIndex : Nat) (rightVar : Var rightContext.sigs sig)
    (rightResolved :
      resolvePort? right rightContext (iso.nodes node)
          (.identity targetIndex) sig = some rightVar) :
    ∃ sourceIndex leftVar,
      resolvePort? left leftContext node (.identity sourceIndex) sig =
          some leftVar ∧
      leftEnv sig leftVar = rightEnv sig rightVar := by
  cases targetOwner :
      right.endpointOwner? ⟨iso.nodes node, .identity targetIndex⟩ with
  | none =>
      simp [resolvePort?, targetOwner] at rightResolved
  | some targetWire =>
      have targetExpected :
          resolveExpected? right rightContext targetWire sig =
            some rightVar := by
        simpa [resolvePort?, targetOwner] using rightResolved
      obtain ⟨sourceIndex, sourceOwner⟩ :=
        iso.identity_owner_backward leftWellFormed nodeData targetOwner
      let sourceWire := iso.wires.symm targetWire
      have targetMember :=
        resolveExpected?_sound_member right rightContext targetWire sig
          targetExpected
      have sourceMember : sourceWire ∈ leftContext.ids :=
        contexts.backward targetWire targetMember
      have targetSignature :=
        resolveExpected?_sound_signature right rightContext targetWire sig
          targetExpected
      have sourceSignature : (left.wires sourceWire).sig = sig := by
        have signatureTransport := iso.wire_signature sourceWire
        have mappedWire : iso.wires sourceWire = targetWire :=
          iso.wires.right_inv targetWire
        rw [mappedWire] at signatureTransport
        exact signatureTransport.symm.trans targetSignature
      obtain ⟨leftVar, pairedRightVar, leftExpected, pairedRightExpected⟩ :=
        resolveExpected?_pair iso contexts sourceWire sig
          sourceMember sourceSignature
      have mappedWire : iso.wires sourceWire = targetWire := by
        exact iso.wires.right_inv targetWire
      have pairedEquality : pairedRightVar = rightVar := by
        apply Option.some.inj
        rw [mappedWire] at pairedRightExpected
        exact pairedRightExpected.symm.trans targetExpected
      subst pairedRightVar
      refine ⟨sourceIndex, leftVar, ?_, ?_⟩
      · change left.endpointOwner? ⟨node, .identity sourceIndex⟩ =
          some sourceWire at sourceOwner
        simp [resolvePort?, sourceOwner, leftExpected]
      · exact envs sourceWire sig leftVar rightVar
          leftExpected (by simpa [mappedWire] using targetExpected)

private theorem resolveAtomPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    (port : CPort) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolvePort? left leftContext node port expected = some leftVar) :
    ∃ rightVar,
      resolvePort? right rightContext (iso.nodes node) port expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, port⟩ with
  | none => simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire expected = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      have targetOwner := iso.atom_owner_forward leftWellFormed
        rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire expected
          leftVar expectedEquation
      refine ⟨rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

private theorem resolveRefPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
    (port : CPort) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolvePort? left leftContext node port expected = some leftVar) :
    ∃ rightVar,
      resolvePort? right rightContext (iso.nodes node) port expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, port⟩ with
  | none => simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire expected = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      have targetOwner := iso.ref_owner_forward leftWellFormed
        rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire expected
          leftVar expectedEquation
      refine ⟨rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

private theorem resolveAtomArgs?_forward_denote
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {nodeArgs : List Sig}
    (nodeData : left.nodes node = .atom region nodeArgs) :
    (args : List Sig) → (index : Nat) →
      (leftVars : Vars leftContext.sigs args) →
      resolveArgs? left leftContext node args index = some leftVars →
      ∃ rightVars,
        resolveArgs? right rightContext (iso.nodes node) args index =
          some rightVars ∧
        Vars.denote leftEnv leftVars = Vars.denote rightEnv rightVars
  | [], _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | sig :: rest, index, .cons leftHead leftTail, equation => by
      cases headEquation :
          resolvePort? left leftContext node (.arg index) sig with
      | none => simp [resolveArgs?, headEquation] at equation
      | some resolvedHead =>
          cases tailEquation :
              resolveArgs? left leftContext node rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation] at equation
          | some resolvedTail =>
              have pairEquality :
                  Vars.cons resolvedHead resolvedTail =
                    Vars.cons leftHead leftTail := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    equation)
              cases pairEquality
              obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
                resolveAtomPort?_forward_value iso leftWellFormed
                  rightWellFormed contexts envs nodeData (.arg index) sig
                  leftHead headEquation
              obtain ⟨rightTail, rightTailEquation, tailDenotes⟩ :=
                resolveAtomArgs?_forward_denote iso leftWellFormed
                  rightWellFormed contexts envs nodeData rest (index + 1)
                  leftTail tailEquation
              refine ⟨.cons rightHead rightTail, ?_, ?_⟩
              · simp [resolveArgs?, rightHeadEquation, rightTailEquation]
              · simp only [Vars.denote_cons, headDenotes, tailDenotes]

private theorem resolveRefArgs?_forward_denote
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {nodeArgs : List Sig}
    (nodeData : left.nodes node = .ref region definition nodeArgs) :
    (args : List Sig) → (index : Nat) →
      (leftVars : Vars leftContext.sigs args) →
      resolveArgs? left leftContext node args index = some leftVars →
      ∃ rightVars,
        resolveArgs? right rightContext (iso.nodes node) args index =
          some rightVars ∧
        Vars.denote leftEnv leftVars = Vars.denote rightEnv rightVars
  | [], _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | sig :: rest, index, .cons leftHead leftTail, equation => by
      cases headEquation :
          resolvePort? left leftContext node (.arg index) sig with
      | none => simp [resolveArgs?, headEquation] at equation
      | some resolvedHead =>
          cases tailEquation :
              resolveArgs? left leftContext node rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation] at equation
          | some resolvedTail =>
              have pairEquality :
                  Vars.cons resolvedHead resolvedTail =
                    Vars.cons leftHead leftTail := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    equation)
              cases pairEquality
              obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
                resolveRefPort?_forward_value iso leftWellFormed
                  rightWellFormed contexts envs nodeData (.arg index) sig
                  leftHead headEquation
              obtain ⟨rightTail, rightTailEquation, tailDenotes⟩ :=
                resolveRefArgs?_forward_denote iso leftWellFormed
                  rightWellFormed contexts envs nodeData rest (index + 1)
                  leftTail tailEquation
              refine ⟨.cons rightHead rightTail, ?_, ?_⟩
              · simp [resolveArgs?, rightHeadEquation, rightTailEquation]
              · simp only [Vars.denote_cons, headDenotes, tailDenotes]

private theorem compileAtomNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  cases headEquation :
      resolvePort? left leftContext node .head (.rel args) with
  | none =>
      simp [compileNode?, nodeData, headEquation] at leftCompiled
  | some leftHead =>
      cases argsEquation :
          resolveArgs? left leftContext node args 0 with
      | none =>
          simp [compileNode?, nodeData, headEquation, argsEquation] at leftCompiled
      | some leftArgs =>
          have itemEquality :
              (Item.atom leftHead leftArgs :
                Item definitions leftContext.sigs) = leftItem := by
            exact Option.some.inj (by
              simpa [compileNode?, nodeData, headEquation, argsEquation] using
                leftCompiled)
          subst leftItem
          obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
            resolveAtomPort?_forward_value iso leftWellFormed rightWellFormed
              contexts envs nodeData .head (.rel args) leftHead headEquation
          obtain ⟨rightArgs, rightArgsEquation, argsDenote⟩ :=
            resolveAtomArgs?_forward_denote iso leftWellFormed rightWellFormed
              contexts envs nodeData args 0 leftArgs argsEquation
          refine ⟨.atom rightHead rightArgs, ?_, ?_⟩
          · simp [compileNode?, iso.node_table, nodeData, CNode.rename,
              rightHeadEquation, rightArgsEquation]
          · simp only [denoteItem_atom, headDenotes, argsDenote]

private theorem compileRefNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  simp only [compileNode?, nodeData] at leftCompiled
  split at leftCompiled
  · rename_i signature
    cases argsEquation :
        resolveArgs? left leftContext node args 0 with
    | none =>
        simp [argsEquation] at leftCompiled
    | some leftArgs =>
        let reference : DefVar definitions args :=
          signature ▸ definitionVarAt definitions definition
        have itemEquality :
              (Item.named reference leftArgs :
              Item definitions leftContext.sigs) = leftItem := by
          exact Option.some.inj (by
            simpa [argsEquation, reference] using leftCompiled)
        subst leftItem
        obtain ⟨rightArgs, rightArgsEquation, argsDenote⟩ :=
          resolveRefArgs?_forward_denote iso leftWellFormed rightWellFormed
            contexts envs nodeData args 0 leftArgs argsEquation
        refine ⟨.named reference rightArgs, ?_, ?_⟩
        · simp only [compileNode?, iso.node_table, nodeData, CNode.rename]
          split
          · simp [rightArgsEquation, reference]
          · contradiction
        · simp only [denoteItem_named, argsDenote]
  · simp at leftCompiled

private theorem endpointOwner?_incident
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    endpoint ∈ (diagram.wires wire).endpoints := by
  unfold ConcreteDiagram.endpointOwner? at owner
  cases found :
      diagram.endpointOccurrences.find? (fun occurrence =>
        occurrence.2 == endpoint) with
  | none => simp [found] at owner
  | some occurrence =>
      have occurrenceMember :=
        List.mem_of_find?_eq_some found
      have endpointEquality :
          occurrence.2 = endpoint :=
        eq_of_beq (List.find?_some
          (p := fun occurrence :
            diagram.WireId × CEndpoint diagram.nodeCount =>
              occurrence.2 == endpoint) found)
      have wireEquality : occurrence.1 = wire := by
        simpa [found] using owner
      subst endpoint
      subst wire
      simp only [ConcreteDiagram.endpointOccurrences,
        List.mem_flatMap] at occurrenceMember
      rcases occurrenceMember with ⟨candidate, _, member⟩
      simp only [List.mem_map] at member
      rcases member with ⟨candidateEndpoint, candidateMember, equality⟩
      cases equality
      exact candidateMember

private theorem endpointOwner?_occurs
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    (wire, endpoint) ∈ diagram.endpointOccurrences := by
  unfold ConcreteDiagram.endpointOwner? at owner
  cases found :
      diagram.endpointOccurrences.find? (fun occurrence =>
        occurrence.2 == endpoint) with
  | none => simp [found] at owner
  | some occurrence =>
      have occurrenceMember :=
        List.mem_of_find?_eq_some found
      have endpointEquality : occurrence.2 = endpoint :=
        eq_of_beq (List.find?_some
          (p := fun occurrence :
            diagram.WireId × CEndpoint diagram.nodeCount =>
              occurrence.2 == endpoint) found)
      have wireEquality : occurrence.1 = wire := by
        simpa [found] using owner
      have pairEquality : occurrence = (wire, endpoint) :=
        Prod.ext wireEquality endpointEquality
      simpa [pairEquality] using occurrenceMember

private theorem endpointOwner?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node) :
    ∃ wire, diagram.endpointOwner? ⟨node, port⟩ = some wire := by
  have nodeCheck := (List.all_eq_true.mp
    wellFormed.ports_covered_exactly_once) node
    (Data.Finite.mem_allFin node)
  have portCheck := (List.all_eq_true.mp nodeCheck) port required
  rw [Bool.and_eq_true] at portCheck
  exact Option.isSome_iff_exists.mp portCheck.2

private theorem endpoint_scope
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    diagram.Encloses (diagram.wires wire).scope
      (diagram.nodes endpoint.node).region := by
  have occurrence := endpointOwner?_occurs diagram endpoint wire owner
  have checked := (List.all_eq_true.mp
    wellFormed.wire_scopes_enclose) (wire, endpoint) occurrence
  exact of_decide_eq_true checked

theorem encloses_iff_exists
    (diagram : ConcreteDiagram definitionCount)
    (ancestor descendant : diagram.RegionId) :
    diagram.Encloses ancestor descendant ↔
      ∃ steps : Fin (diagram.regionCount + 1),
        diagram.climb steps descendant = some ancestor := by
  simp [ConcreteDiagram.Encloses]

private theorem root_has_no_strict_ancestor
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (ancestor : diagram.RegionId)
    (encloses : diagram.Encloses ancestor diagram.root) :
    ancestor = diagram.root := by
  rcases (encloses_iff_exists diagram ancestor diagram.root).mp encloses with
    ⟨⟨steps, bound⟩, climbed⟩
  cases steps with
  | zero => simpa using climbed.symm
  | succ steps =>
      have rootData : diagram.regions diagram.root = .sheet :=
        wellFormed.root_is_sheet
      rw [ConcreteDiagram.climb, rootData] at climbed
      simp at climbed

private theorem encloses_child_split
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  rcases (encloses_iff_exists diagram ancestor child).mp encloses with
    ⟨⟨steps, bound⟩, climbed⟩
  cases steps with
  | zero => exact .inl (by simpa using climbed.symm)
  | succ steps =>
      right
      apply (encloses_iff_exists diagram ancestor parent).mpr
      exact ⟨⟨steps, by omega⟩, by
        simpa [ConcreteDiagram.climb, childData] using climbed⟩

namespace WireContext

def Covers (context : WireContext diagram)
    (region : diagram.RegionId) : Prop :=
  ∀ wire, diagram.Encloses (diagram.wires wire).scope region →
    wire ∈ context.ids

private theorem member_wiresAt (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) (wire : diagram.WireId)
    (scope : (diagram.wires wire).scope = region) :
    wire ∈ diagram.wiresAt region := by
  have member : wire ∈ diagram.wiresList := by
    exact Data.Finite.mem_allFin wire
  simp [ConcreteDiagram.wiresAt, scope, member]

theorem extend_covers_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    ((WireContext.empty diagram).extend diagram.root).Covers diagram.root := by
  intro wire encloses
  have scope := root_has_no_strict_ancestor definitions diagram wellFormed
    (diagram.wires wire).scope encloses
  simp [WireContext.extend,
    member_wiresAt diagram diagram.root wire scope]

theorem extend_covers_child
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram)
    (parent child : diagram.RegionId)
    (parentCoverage : context.Covers parent)
    (childData : diagram.regions child = .cut parent) :
    (context.extend child).Covers child := by
  intro wire encloses
  rcases encloses_child_split diagram (diagram.wires wire).scope child parent
    childData encloses with localScope | inherited
  · simp [WireContext.extend,
      member_wiresAt diagram child wire localScope]
  · simp [WireContext.extend, parentCoverage wire inherited]

end WireContext

private theorem resolvePort?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region)
    (node : diagram.NodeId) (nodeRegion : (diagram.nodes node).region = region)
    (port : CPort) (expected : Sig)
    (required : port ∈ diagram.requiredPorts node)
    (typed : ∀ wire, diagram.endpointOwner? ⟨node, port⟩ = some wire →
      (diagram.wires wire).sig = expected) :
    ∃ resolved,
      resolvePort? diagram context node port expected = some resolved := by
  obtain ⟨wire, owner⟩ :=
    endpointOwner?_complete definitions diagram wellFormed node port required
  have inScope := endpoint_scope definitions diagram wellFormed
    ⟨node, port⟩ wire owner
  rw [nodeRegion] at inScope
  have member := coverage wire inScope
  obtain ⟨wireVar, wireResolved⟩ :=
    resolveWire?_complete diagram context wire member
  have signature := typed wire owner
  exact ⟨signature ▸ wireVar, by
    simp [resolvePort?, owner, resolveExpected?, signature, wireResolved]⟩

private theorem atom_head_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (args : List Sig)
    (nodeData : diagram.nodes node = .atom region args)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .head⟩ = some wire) :
    (diagram.wires wire).sig = .rel args := by
  have checked := wellFormed.atom_ports_typed
  unfold ConcreteDiagram.AtomPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData, Bool.and_eq_true] at nodeChecked
  rw [owner] at nodeChecked
  exact eq_of_beq nodeChecked.1

private theorem atom_arg_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (args : List Sig)
    (nodeData : diagram.nodes node = .atom region args)
    (index : Nat) (bound : index < args.length)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .arg index⟩ = some wire) :
    (diagram.wires wire).sig = args[index] := by
  have checked := wellFormed.atom_ports_typed
  unfold ConcreteDiagram.AtomPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData, Bool.and_eq_true] at nodeChecked
  have indexChecked := (List.all_eq_true.mp nodeChecked.2) index
    (by simpa using bound)
  rw [owner] at indexChecked
  have lookup : args[index]? = some args[index] :=
    List.getElem?_eq_getElem bound
  rw [lookup] at indexChecked
  exact eq_of_beq indexChecked

private theorem ref_arg_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId)
    (definition : Fin definitions.length) (args : List Sig)
    (nodeData : diagram.nodes node = .ref region definition args)
    (index : Nat) (bound : index < args.length)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .arg index⟩ = some wire) :
    (diagram.wires wire).sig = args[index] := by
  have checked := wellFormed.ref_ports_typed
  unfold ConcreteDiagram.RefPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  have indexChecked := (List.all_eq_true.mp nodeChecked) index
    (by simpa using bound)
  rw [owner] at indexChecked
  have lookup : args[index]? = some args[index] :=
    List.getElem?_eq_getElem bound
  rw [lookup] at indexChecked
  exact eq_of_beq indexChecked

private theorem identity_port_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (index : Nat) (bound : index < arity)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .identity index⟩ = some wire) :
    (diagram.wires wire).sig = sig := by
  have checked := wellFormed.identity_ports_typed
  unfold ConcreteDiagram.IdentityPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  have indexChecked := (List.all_eq_true.mp nodeChecked) index
    (by simpa using bound)
  rw [owner] at indexChecked
  exact eq_of_beq indexChecked

private theorem resolveArgs?_complete
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId)
    (args : List Sig) (index : Nat)
    (complete : ∀ offset (bound : offset < args.length),
      ∃ resolved,
        resolvePort? diagram context node (.arg (index + offset))
          args[offset] = some resolved) :
    ∃ resolved, resolveArgs? diagram context node args index = some resolved := by
  induction args generalizing index with
  | nil => exact ⟨.nil, rfl⟩
  | cons sig rest ih =>
      obtain ⟨head, headResolved⟩ := complete 0 (by simp)
      obtain ⟨tail, tailResolved⟩ := ih (index := index + 1) (by
        intro offset bound
        obtain ⟨resolved, resolvedEq⟩ :=
          complete (offset + 1) (by simp; omega)
        exact ⟨resolved, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            resolvedEq⟩)
      have headResolved' :
          resolvePort? diagram context node (.arg index) sig = some head := by
        simpa using headResolved
      exact ⟨.cons head tail, by
        simp [resolveArgs?, headResolved', tailResolved]⟩

private theorem resolveIdentityPorts?_complete
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig)
    (remaining index : Nat)
    (complete : ∀ offset (_bound : offset < remaining),
      ∃ resolved,
        resolvePort? diagram context node (.identity (index + offset)) sig =
          some resolved) :
    ∃ resolved,
      resolveIdentityPorts? diagram context node sig remaining index =
        some resolved := by
  induction remaining generalizing index with
  | zero => exact ⟨⟨[], rfl⟩, rfl⟩
  | succ remaining ih =>
      obtain ⟨head, headResolved⟩ := complete 0 (by omega)
      obtain ⟨tail, tailResolved⟩ := ih (index := index + 1) (by
        intro offset bound
        obtain ⟨resolved, resolvedEq⟩ :=
          complete (offset + 1) (by omega)
        exact ⟨resolved, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            resolvedEq⟩)
      have headResolved' :
          resolvePort? diagram context node (.identity index) sig =
            some head := by
        simpa using headResolved
      exact ⟨⟨head :: tail.val, by simp [tail.property]⟩, by
        simp [resolveIdentityPorts?, headResolved', tailResolved]⟩

private theorem compileIdentityNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  simp only [compileNode?, nodeData] at leftCompiled
  split at leftCompiled
  · rename_i arityWitness
    cases portsEquation :
        resolveIdentityPorts? left leftContext node sig arity 0 with
    | none =>
        simp [portsEquation] at leftCompiled
    | some leftPorts =>
        have itemEquality :
            (Item.identity sig leftPorts.val (by
              simpa [leftPorts.property] using arityWitness) :
              Item definitions leftContext.sigs) = leftItem := by
          exact Option.some.inj (by
            simpa [portsEquation] using leftCompiled)
        subst leftItem
        have rightNodeData :
            right.nodes (iso.nodes node) =
              .identity (iso.regions region) sig arity := by
          rw [iso.node_table, nodeData]
          rfl
        obtain ⟨rightPorts, rightPortsEquation⟩ :=
          resolveIdentityPorts?_complete right rightContext (iso.nodes node)
            sig arity 0 (by
              intro targetIndex targetBound
              obtain ⟨targetWire, targetOwner⟩ :=
                ConcreteDiagram.endpointOwner?_complete definitions right
                  rightWellFormed (iso.nodes node)
                  (.identity targetIndex)
                  (by
                    simp [ConcreteDiagram.requiredPorts, rightNodeData,
                      targetBound])
              obtain ⟨sourceIndex, sourceOwner⟩ :=
                iso.identity_owner_backward leftWellFormed nodeData targetOwner
              have sourceIncident :=
                ConcreteDiagram.endpointOwner?_incident left
                  ⟨node, .identity sourceIndex⟩
                  (iso.wires.symm targetWire) sourceOwner
              have sourceRequired :=
                ConcreteDiagram.incident_port_required definitions left
                  leftWellFormed (iso.wires.symm targetWire)
                  ⟨node, .identity sourceIndex⟩ sourceIncident
              have sourceBound : sourceIndex < arity := by
                simpa [ConcreteDiagram.requiredPorts, nodeData] using
                  sourceRequired
              obtain ⟨leftVar, leftResolved, _⟩ :=
                resolveIdentityPorts?_at left leftContext node sig arity 0
                  leftPorts portsEquation sourceIndex sourceBound
              have leftExpected :
                  resolveExpected? left leftContext
                      (iso.wires.symm targetWire) sig =
                    some leftVar := by
                simpa [resolvePort?, sourceOwner] using leftResolved
              obtain ⟨rightVar, rightExpected, _⟩ :=
                resolveExpected?_forward_value iso contexts envs
                  (iso.wires.symm targetWire) sig leftVar leftExpected
              have mappedWire :
                  iso.wires (iso.wires.symm targetWire) = targetWire :=
                iso.wires.right_inv targetWire
              refine ⟨rightVar, ?_⟩
              rw [mappedWire] at rightExpected
              simpa [resolvePort?, targetOwner] using rightExpected)
        let rightItem : Item definitions rightContext.sigs :=
          .identity sig rightPorts.val (by
            simpa [rightPorts.property] using arityWitness)
        refine ⟨rightItem, ?_, ?_⟩
        · simp [rightItem, compileNode?, rightNodeData, arityWitness,
            rightPortsEquation]
        · simp only [rightItem, denoteItem_identity]
          apply AllEqual.iff_of_mem_iff
          intro value
          constructor
          · intro member
            rcases List.mem_map.mp member with
              ⟨leftVar, leftMember, leftValue⟩
            obtain ⟨sourceIndex, sourceBound, leftResolved⟩ :=
              resolveIdentityPorts?_mem left leftContext node sig arity 0
                leftPorts portsEquation leftVar leftMember
            obtain ⟨targetIndex, rightVar, rightResolved, valuesEqual⟩ :=
              resolveIdentityPort?_forward_value iso rightWellFormed
                contexts envs nodeData sourceIndex leftVar
                  (by simpa using leftResolved)
            have targetBound :=
              identity_resolved_index_bound definitions right rightWellFormed
                rightContext (iso.nodes node) (iso.regions region) sig arity
                targetIndex rightNodeData rightVar rightResolved
            have rightMember :=
              resolveIdentityPorts?_member_of_resolved right rightContext
                (iso.nodes node) sig arity 0 rightPorts rightPortsEquation
                targetIndex targetBound rightVar (by simpa using rightResolved)
            exact List.mem_map.mpr
              ⟨rightVar, rightMember, valuesEqual.symm.trans leftValue⟩
          · intro member
            rcases List.mem_map.mp member with
              ⟨rightVar, rightMember, rightValue⟩
            obtain ⟨targetIndex, targetBound, rightResolved⟩ :=
              resolveIdentityPorts?_mem right rightContext (iso.nodes node)
                sig arity 0 rightPorts rightPortsEquation rightVar rightMember
            obtain ⟨sourceIndex, leftVar, leftResolved, valuesEqual⟩ :=
              resolveIdentityPort?_backward_value iso leftWellFormed
                contexts envs nodeData targetIndex rightVar
                  (by simpa using rightResolved)
            have sourceBound :=
              identity_resolved_index_bound definitions left leftWellFormed
                leftContext node region sig arity sourceIndex nodeData
                leftVar leftResolved
            have leftMember :=
              resolveIdentityPorts?_member_of_resolved left leftContext node
                sig arity 0 leftPorts portsEquation sourceIndex sourceBound
                leftVar (by simpa using leftResolved)
            exact List.mem_map.mpr
              ⟨leftVar, leftMember, valuesEqual.trans rightValue⟩
  · simp at leftCompiled

private theorem compileNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    (node : left.NodeId)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  cases nodeData : left.nodes node with
  | atom region args =>
      exact compileAtomNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled
  | ref region definition args =>
      exact compileRefNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled
  | identity region sig arity =>
      exact compileIdentityNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled

private theorem reference_signature
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId)
    (definition : Fin definitions.length) (args : List Sig)
    (nodeData : diagram.nodes node = .ref region definition args) :
    definitions.get definition = args := by
  have checked := wellFormed.references_match
  unfold ConcreteDiagram.ReferencesMatch at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  exact (eq_of_beq nodeChecked).symm

private theorem identity_arity
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity) :
    2 ≤ arity := by
  have checked := wellFormed.identities_have_arity
  unfold ConcreteDiagram.IdentitiesHaveArity at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  exact of_decide_eq_true nodeChecked

private theorem compileNode?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region)
    (node : diagram.NodeId)
    (nodeRegion : (diagram.nodes node).region = region) :
    ∃ item, compileNode? definitions diagram context node = some item := by
  cases nodeData : diagram.nodes node with
  | atom storedRegion args =>
      obtain ⟨head, headResolved⟩ := resolvePort?_complete
        definitions diagram wellFormed context region coverage node nodeRegion
        .head (.rel args)
        (by simp [ConcreteDiagram.requiredPorts, nodeData])
        (atom_head_typed definitions diagram wellFormed node storedRegion args
          nodeData)
      obtain ⟨arguments, argumentsResolved⟩ :=
        resolveArgs?_complete diagram context node args 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using atom_arg_typed definitions diagram wellFormed node
              storedRegion args nodeData offset bound)
      exact ⟨.atom head arguments, by
        unfold compileNode?
        rw [nodeData]
        simp [headResolved, argumentsResolved]⟩
  | ref storedRegion definition args =>
      have signature := reference_signature definitions diagram wellFormed
        node storedRegion definition args nodeData
      have signatureGetElem : definitions[definition.val] = args := by
        change definitions.get definition = args
        exact signature
      obtain ⟨arguments, argumentsResolved⟩ :=
        resolveArgs?_complete diagram context node args 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using ref_arg_typed definitions diagram wellFormed node
              storedRegion definition args nodeData offset bound)
      exact ⟨.named (signature ▸ definitionVarAt definitions definition)
        arguments, by
          unfold compileNode?
          rw [nodeData]
          simp [signatureGetElem, argumentsResolved]⟩
  | identity storedRegion sig arity =>
      have arityWitness := identity_arity definitions diagram wellFormed
        node storedRegion sig arity nodeData
      obtain ⟨ports, portsResolved⟩ :=
        resolveIdentityPorts?_complete diagram context node sig arity 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using identity_port_typed definitions diagram wellFormed node
              storedRegion sig arity nodeData offset bound)
      exact ⟨.identity sig ports.val (by
        simpa [ports.property] using arityWitness), by
          unfold compileNode?
          rw [nodeData]
          simp [arityWitness, portsResolved]⟩

theorem compileNodes?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region) :
    (nodes : List diagram.NodeId) →
    (∀ node, node ∈ nodes → (diagram.nodes node).region = region) →
    ∃ items, compileNodes? definitions diagram context nodes = some items
  | [], _ => ⟨.nil, rfl⟩
  | node :: tail, owns => by
      obtain ⟨head, headCompiled⟩ := compileNode?_complete definitions diagram
        wellFormed context region coverage node (owns node (by simp))
      obtain ⟨rest, restCompiled⟩ := compileNodes?_complete definitions diagram
        wellFormed context region coverage tail (by
          intro candidate member
          exact owns candidate (by simp [member]))
      exact ⟨.cons head rest, by
        simp [compileNodes?, headCompiled, restCompiled]⟩

private theorem compileNodes?_item_for_node
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) :
    ∀ {nodes : List diagram.NodeId}
      {items : ItemSeq definitions context.sigs},
      compileNodes? definitions diagram context nodes = some items →
      ∀ node, node ∈ nodes →
        ∃ item,
          item ∈ items.toList ∧
          compileNode? definitions diagram context node = some item
  | [], _, compiled, node, member => by simp at member
  | head :: tail, items, compiled, node, member => by
      cases headEquation :
          compileNode? definitions diagram context head with
      | none => simp [compileNodes?, headEquation] at compiled
      | some headItem =>
          cases tailEquation :
              compileNodes? definitions diagram context tail with
          | none =>
              simp [compileNodes?, headEquation, tailEquation] at compiled
          | some tailItems =>
              have itemsEquality :
                  (ItemSeq.cons headItem tailItems :
                    ItemSeq definitions context.sigs) = items := by
                exact Option.some.inj (by
                  simpa [compileNodes?, headEquation, tailEquation] using
                    compiled)
              subst items
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact ⟨headItem, by simp [ItemSeq.toList], headEquation⟩
              · obtain ⟨item, itemMember, itemCompiled⟩ :=
                  compileNodes?_item_for_node definitions diagram context
                    tailEquation node tailMember
                exact ⟨item, by
                  simp [ItemSeq.toList, itemMember], itemCompiled⟩

private theorem compileNodes?_node_for_item
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) :
    ∀ {nodes : List diagram.NodeId}
      {items : ItemSeq definitions context.sigs},
      compileNodes? definitions diagram context nodes = some items →
      ∀ item, item ∈ items.toList →
        ∃ node,
          node ∈ nodes ∧
          compileNode? definitions diagram context node = some item
  | [], items, compiled, item, member => by
      have itemsEquality : (.nil : ItemSeq definitions context.sigs) = items :=
        Option.some.inj (by simpa [compileNodes?] using compiled)
      subst items
      simp [ItemSeq.toList] at member
  | head :: tail, items, compiled, item, member => by
      cases headEquation :
          compileNode? definitions diagram context head with
      | none => simp [compileNodes?, headEquation] at compiled
      | some headItem =>
          cases tailEquation :
              compileNodes? definitions diagram context tail with
          | none =>
              simp [compileNodes?, headEquation, tailEquation] at compiled
          | some tailItems =>
              have itemsEquality :
                  (ItemSeq.cons headItem tailItems :
                    ItemSeq definitions context.sigs) = items := by
                exact Option.some.inj (by
                  simpa [compileNodes?, headEquation, tailEquation] using
                    compiled)
              subst items
              simp only [ItemSeq.toList, List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact ⟨head, by simp, headEquation⟩
              · obtain ⟨node, nodeMember, itemCompiled⟩ :=
                  compileNodes?_node_for_item definitions diagram context
                    tailEquation item tailMember
                exact ⟨node, by simp [nodeMember], itemCompiled⟩

theorem compileNodes?_iso_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {leftNodes : List left.NodeId} {rightNodes : List right.NodeId}
    (forwardNodes :
      ∀ node, node ∈ leftNodes → iso.nodes node ∈ rightNodes)
    (backwardNodes :
      ∀ node, node ∈ rightNodes → iso.nodes.symm node ∈ leftNodes)
    {leftItems : ItemSeq definitions leftContext.sigs}
    {rightItems : ItemSeq definitions rightContext.sigs}
    (leftCompiled :
      compileNodes? definitions left leftContext leftNodes = some leftItems)
    (rightCompiled :
      compileNodes? definitions right rightContext rightNodes =
        some rightItems) :
    denoteItemSeq pre definitionEnv leftEnv leftItems ↔
      denoteItemSeq pre definitionEnv rightEnv rightItems := by
  rw [ItemSeq.denote_iff_mem, ItemSeq.denote_iff_mem]
  constructor
  · intro leftDenotes rightItem rightMember
    obtain ⟨rightNode, rightNodeMember, rightItemCompiled⟩ :=
      compileNodes?_node_for_item definitions right rightContext
        rightCompiled rightItem rightMember
    let leftNode := iso.nodes.symm rightNode
    have leftNodeMember : leftNode ∈ leftNodes :=
      backwardNodes rightNode rightNodeMember
    obtain ⟨leftItem, leftItemMember, leftItemCompiled⟩ :=
      compileNodes?_item_for_node definitions left leftContext leftCompiled
        leftNode leftNodeMember
    obtain ⟨mappedItem, mappedCompiled, itemDenotation⟩ :=
      compileNode?_forward_denotation iso leftWellFormed rightWellFormed
        contexts definitionEnv envs leftNode leftItem leftItemCompiled
    have mappedNode : iso.nodes leftNode = rightNode :=
      iso.nodes.right_inv rightNode
    have mappedItemEquality : mappedItem = rightItem := by
      apply Option.some.inj
      rw [mappedNode] at mappedCompiled
      exact mappedCompiled.symm.trans rightItemCompiled
    subst mappedItem
    exact itemDenotation.mp (leftDenotes leftItem leftItemMember)
  · intro rightDenotes leftItem leftMember
    obtain ⟨leftNode, leftNodeMember, leftItemCompiled⟩ :=
      compileNodes?_node_for_item definitions left leftContext leftCompiled
        leftItem leftMember
    obtain ⟨rightItem, rightItemCompiled, itemDenotation⟩ :=
      compileNode?_forward_denotation iso leftWellFormed rightWellFormed
        contexts definitionEnv envs leftNode leftItem leftItemCompiled
    have rightNodeMember : iso.nodes leftNode ∈ rightNodes :=
      forwardNodes leftNode leftNodeMember
    obtain ⟨storedItem, storedMember, storedCompiled⟩ :=
      compileNodes?_item_for_node definitions right rightContext rightCompiled
        (iso.nodes leftNode) rightNodeMember
    have storedEquality : storedItem = rightItem := by
      exact Option.some.inj (storedCompiled.symm.trans rightItemCompiled)
    subst storedItem
    exact itemDenotation.mpr (rightDenotes rightItem storedMember)


end ConcreteElaboration

end VisualProof
