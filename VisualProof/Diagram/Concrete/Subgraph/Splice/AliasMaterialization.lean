import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Quotient

namespace VisualProof.Diagram.Splice

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AliasMaterialization

/-- A boundary position repeats an earlier occurrence of the same concrete
wire identity. The strict order makes the first incidence canonical. -/
def IsRepeat (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) : Prop :=
  ∃ prior : Fin pattern.boundary.length,
    prior.val < position.val ∧
      pattern.boundary.get prior = pattern.boundary.get position

instance (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) :
    Decidable (IsRepeat pattern position) := by
  unfold IsRepeat
  infer_instance

/-- Repeated positions in their authoritative ordered-boundary order. -/
def repeatPositions (pattern : OpenConcreteDiagram) :
    List (Fin pattern.boundary.length) :=
  (allFin pattern.boundary.length).filter fun position =>
    decide (IsRepeat pattern position)

@[simp] theorem mem_repeatPositions (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) :
    position ∈ repeatPositions pattern ↔ IsRepeat pattern position := by
  simp [repeatPositions]

theorem repeatPositions_nodup (pattern : OpenConcreteDiagram) :
    (repeatPositions pattern).Nodup := by
  exact List.Sublist.nodup List.filter_sublist
    (allFin_nodup pattern.boundary.length)

def repeatCount (pattern : OpenConcreteDiagram) : Nat :=
  (repeatPositions pattern).length

def repeatPosition (pattern : OpenConcreteDiagram)
    (aliasIndex : Fin (repeatCount pattern)) : Fin pattern.boundary.length :=
  (repeatPositions pattern).get aliasIndex

def repeatIndex? (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) :
    Option (Fin (repeatCount pattern)) :=
  indexOf? (repeatPositions pattern) position

@[simp] theorem repeatIndex?_isSome_iff (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) :
    (repeatIndex? pattern position).isSome = true ↔
      IsRepeat pattern position := by
  change (indexOf? (repeatPositions pattern) position).isSome = true ↔ _
  rw [indexOf?_isSome_iff, mem_repeatPositions]

private theorem indexOf?_minimal [DecidableEq α]
    {values : List α} {value : α} {found : Fin values.length}
    (hfound : indexOf? values value = some found) :
    ∀ prior : Fin values.length, prior.val < found.val →
      values.get prior ≠ value := by
  induction values with
  | nil => simp [indexOf?] at hfound
  | cons head tail ih =>
      simp only [indexOf?] at hfound
      split at hfound
      · cases hfound
        intro prior hprior
        exact (Nat.not_lt_zero prior.val hprior).elim
      · rename_i hne
        cases htail : indexOf? tail value with
        | none => simp [htail] at hfound
        | some tailFound =>
            simp [htail] at hfound
            cases hfound
            intro prior hprior heq
            rcases prior with ⟨_ | priorValue, priorBound⟩
            · exact hne (by simpa using heq.symm)
            · have tailBound : priorValue < tail.length := by
                simpa using priorBound
              let tailPrior : Fin tail.length := ⟨priorValue, tailBound⟩
              apply ih htail tailPrior
              · simpa [tailPrior] using hprior
              · simpa [tailPrior] using heq

theorem indexOf?_not_repeat (pattern : OpenConcreteDiagram)
    (wire : Fin pattern.diagram.wireCount)
    (position : Fin pattern.boundary.length)
    (hposition : indexOf? pattern.boundary wire = some position) :
    ¬ IsRepeat pattern position := by
  rintro ⟨prior, hprior, heq⟩
  exact indexOf?_minimal hposition prior hprior
    (heq.trans (indexOf?_sound hposition))

def aliasNode (pattern : OpenConcreteDiagram)
    (aliasIndex : Fin (repeatCount pattern)) :
    Fin (pattern.diagram.nodeCount + repeatCount pattern) :=
  Fin.natAdd pattern.diagram.nodeCount aliasIndex

def aliasWire (pattern : OpenConcreteDiagram)
    (aliasIndex : Fin (repeatCount pattern)) :
    Fin (pattern.diagram.wireCount + repeatCount pattern) :=
  Fin.natAdd pattern.diagram.wireCount aliasIndex

def liftOldNode (pattern : OpenConcreteDiagram)
    (node : Fin pattern.diagram.nodeCount) :
    Fin (pattern.diagram.nodeCount + repeatCount pattern) :=
  Fin.castAdd (repeatCount pattern) node

def liftOldWire (pattern : OpenConcreteDiagram)
    (wire : Fin pattern.diagram.wireCount) :
    Fin (pattern.diagram.wireCount + repeatCount pattern) :=
  Fin.castAdd (repeatCount pattern) wire

def liftOldEndpoint (pattern : OpenConcreteDiagram)
    (endpoint : CEndpoint pattern.diagram.nodeCount) :
    CEndpoint (pattern.diagram.nodeCount + repeatCount pattern) := {
  node := liftOldNode pattern endpoint.node
  port := endpoint.port
}

/-- Alias equations use the original boundary wire as output and the fresh
position wire as their sole free input, exactly matching the TypeScript
first-incidence construction. -/
def aliasOutputs (pattern : OpenConcreteDiagram)
    (wire : Fin pattern.diagram.wireCount) :
    List (CEndpoint (pattern.diagram.nodeCount + repeatCount pattern)) :=
  (allFin (repeatCount pattern)).filterMap fun aliasIndex =>
    if pattern.boundary.get (repeatPosition pattern aliasIndex) = wire then
      some { node := aliasNode pattern aliasIndex, port := .output }
    else
      none

def materializedDiagram (pattern : OpenConcreteDiagram)
    (bodyContainer : Fin pattern.diagram.regionCount) : ConcreteDiagram where
  regionCount := pattern.diagram.regionCount
  nodeCount := pattern.diagram.nodeCount + repeatCount pattern
  wireCount := pattern.diagram.wireCount + repeatCount pattern
  root := pattern.diagram.root
  regions := pattern.diagram.regions
  nodes := Fin.addCases pattern.diagram.nodes fun _ =>
    .term bodyContainer 1 (.port 0)
  wires := Fin.addCases
    (fun wire => {
      scope := (pattern.diagram.wires wire).scope
      endpoints :=
        (pattern.diagram.wires wire).endpoints.map (liftOldEndpoint pattern) ++
          aliasOutputs pattern wire
    })
    (fun aliasIndex => {
      scope := pattern.diagram.root
      endpoints := [{ node := aliasNode pattern aliasIndex, port := .free 0 }]
    })

def materializedBoundaryWire (pattern : OpenConcreteDiagram)
    (position : Fin pattern.boundary.length) :
    Fin ((materializedDiagram pattern pattern.diagram.root).wireCount) :=
  match repeatIndex? pattern position with
  | some aliasIndex => aliasWire pattern aliasIndex
  | none => liftOldWire pattern (pattern.boundary.get position)

/-- Pure graph normalization: later incidences become distinct root stubs and
one identity node is appended at the designated terminal body for each. -/
def raw (pattern : OpenConcreteDiagram)
    (bodyContainer : Fin pattern.diagram.regionCount) : OpenConcreteDiagram where
  diagram := materializedDiagram pattern bodyContainer
  boundary := List.ofFn fun position =>
    match repeatIndex? pattern position with
    | some aliasIndex => aliasWire pattern aliasIndex
    | none => liftOldWire pattern (pattern.boundary.get position)

@[simp] theorem raw_boundary_length (pattern : OpenConcreteDiagram)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    (raw pattern bodyContainer).boundary.length = pattern.boundary.length := by
  simp [raw]

theorem liftOldWire_mem_raw_boundary (pattern : OpenConcreteDiagram)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin pattern.diagram.wireCount) (hwire : wire ∈ pattern.boundary) :
    liftOldWire pattern wire ∈ (raw pattern bodyContainer).boundary := by
  obtain ⟨position, hposition⟩ := indexOf?_complete hwire
  have hnotRepeat := indexOf?_not_repeat pattern wire position hposition
  have hnone : repeatIndex? pattern position = none := by
    cases hrepeat : repeatIndex? pattern position with
    | none => rfl
    | some aliasIndex =>
        have : (repeatIndex? pattern position).isSome = true := by
          simp [hrepeat]
        exact (hnotRepeat
          ((repeatIndex?_isSome_iff pattern position).mp this)).elim
  change liftOldWire pattern wire ∈ List.ofFn
    (fun position : Fin pattern.boundary.length =>
      match repeatIndex? pattern position with
      | some aliasIndex => aliasWire pattern aliasIndex
      | none => liftOldWire pattern (pattern.boundary.get position))
  rw [List.mem_ofFn]
  refine ⟨position, ?_⟩
  simp only [hnone]
  exact congrArg (liftOldWire pattern) (indexOf?_sound hposition)

theorem aliasWire_mem_raw_boundary (pattern : OpenConcreteDiagram)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (aliasIndex : Fin (repeatCount pattern)) :
    aliasWire pattern aliasIndex ∈ (raw pattern bodyContainer).boundary := by
  change aliasWire pattern aliasIndex ∈ List.ofFn
    (fun position : Fin pattern.boundary.length =>
      match repeatIndex? pattern position with
      | some found => aliasWire pattern found
      | none => liftOldWire pattern (pattern.boundary.get position))
  rw [List.mem_ofFn]
  refine ⟨repeatPosition pattern aliasIndex, ?_⟩
  have hindex : repeatIndex? pattern (repeatPosition pattern aliasIndex) =
      some aliasIndex := by
    exact indexOf?_get_eq_some_of_nodup (repeatPositions_nodup pattern)
      aliasIndex
  rw [hindex]

/-- Regions are unchanged, so the designated external-binder spine transports
definitionally to the alias-materialized pattern. -/
def binderSpine {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (spine : BinderSpine pattern.val.diagram) :
    BinderSpine (raw pattern.val spine.bodyContainer).diagram where
  proxyCount := spine.proxyCount
  proxy := spine.proxy
  arity := spine.arity
  bodyContainer := spine.bodyContainer
  proxy_injective := spine.proxy_injective
  proxy_ne_root := spine.proxy_ne_root
  body_eq_root_of_empty := spine.body_eq_root_of_empty
  body_eq_terminal_of_nonempty := spine.body_eq_terminal_of_nonempty
  proxy_region := spine.proxy_region

theorem terminalBody {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val) :
    (binderSpine pattern spine).TerminalBodyContract
      (raw pattern.val spine.bodyContainer) where
  root_direct_child := contract.root_direct_child
  nonterminal_direct_child := contract.nonterminal_direct_child
  root_has_no_nodes := by
    intro hnonzero node
    refine Fin.addCases (motive := fun node =>
      ((raw pattern.val spine.bodyContainer).diagram.nodes node).region ≠
        (raw pattern.val spine.bodyContainer).diagram.root) ?_ ?_ node
    · intro old
      simpa [raw, materializedDiagram] using
        contract.root_has_no_nodes hnonzero old
    · intro aliasIndex
      have hbody : spine.bodyContainer ≠ pattern.val.diagram.root := by
        rw [spine.body_eq_terminal_of_nonempty hnonzero]
        exact spine.proxy_ne_root _
      simpa [raw, materializedDiagram] using hbody
  nonterminal_has_no_nodes := by
    intro proxyIndex hnonterminal node
    change proxyIndex.val + 1 < spine.proxyCount at hnonterminal
    refine Fin.addCases (motive := fun node =>
      ((raw pattern.val spine.bodyContainer).diagram.nodes node).region ≠
        (binderSpine pattern spine).proxy proxyIndex) ?_ ?_ node
    · intro old
      simpa [raw, materializedDiagram, binderSpine] using
        contract.nonterminal_has_no_nodes proxyIndex hnonterminal old
    · intro aliasIndex
      have hbody : spine.bodyContainer ≠ spine.proxy proxyIndex := by
        intro heq
        have hnonzero : spine.proxyCount ≠ 0 := by omega
        rw [spine.body_eq_terminal_of_nonempty hnonzero] at heq
        have hindices := spine.proxy_injective heq
        have hvals := congrArg Fin.val hindices
        change spine.proxyCount - 1 = proxyIndex.val at hvals
        omega
      simpa [raw, materializedDiagram, binderSpine] using hbody
  root_has_no_nonboundary_wires := by
    intro hnonzero wire hnotBoundary
    refine Fin.addCases (motive := fun wire =>
      wire ∉ (raw pattern.val spine.bodyContainer).boundary →
        ((raw pattern.val spine.bodyContainer).diagram.wires wire).scope ≠
          (raw pattern.val spine.bodyContainer).diagram.root) ?_ ?_ wire
        hnotBoundary
    · intro old hold
      have oldNotBoundary : old ∉ pattern.val.boundary := by
        intro oldBoundary
        exact hold (liftOldWire_mem_raw_boundary pattern.val
          spine.bodyContainer old oldBoundary)
      simpa [raw, materializedDiagram] using
        contract.root_has_no_nonboundary_wires hnonzero old oldNotBoundary
    · intro aliasIndex halias
      exact (halias (aliasWire_mem_raw_boundary pattern.val
        spine.bodyContainer aliasIndex)).elim
  nonterminal_has_no_nonboundary_wires := by
    intro proxyIndex hnonterminal wire hnotBoundary
    refine Fin.addCases (motive := fun wire =>
      wire ∉ (raw pattern.val spine.bodyContainer).boundary →
        ((raw pattern.val spine.bodyContainer).diagram.wires wire).scope ≠
          (binderSpine pattern spine).proxy proxyIndex) ?_ ?_ wire hnotBoundary
    · intro old hold
      have oldNotBoundary : old ∉ pattern.val.boundary := by
        intro oldBoundary
        exact hold (liftOldWire_mem_raw_boundary pattern.val
          spine.bodyContainer old oldBoundary)
      simpa [raw, materializedDiagram, binderSpine] using
        contract.nonterminal_has_no_nonboundary_wires proxyIndex hnonterminal
          old oldNotBoundary
    · intro aliasIndex halias
      exact (halias (aliasWire_mem_raw_boundary pattern.val
        spine.bodyContainer aliasIndex)).elim
  boundary_is_root_scoped := by
    intro wire hwire
    simp only [raw] at hwire
    obtain ⟨position, hposition⟩ := List.mem_ofFn.mp hwire
    cases hrepeat : repeatIndex? pattern.val position with
    | none =>
        simp only [hrepeat] at hposition
        subst wire
        simpa [raw, materializedDiagram, liftOldWire] using
          contract.boundary_is_root_scoped
            (pattern.val.boundary.get position)
            (List.get_mem pattern.val.boundary position)
    | some aliasIndex =>
        simp only [hrepeat] at hposition
        subst wire
        simp [raw, materializedDiagram, aliasWire]

/-- Proof-bearing checked normalization. The result is locked to `raw`; the
certificate cannot replace the executor construction with another diagram. -/
structure Certificate {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (spine : BinderSpine pattern.val.diagram) : Type where
  wellFormed : (raw pattern.val spine.bodyContainer).WellFormed signature

namespace Certificate

def result {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern originalSpine) :
    CheckedOpenDiagram signature :=
  ⟨raw pattern.val originalSpine.bodyContainer, certificate.wellFormed⟩

def spine {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (_certificate : Certificate pattern originalSpine) :
    BinderSpine (raw pattern.val originalSpine.bodyContainer).diagram :=
  binderSpine pattern originalSpine

theorem terminalBody {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (_certificate : Certificate pattern originalSpine)
    (contract : originalSpine.TerminalBodyContract pattern.val) :
    (binderSpine pattern originalSpine).TerminalBodyContract
      (raw pattern.val originalSpine.bodyContainer) :=
  AliasMaterialization.terminalBody pattern originalSpine contract

theorem boundary_length {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern originalSpine) :
    certificate.result.val.boundary.length = pattern.val.boundary.length := by
  exact raw_boundary_length pattern.val originalSpine.bodyContainer

end Certificate

/-- The executor validates the concrete batch it will splice.  The checker is
the same authoritative well-formedness decision used for rule outputs; the
open-boundary and terminal-body obligations are structural consequences of
the source contract. -/
def check {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val) :
    Except WFError (Certificate pattern spine) :=
  match hcheck : checkWellFormed signature
      (materializedDiagram pattern.val spine.bodyContainer) with
  | .error error => .error error
  | .ok checked =>
      let diagramWellFormed :
          (materializedDiagram pattern.val spine.bodyContainer).WellFormed
            signature :=
        checkWellFormed_iff.mp ⟨checked, hcheck,
          checkWellFormed_preserves_input hcheck⟩
      .ok {
        wellFormed := {
          diagram_well_formed := diagramWellFormed
          boundary_is_root_scoped :=
            (terminalBody pattern spine contract).boundary_is_root_scoped
        }
      }

theorem check_success {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {spine : BinderSpine pattern.val.diagram}
    {contract : spine.TerminalBodyContract pattern.val}
    {certificate : Certificate pattern spine}
    (hcheck : check pattern spine contract = .ok certificate) :
    certificate.result.val = raw pattern.val spine.bodyContainer := by
  rfl

end AliasMaterialization

end VisualProof.Diagram.Splice
