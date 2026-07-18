import VisualProof.Rule.Step
import VisualProof.Diagram.Algebra

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Theory
open Diagram

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) =
      (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++
        (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), ih, List.map_append,
        allFin_succ_last m,
        List.map_append, List.map_map, List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

private theorem eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinjective : Function.Injective f) :
    ∀ values : List α,
      (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← eraseDups_map_injective f hinjective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [hinjective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem castAdd_injective (n m : Nat) : Function.Injective
    (Fin.castAdd m : Fin n → Fin (n + m)) := by
  intro left right heq
  apply Fin.ext
  exact congrArg (fun value : Fin (n + m) => value.val) heq

private theorem get_map_cast (values : List α) (f : α → β)
    (index : Fin values.length) :
    (values.map f).get
        (Fin.cast (List.length_map (as := values) f).symm index) =
      f (values.get index) := by
  simpa only [List.get_eq_getElem, Fin.val_cast] using
    (List.getElem_map (l := values) (i := index.val) f)

theorem get_of_eq {left right : List α}
    (heq : left = right) (index : Fin right.length) :
    left.get (Fin.cast (congrArg List.length heq).symm index) =
      right.get index := by
  subst left
  rfl

theorem survivor_index?_injective (domain : SurvivorDomain size) :
    ∀ {left right mapped}, domain.index? left = some mapped →
      domain.index? right = some mapped → left = right := by
  intro left right mapped hleft hright
  have leftOrigin := (domain.index?_eq_some_iff left mapped).mp hleft
  have rightOrigin := (domain.index?_eq_some_iff right mapped).mp hright
  exact leftOrigin.symm.trans rightOrigin

def erasurePolarity (orientation : Orientation) (depth : Nat) : Prop :=
  match orientation with
  | .forward => depth % 2 = 0
  | .backward => depth % 2 = 1

instance (orientation : Orientation) (depth : Nat) :
    Decidable (erasurePolarity orientation depth) := by
  cases orientation <;> simp [erasurePolarity] <;> infer_instance

def spawnPolarity (orientation : Orientation) (depth : Nat) : Prop :=
  match orientation with
  | .forward => depth % 2 = 1
  | .backward => depth % 2 = 0

instance (orientation : Orientation) (depth : Nat) :
    Decidable (spawnPolarity orientation depth) := by
  cases orientation <;> simp [spawnPolarity] <;> infer_instance

def spawnLiftEndpoint (endpoint : CEndpoint nodes) :
    CEndpoint (nodes + 1) :=
  { node := endpoint.node.castSucc, port := endpoint.port }

def spawnLiftWire (wire : CWire regions nodes) :
    CWire regions (nodes + 1) :=
  { scope := wire.scope, endpoints := wire.endpoints.map spawnLiftEndpoint }

/-- Append one node and one fresh singleton wire for every required port. -/
def spawnNodeRaw (input : ConcreteDiagram)
    (node : CNode input.regionCount) (scope : Fin input.regionCount)
    (portCount : Nat) (port : Fin portCount → CPort) : ConcreteDiagram where
  regionCount := input.regionCount
  nodeCount := input.nodeCount + 1
  wireCount := input.wireCount + portCount
  root := input.root
  regions := input.regions
  nodes := Fin.lastCases node input.nodes
  wires := Fin.addCases
    (fun wire => spawnLiftWire (input.wires wire))
    (fun fresh =>
      { scope := scope
        endpoints := [{ node := Fin.last input.nodeCount, port := port fresh }] })

def spawnNodeWireProvenance (input : ConcreteDiagram)
    (node : CNode input.regionCount) (scope : Fin input.regionCount)
    (portCount : Nat) (port : Fin portCount → CPort) :
    WireProvenance input (spawnNodeRaw input node scope portCount port) :=
  WireProvenance.rootFiltered input
    (spawnNodeRaw input node scope portCount port)
    (fun wire => some (Fin.castAdd portCount wire)) (by
      intro left right mapped hleft hright
      change some (Fin.castAdd portCount left) = some mapped at hleft
      change some (Fin.castAdd portCount right) = some mapped at hright
      have heq : Fin.castAdd portCount left = Fin.castAdd portCount right :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      exact congrArg (fun value : Fin (input.wireCount + portCount) =>
        value.val) heq)

def spawnNodeInterfaceTransport (input : ConcreteDiagram)
    (node : CNode input.regionCount) (scope : Fin input.regionCount)
    (portCount : Nat) (port : Fin portCount → CPort) :
    InterfaceTransport input (spawnNodeRaw input node scope portCount port) :=
  InterfaceTransport.append input
    (spawnNodeRaw input node scope portCount port) portCount rfl

/-- Append-only spawn transports every ordered root-boundary position to the
same wire in the old prefix.  Repeated boundary positions remain repeated. -/
theorem spawnNodeInterfaceTransport_transportBoundary
    (boundary : List (Fin input.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    InterfaceTransport.transportBoundary
        (spawnNodeInterfaceTransport input node scope portCount port) boundary =
      some (boundary.map fun wire =>
        Fin.cast (by rfl) (Fin.castAdd portCount wire)) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire hmem
  simp [spawnNodeInterfaceTransport, InterfaceTransport.append,
    InterfaceTransport.rootFiltered, spawnNodeRaw, spawnLiftWire,
    sourceRoot wire hmem]

/-- The exact ordered open graph produced by spawn.  Boundary positions are
mapped injectively into the old-wire prefix, preserving order and aliases. -/
def spawnNodeRawOpen (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) : OpenConcreteDiagram where
  diagram := spawnNodeRaw source.diagram node scope portCount port
  boundary := source.boundary.map (Fin.castAdd portCount)

theorem spawnNodeRawOpen_exposedWires
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    (spawnNodeRawOpen source node scope portCount port).exposedWires =
      source.exposedWires.map (Fin.castAdd portCount) := by
  unfold spawnNodeRawOpen OpenConcreteDiagram.exposedWires
  have hinjective : Function.Injective
      (Fin.castAdd portCount : Fin source.diagram.wireCount →
        Fin (source.diagram.wireCount + portCount)) := by
    intro left right heq
    apply Fin.ext
    exact congrArg
      (fun value : Fin (source.diagram.wireCount + portCount) => value.val) heq
  exact eraseDups_map_injective (Fin.castAdd portCount) hinjective _

theorem spawnNodeRawOpen_wellFormed
    (source : CheckedOpenDiagram signature)
    (node : CNode source.val.diagram.regionCount)
    (scope : Fin source.val.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (htarget : (spawnNodeRaw source.val.diagram node scope portCount port).WellFormed
      signature) :
    (spawnNodeRawOpen source.val node scope portCount port).WellFormed
      signature where
  diagram_well_formed := htarget
  boundary_is_root_scoped := by
    intro targetWire hmem
    change targetWire ∈ source.val.boundary.map (Fin.castAdd portCount) at hmem
    rcases List.mem_map.mp hmem with ⟨sourceWire, hsourceWire, heq⟩
    subst targetWire
    change ((spawnNodeRaw source.val.diagram node scope portCount port).wires
      (Fin.castAdd portCount sourceWire)).scope = source.val.diagram.root
    simpa [spawnNodeRaw, spawnLiftWire] using
      source.property.boundary_is_root_scoped sourceWire hsourceWire

@[simp] theorem spawnNodeRaw_newNode
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    (spawnNodeRaw input node scope portCount port).nodes
        (Fin.last input.nodeCount) = node := by
  simp [spawnNodeRaw]

@[simp] theorem spawnNodeRaw_oldNode
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (old : Fin input.nodeCount) :
    (spawnNodeRaw input node scope portCount port).nodes old.castSucc =
      input.nodes old := by
  simp [spawnNodeRaw]

@[simp] theorem spawnNodeRaw_oldWire_scope
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (old : Fin input.wireCount) :
    ((spawnNodeRaw input node scope portCount port).wires
      (Fin.castAdd portCount old)).scope = (input.wires old).scope := by
  simp [spawnNodeRaw, spawnLiftWire]

@[simp] theorem spawnNodeRaw_freshWire_scope
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (fresh : Fin portCount) :
    ((spawnNodeRaw input node scope portCount port).wires
      (Fin.natAdd input.wireCount fresh)).scope = scope := by
  simp [spawnNodeRaw]

/-- An endpoint of an old node occurs on an old wire after spawn exactly when
it occurred on the corresponding source wire. -/
theorem spawnNodeRaw_oldEndpointOccurs_iff
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (wire : Fin input.wireCount)
    (old : Fin input.nodeCount) (endpointPort : CPort) :
    (spawnNodeRaw input node scope portCount port).EndpointOccurs
        (Fin.castAdd portCount wire) ⟨old.castSucc, endpointPort⟩ ↔
      input.EndpointOccurs wire ⟨old, endpointPort⟩ := by
  unfold ConcreteDiagram.EndpointOccurs
  have hwire :
      (spawnNodeRaw input node scope portCount port).wires
          (Fin.castAdd portCount wire) =
        spawnLiftWire (input.wires wire) := by
    simp [spawnNodeRaw]
  rw [hwire]
  unfold spawnLiftWire
  constructor
  · intro hoccurs
    obtain ⟨endpoint, hmem, heq⟩ := List.mem_map.mp hoccurs
    have hnode : endpoint.node = old := by
      apply Fin.ext
      exact congrArg
        (fun value : CEndpoint (input.nodeCount + 1) => value.node.val) heq
    have hport : endpoint.port = endpointPort :=
      congrArg (fun value : CEndpoint (input.nodeCount + 1) => value.port) heq
    cases endpoint
    simp only at hnode hport
    subst_vars
    exact hmem
  · intro hmem
    apply List.mem_map.mpr
    exact ⟨⟨old, endpointPort⟩, hmem, rfl⟩

/-- No fresh wire contains an endpoint of an old node, so every target owner
of such an endpoint is the image of a unique source wire. -/
theorem spawnNodeRaw_oldEndpointOccurs_backward
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (targetWire : Fin (input.wireCount + portCount))
    (old : Fin input.nodeCount) (endpointPort : CPort)
    (hoccurs : (spawnNodeRaw input node scope portCount port).EndpointOccurs
      targetWire ⟨old.castSucc, endpointPort⟩) :
    ∃ sourceWire : Fin input.wireCount,
      Fin.castAdd portCount sourceWire = targetWire ∧
        input.EndpointOccurs sourceWire ⟨old, endpointPort⟩ := by
  refine Fin.addCases
      (motive := fun candidate =>
        (spawnNodeRaw input node scope portCount port).EndpointOccurs
            candidate ⟨old.castSucc, endpointPort⟩ →
          ∃ sourceWire : Fin input.wireCount,
            Fin.castAdd portCount sourceWire = candidate ∧
              input.EndpointOccurs sourceWire ⟨old, endpointPort⟩)
      (fun sourceWire h => ?_) (fun fresh h => ?_) targetWire hoccurs
  · exact ⟨sourceWire, rfl,
      (spawnNodeRaw_oldEndpointOccurs_iff input node scope portCount port
        sourceWire old endpointPort).mp h⟩
  · unfold ConcreteDiagram.EndpointOccurs at h
    have hwire :
        (spawnNodeRaw input node scope portCount port).wires
            (Fin.natAdd input.wireCount fresh) =
          { scope := scope
            endpoints := [⟨Fin.last input.nodeCount, port fresh⟩] } := by
      simp [spawnNodeRaw]
    rw [hwire] at h
    simp only [List.mem_singleton] at h
    have hval := congrArg
      (fun value : CEndpoint (input.nodeCount + 1) => value.node.val) h
    simp only [Fin.val_castSucc, Fin.val_last] at hval
    omega

/-- A lexical wire context for the source embedded in the spawned diagram.
The target may additionally contain fresh site wires, so this is deliberately
an injection with exact old-wire membership rather than an equivalence. -/
structure SpawnContextEmbedding
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port)) where
  index : Fin source.length → Fin target.length
  get : ∀ i,
    target.get (index i) = Fin.castAdd portCount (source.get i)
  mem_old : ∀ wire : Fin input.wireCount,
    Fin.castAdd portCount wire ∈ target ↔ wire ∈ source

namespace SpawnContextEmbedding

/-- The positional target context obtained by relabelling every old wire and
introducing no fresh lexical entry. -/
def mapOldContext
    (input : ConcreteDiagram) (portCount : Nat)
    (source : ConcreteElaboration.WireContext input) :
    List (Fin (input.wireCount + portCount)) :=
  source.map (Fin.castAdd portCount)

theorem mapOldContext_length
    (input : ConcreteDiagram) (portCount : Nat)
    (source : ConcreteElaboration.WireContext input) :
    (mapOldContext input portCount source).length = source.length := by
  simp [mapOldContext]

/-- The canonical position-preserving embedding into `mapOldContext`. -/
def positional
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input) :
    SpawnContextEmbedding input node scope portCount port source
      (mapOldContext input portCount source) where
  index := fun i => Fin.cast
    (mapOldContext_length input portCount source).symm i
  get := by
    intro i
    change (source.map (Fin.castAdd portCount))[i.val] =
      Fin.castAdd portCount source[i.val]
    exact List.getElem_map (f := Fin.castAdd portCount) (l := source)
  mem_old := by
    intro wire
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨old, hold, heq⟩
      have : old = wire := by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.wireCount + portCount) => value.val) heq
      simpa [this] using hold
    · intro hmem
      exact List.mem_map.mpr ⟨wire, hmem, rfl⟩

theorem positional_index_val
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (index : Fin source.length) :
    ((positional input node scope portCount port source).index index).val =
      index.val := by
  rfl

/-- Construct the canonical lexical embedding by looking each source wire up
in a target context with exact old-wire membership. -/
noncomputable def ofMem
    {input : ConcreteDiagram} {node : CNode input.regionCount}
    {scope : Fin input.regionCount} {portCount : Nat}
    {port : Fin portCount → CPort}
    {source : ConcreteElaboration.WireContext input}
    {target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port)}
    (hmem : ∀ wire : Fin input.wireCount,
      Fin.castAdd portCount wire ∈ target ↔ wire ∈ source) :
    SpawnContextEmbedding input node scope portCount port source target where
  index := fun i => Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((hmem (source.get i)).mpr (List.get_mem source i)))
  get := by
    intro i
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (ConcreteElaboration.WireContext.lookup?_complete
          ((hmem (source.get i)).mpr (List.get_mem source i))))
  mem_old := hmem

/-- In a duplicate-free target context, the wire value uniquely determines
the embedded lexical index. -/
theorem index_eq_of_get
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (targetNodup : target.Nodup) (i : Fin source.length)
    (candidate : Fin target.length)
    (hcandidate : target.get candidate =
      Fin.castAdd portCount (source.get i)) :
    candidate = embedding.index i := by
  obtain ⟨found, hfound⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete
      (List.get_mem target candidate)
  have hcandidateFound :=
    ConcreteElaboration.WireContext.lookup?_unique targetNodup hfound rfl
  have hembeddingFound :=
    ConcreteElaboration.WireContext.lookup?_unique targetNodup hfound
      ((embedding.get i).trans hcandidate.symm)
  exact hcandidateFound.trans hembeddingFound.symm

end SpawnContextEmbedding

/-- Exact-scope traversal reflects membership of every old wire.  Fresh wires
may occur at the spawn scope but can never masquerade as an old wire. -/
theorem spawnNodeRaw_exactScopeWires_mem_old_iff
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (wire : Fin input.wireCount) :
    Fin.castAdd portCount wire ∈
        ConcreteElaboration.exactScopeWires
          (spawnNodeRaw input node scope portCount port) region ↔
      wire ∈ ConcreteElaboration.exactScopeWires input region := by
  constructor
  · intro hmem
    have hscope := (ConcreteElaboration.mem_exactScopeWires
      (spawnNodeRaw input node scope portCount port) region
      (Fin.castAdd portCount wire)).mp hmem
    rw [spawnNodeRaw_oldWire_scope] at hscope
    exact (ConcreteElaboration.mem_exactScopeWires input region wire).mpr hscope
  · intro hmem
    have hscope :=
      (ConcreteElaboration.mem_exactScopeWires input region wire).mp hmem
    apply (ConcreteElaboration.mem_exactScopeWires
      (spawnNodeRaw input node scope portCount port) region
      (Fin.castAdd portCount wire)).mpr
    rw [spawnNodeRaw_oldWire_scope]
    exact hscope

namespace SpawnContextEmbedding

/-- Extending both contexts at the same concrete region preserves the exact
old-wire embedding.  At the spawn scope the target extension may additionally
contain the fresh port wires; at every other scope the local suffixes match. -/
noncomputable def extend
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (region : Fin input.regionCount) :
    SpawnContextEmbedding input node scope portCount port
      (source.extend region) (target.extend region) :=
  ofMem (by
    intro wire
    unfold ConcreteElaboration.WireContext.extend
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hinherited | hlocal
      · exact List.mem_append_left _ ((embedding.mem_old wire).mp hinherited)
      · exact List.mem_append_right _
          ((spawnNodeRaw_exactScopeWires_mem_old_iff input node scope region
            portCount port wire).mp hlocal)
    · intro hmem
      rcases List.mem_append.mp hmem with hinherited | hlocal
      · exact List.mem_append_left _ ((embedding.mem_old wire).mpr hinherited)
      · exact List.mem_append_right _
          ((spawnNodeRaw_exactScopeWires_mem_old_iff input node scope region
            portCount port wire).mpr hlocal))

end SpawnContextEmbedding

/-- Compilation of every pre-existing node commutes with append-only spawn.
The target item is renamed along the supplied lexical context embedding; no
surjectivity is assumed because fresh site wires may also be visible. -/
theorem spawnNodeRaw_compileNode?_old
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (spawnNodeRaw input node scope portCount port).WireEndpointsAreDisjoint)
    (old : Fin input.nodeCount) :
    ConcreteElaboration.compileNode? signature
        (spawnNodeRaw input node scope portCount port) target binders old.castSucc =
      (ConcreteElaboration.compileNode? signature input source binders old).map
        (Item.renameWires embedding.index) := by
  let spawned := spawnNodeRaw input node scope portCount port
  have hnode : spawned.nodes old.castSucc =
      match input.nodes old with
      | .term region freePorts term =>
          .term (id region) freePorts term
      | .atom region binder => .atom (id region) (id binder)
      | .named region definition arity =>
          .named (id region) definition arity := by
    rw [spawnNodeRaw_oldNode]
    cases input.nodes old <;> rfl
  have hports : ∀ endpointPort,
      ConcreteElaboration.resolvePort? spawned target old.castSucc endpointPort =
        (ConcreteElaboration.resolvePort? input source old endpointPort).map
          embedding.index := by
    intro endpointPort
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      source target old old.castSucc (Fin.castAdd portCount) embedding.index
      targetNodup embedding.get embedding.mem_old
    · intro wire candidatePort hoccurs
      exact (spawnNodeRaw_oldEndpointOccurs_iff input node scope portCount port
        wire old candidatePort).mpr hoccurs
    · intro targetWire candidatePort hoccurs
      exact spawnNodeRaw_oldEndpointOccurs_backward input node scope portCount
        port targetWire old candidatePort hoccurs
    · exact targetDisjoint
  have hbinders : ∀ region binder,
      input.nodes old = .atom region binder →
        binders (id binder) =
          (binders binder).map (fun relation =>
            ⟨relation.1, (fun {_} relation => relation) relation.2⟩) := by
    intro region binder _
    simp
  have hmap := ConcreteElaboration.compileNode?_map
    (signature := signature) source target binders binders old old.castSucc
    id id embedding.index (fun relation => relation) hnode hports hbinders
  simpa only [Item.renameRelations_id] using hmap

/-- Exact-scope traversal keeps the old wire prefix and appends precisely the
fresh port wires when the traversal reaches the spawn scope. -/
theorem spawnNodeRaw_exactScopeWires
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    ConcreteElaboration.exactScopeWires
        (spawnNodeRaw input node scope portCount port) region =
      (ConcreteElaboration.exactScopeWires input region).map
          (Fin.castAdd portCount) ++
        if region = scope then
          (allFin portCount).map (Fin.natAdd input.wireCount)
        else [] := by
  unfold ConcreteElaboration.exactScopeWires filterFin
  change List.filter _ (allFin (input.wireCount + portCount)) = _
  rw [allFin_add, List.filter_append]
  simp only [List.filter_map]
  congr 1
  · apply congrArg (List.map (Fin.castAdd portCount))
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.wireCount))
    funext wire
    simp only [Function.comp_apply]
    rw [spawnNodeRaw_oldWire_scope]
    rfl
  · split <;> rename_i hregion
    · subst region
      apply congrArg (List.map (Fin.natAdd input.wireCount))
      apply List.filter_eq_self.mpr
      intro wire _
      simp only [Function.comp_apply, spawnNodeRaw_freshWire_scope,
        decide_eq_true_eq]
    · change List.map (Fin.natAdd input.wireCount)
          (List.filter _ (allFin portCount)) =
          List.map (Fin.natAdd input.wireCount) []
      apply congrArg (List.map (Fin.natAdd input.wireCount))
      apply List.filter_eq_nil_iff.mpr
      intro wire _ heq
      have hdecide : decide
          (((spawnNodeRaw input node scope portCount port).wires
            (Fin.natAdd input.wireCount wire)).scope = region) = true :=
        by simpa only [Function.comp_apply] using heq
      rw [spawnNodeRaw_freshWire_scope] at hdecide
      have hscope : scope = region := of_decide_eq_true hdecide
      exact hregion hscope.symm

/-- Hidden root wires retain their order in the old-wire prefix.  Fresh
spawn wires are hidden exactly when the spawn occurs at the root. -/
theorem spawnNodeRawOpen_hiddenWires
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    (spawnNodeRawOpen source node scope portCount port).hiddenWires =
      source.hiddenWires.map (Fin.castAdd portCount) ++
        if source.diagram.root = scope then
          (allFin portCount).map (Fin.natAdd source.diagram.wireCount)
        else [] := by
  unfold OpenConcreteDiagram.hiddenWires
  change List.filter
      (fun wire => decide
        (wire ∉ (spawnNodeRawOpen source node scope portCount port).exposedWires))
      (ConcreteElaboration.exactScopeWires
        (spawnNodeRaw source.diagram node scope portCount port)
        source.diagram.root) = _
  rw [spawnNodeRaw_exactScopeWires, spawnNodeRawOpen_exposedWires]
  have hold :
      List.filter
          (fun wire => decide
            (wire ∉ source.exposedWires.map (Fin.castAdd portCount)))
          ((ConcreteElaboration.exactScopeWires source.diagram
            source.diagram.root).map (Fin.castAdd portCount)) =
        source.hiddenWires.map (Fin.castAdd portCount) := by
    unfold OpenConcreteDiagram.hiddenWires
    rw [List.filter_map]
    apply congrArg (List.map (Fin.castAdd portCount))
    apply congrArg (fun predicate =>
      List.filter predicate
        (ConcreteElaboration.exactScopeWires source.diagram
          source.diagram.root))
    funext wire
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro hnotMap hmemSource
      exact hnotMap (List.mem_map.mpr ⟨wire, hmemSource, rfl⟩)
    · intro hnotSource hmemMap
      rcases List.mem_map.mp hmemMap with ⟨old, hold, heq⟩
      have : old = wire := castAdd_injective _ _ heq
      exact hnotSource (by simpa [this] using hold)
  by_cases hscope : source.diagram.root = scope
  · simp only [if_pos hscope]
    have hsplit := List.filter_append
      (p := fun wire => decide
        (wire ∉ source.exposedWires.map (Fin.castAdd portCount)))
      ((ConcreteElaboration.exactScopeWires source.diagram
        source.diagram.root).map (Fin.castAdd portCount))
      ((allFin portCount).map (Fin.natAdd source.diagram.wireCount))
    apply Eq.trans hsplit
    rw [hold]
    congr 1
    apply List.filter_eq_self.mpr
    intro fresh hmem
    have hfresh : ∃ index : Fin portCount,
        fresh = Fin.natAdd source.diagram.wireCount index := by
      rcases List.mem_map.mp hmem with ⟨index, _, heq⟩
      exact ⟨index, heq.symm⟩
    rcases hfresh with ⟨index, rfl⟩
    apply decide_eq_true
    intro hexposed
    rcases List.mem_map.mp hexposed with ⟨old, _, heq⟩
    have hval := congrArg
      (fun value : Fin (source.diagram.wireCount + portCount) => value.val) heq
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
    omega
  · simp only [if_neg hscope, List.append_nil]
    exact hold

theorem spawnNodeRawOpen_rootWires
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    (spawnNodeRawOpen source node scope portCount port).rootWires =
      source.rootWires.map (Fin.castAdd portCount) ++
        if source.diagram.root = scope then
          (allFin portCount).map (Fin.natAdd source.diagram.wireCount)
        else [] := by
  unfold OpenConcreteDiagram.rootWires
  rw [spawnNodeRawOpen_exposedWires, spawnNodeRawOpen_hiddenWires,
    List.map_append]
  split <;> simp only [List.append_assoc, List.append_nil] <;> rfl

theorem OpenConcreteDiagram.rootWires_exact
    (source : OpenConcreteDiagram) (hwf : source.WellFormed signature) :
    ConcreteElaboration.WireContext.Exact source.rootWires
      source.diagram.root := by
  constructor
  · exact source.rootWires_nodup
  · intro wire
    rw [OpenConcreteDiagram.mem_rootWires_iff source hwf]
    constructor
    · intro hscope
      rw [hscope]
      exact ConcreteDiagram.Encloses.refl _ _
    · exact ConcreteElaboration.encloses_sheet_eq
        hwf.diagram_well_formed.root_is_sheet

/-- The position of an old root wire in the spawned root context. -/
def spawnNodeRawOpenRootIndex
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (index : Fin source.rootWires.length) :
    Fin (spawnNodeRawOpen source node scope portCount port).rootWires.length :=
  Fin.cast (by
    have hlist := spawnNodeRawOpen_rootWires source node scope portCount port
    rw [if_pos hroot] at hlist
    calc
      source.rootWires.length + portCount =
          (source.rootWires.map (Fin.castAdd portCount) ++
            (allFin portCount).map
              (Fin.natAdd source.diagram.wireCount)).length := by
        simp only [List.length_append, List.length_map, Nat.add_left_cancel_iff]
        rw [allFin_eq_finRange, List.length_finRange]
      _ = (spawnNodeRawOpen source node scope portCount port).rootWires.length :=
        (congrArg List.length hlist).symm)
      (Fin.castAdd portCount index)

theorem spawnNodeRawOpen_rootWires_get_old
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (index : Fin source.rootWires.length) :
    (spawnNodeRawOpen source node scope portCount port).rootWires.get
        (spawnNodeRawOpenRootIndex source node scope portCount port hroot
          index) =
      Fin.castAdd portCount (source.rootWires.get index) := by
  let target := spawnNodeRawOpen source node scope portCount port
  let suffix := (allFin portCount).map
    (Fin.natAdd source.diagram.wireCount)
  have heq : target.rootWires =
      source.rootWires.map (Fin.castAdd portCount) ++ suffix := by
    simpa only [suffix, if_pos hroot] using
      spawnNodeRawOpen_rootWires source node scope portCount port
  let mappedIndex : Fin
      (source.rootWires.map (Fin.castAdd portCount)).length :=
    Fin.cast (List.length_map (as := source.rootWires)
      (Fin.castAdd portCount)).symm index
  let appendedIndex : Fin
      (source.rootWires.map (Fin.castAdd portCount) ++ suffix).length :=
    Fin.cast (by simp) (Fin.castAdd suffix.length mappedIndex)
  have hindex :
      spawnNodeRawOpenRootIndex source node scope portCount port hroot index =
        Fin.cast (congrArg List.length heq).symm appendedIndex := by
    apply Fin.ext
    simp [spawnNodeRawOpenRootIndex, appendedIndex, mappedIndex]
  rw [hindex]
  apply Eq.trans (get_of_eq heq appendedIndex)
  change (source.rootWires.map (Fin.castAdd portCount) ++ suffix).get
      appendedIndex = _
  simp only [List.get_eq_getElem, appendedIndex, Fin.val_castAdd,
    Fin.val_cast, mappedIndex]
  apply Eq.trans (List.getElem_append_left
    (as := source.rootWires.map (Fin.castAdd portCount))
    (bs := suffix) (i := index.val) (by simpa using index.isLt))
  exact List.getElem_map (Fin.castAdd portCount)

/-- The canonical old-wire embedding between complete root compiler
contexts.  At a root spawn, fresh wires occupy only the target suffix. -/
def spawnNodeRawOpenRootEmbedding
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope) :
    SpawnContextEmbedding source.diagram node scope portCount port
      source.rootWires
      (spawnNodeRawOpen source node scope portCount port).rootWires where
  index := spawnNodeRawOpenRootIndex source node scope portCount port hroot
  get := spawnNodeRawOpen_rootWires_get_old source node scope portCount port hroot
  mem_old := by
    intro wire
    rw [spawnNodeRawOpen_rootWires, if_pos hroot]
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hold | hfresh
      · rcases List.mem_map.mp hold with ⟨old, hold, heq⟩
        have : old = wire := by
          apply Fin.ext
          exact congrArg
            (fun value : Fin (source.diagram.wireCount + portCount) =>
              value.val) heq
        simpa [this] using hold
      · rcases List.mem_map.mp hfresh with ⟨fresh, _, heq⟩
        have hval := congrArg
          (fun value : Fin (source.diagram.wireCount + portCount) =>
            value.val) heq
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
    · intro hmem
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨wire, hmem, rfl⟩)

theorem spawnNodeRawOpenRootEmbedding_index_val
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (index : Fin source.rootWires.length) :
    ((spawnNodeRawOpenRootEmbedding source node scope portCount port hroot).index
      index).val = index.val := by
  rfl

/-- At a non-root spawn the complete root compiler context is only the
position-preserving image of the old root context; no fresh root-local suffix
is introduced. -/
def spawnNodeRawOpenRootEmbeddingAway
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hne : source.diagram.root ≠ scope) :
    SpawnContextEmbedding source.diagram node scope portCount port
      source.rootWires
      (spawnNodeRawOpen source node scope portCount port).rootWires where
  index := fun index => Fin.cast (by
    rw [spawnNodeRawOpen_rootWires, if_neg hne]
    simpa only [List.append_nil] using
      (List.length_map (as := source.rootWires)
        (Fin.castAdd portCount)).symm) index
  get := by
    intro index
    have heq : (spawnNodeRawOpen source node scope portCount port).rootWires =
        source.rootWires.map (Fin.castAdd portCount) := by
      simpa [if_neg hne] using
        spawnNodeRawOpen_rootWires source node scope portCount port
    let mapped : Fin
        (source.rootWires.map (Fin.castAdd portCount)).length :=
      Fin.cast ((List.length_map (as := source.rootWires)
        (Fin.castAdd portCount)).symm) index
    have hindex : Fin.cast (by
        rw [spawnNodeRawOpen_rootWires, if_neg hne]
        simpa only [List.append_nil] using
          (List.length_map (as := source.rootWires)
            (Fin.castAdd portCount)).symm) index =
        Fin.cast (congrArg List.length heq).symm mapped := by
      apply Fin.ext
      rfl
    calc
      _ =
          (spawnNodeRawOpen source node scope portCount port).rootWires.get
            (Fin.cast (congrArg List.length heq).symm mapped) := by
              apply congrArg
              exact hindex
      _ = (source.rootWires.map (Fin.castAdd portCount)).get mapped :=
        get_of_eq heq mapped
      _ = Fin.castAdd portCount (source.rootWires.get index) :=
        get_map_cast source.rootWires (Fin.castAdd portCount) index
  mem_old := by
    intro wire
    rw [spawnNodeRawOpen_rootWires, if_neg hne, List.append_nil]
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨old, hold, heq⟩
      have : old = wire := castAdd_injective _ _ heq
      simpa [this] using hold
    · intro hmem
      exact List.mem_map.mpr ⟨wire, hmem, rfl⟩

theorem spawnNodeRawOpenRootEmbeddingAway_index_val
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hne : source.diagram.root ≠ scope)
    (index : Fin source.rootWires.length) :
    ((spawnNodeRawOpenRootEmbeddingAway source node scope portCount port hne).index
      index).val = index.val := by
  rfl

/-- The old hidden-wire position in the target hidden prefix. -/
def spawnNodeRawOpenHiddenIndex
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (index : Fin source.hiddenWires.length) :
    Fin (spawnNodeRawOpen source node scope portCount port).hiddenWires.length :=
  Fin.cast (by
    have hlist := spawnNodeRawOpen_hiddenWires source node scope portCount port
    rw [if_pos hroot] at hlist
    calc
      source.hiddenWires.length + portCount =
          (source.hiddenWires.map (Fin.castAdd portCount) ++
            (allFin portCount).map
              (Fin.natAdd source.diagram.wireCount)).length := by
        simp only [List.length_append, List.length_map, Nat.add_left_cancel_iff]
        rw [allFin_eq_finRange, List.length_finRange]
      _ = (spawnNodeRawOpen source node scope portCount port).hiddenWires.length :=
        (congrArg List.length hlist).symm)
      (Fin.castAdd portCount index)

theorem spawnNodeRawOpenHiddenIndex_val
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (index : Fin source.hiddenWires.length) :
    (spawnNodeRawOpenHiddenIndex source node scope portCount port hroot
      index).val = index.val := by
  rfl

/-- The unchanged ordered boundary position in the spawned open diagram. -/
def spawnNodeRawOpenBoundaryPosition
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (position : Fin source.boundary.length) :
    Fin (spawnNodeRawOpen source node scope portCount port).boundary.length :=
  Fin.cast (by simp [spawnNodeRawOpen]) position

/-- The old external class in the spawned diagram's old-wire prefix. -/
def spawnNodeRawOpenExternalClass
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (external : Fin source.exposedWires.length) :
    Fin (spawnNodeRawOpen source node scope portCount port).exposedWires.length :=
  Fin.cast (by
    rw [spawnNodeRawOpen_exposedWires]
    exact (List.length_map (as := source.exposedWires)
      (Fin.castAdd portCount)).symm)
    external

theorem spawnNodeRawOpenExternalClass_val
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (external : Fin source.exposedWires.length) :
    (spawnNodeRawOpenExternalClass source node scope portCount port
      external).val = external.val := by
  rfl

/-- Splitting a target root valuation into exposed and hidden parts and then
restricting it along the old root prefix agrees exactly with the corresponding
source split. -/
theorem spawnNodeRaw_rootExtendWireEnv
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hroot : source.diagram.root = scope)
    (D : Type)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length → D)
    (localEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length → D) :
    let embedding := spawnNodeRawOpenRootEmbedding source node scope portCount
      port hroot
    let sourceOuter : Fin source.exposedWires.length → D :=
      outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port
    let sourceLocal : Fin source.hiddenWires.length → D := fun index =>
      localEnv (spawnNodeRawOpenHiddenIndex source node scope portCount port
        hroot index)
    (extendWireEnv outerEnv localEnv ∘
        Fin.cast (by exact List.length_append) ∘ embedding.index) =
      (extendWireEnv sourceOuter sourceLocal ∘
        Fin.cast (by exact List.length_append)) := by
  dsimp only
  funext index
  have hsourceLength : source.rootWires.length =
      source.exposedWires.length + source.hiddenWires.length := by
    exact List.length_append
  let split := Fin.cast hsourceLength index
  have hindex : index = Fin.cast hsourceLength.symm split := by
    apply Fin.ext
    rfl
  rw [hindex]
  refine Fin.addCases (motive := fun current =>
      (extendWireEnv outerEnv localEnv ∘
          Fin.cast (by exact List.length_append) ∘
          (spawnNodeRawOpenRootEmbedding source node scope portCount port
            hroot).index)
          (Fin.cast hsourceLength.symm current) =
        (extendWireEnv
            (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope
              portCount port)
            (fun hidden => localEnv
              (spawnNodeRawOpenHiddenIndex source node scope portCount port
                hroot hidden)) ∘
          Fin.cast (by exact List.length_append))
          (Fin.cast hsourceLength.symm current))
    (fun external => ?_) (fun hidden => ?_) split
  · have htargetIndex :
        Fin.cast (by exact List.length_append)
          ((spawnNodeRawOpenRootEmbedding source node scope portCount port
            hroot).index
            (Fin.cast hsourceLength.symm
              (Fin.castAdd source.hiddenWires.length external))) =
          Fin.castAdd
            (spawnNodeRawOpen source node scope portCount port).hiddenWires.length
            (spawnNodeRawOpenExternalClass source node scope portCount port
              external) := by
      apply Fin.ext
      rfl
    have hsourceIndex :
        Fin.cast (by exact List.length_append)
            (Fin.cast hsourceLength.symm
              (Fin.castAdd source.hiddenWires.length external)) =
          Fin.castAdd source.hiddenWires.length external := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [htargetIndex, hsourceIndex]
    simp [extendWireEnv]
  · have htargetIndex :
        Fin.cast (by exact List.length_append)
          ((spawnNodeRawOpenRootEmbedding source node scope portCount port
            hroot).index
            (Fin.cast hsourceLength.symm
              (Fin.natAdd source.exposedWires.length hidden))) =
          Fin.natAdd
            (spawnNodeRawOpen source node scope portCount port).exposedWires.length
            (spawnNodeRawOpenHiddenIndex source node scope portCount port
              hroot hidden) := by
      apply Fin.ext
      have hlen :
          (spawnNodeRawOpen source node scope portCount port).exposedWires.length =
            source.exposedWires.length :=
        (congrArg List.length
          (spawnNodeRawOpen_exposedWires source node scope portCount port)).trans
            (List.length_map (as := source.exposedWires)
              (Fin.castAdd portCount))
      simp only [Fin.val_cast, Fin.val_natAdd]
      rw [spawnNodeRawOpenRootEmbedding_index_val,
        spawnNodeRawOpenHiddenIndex_val, hlen]
      rfl
    have hsourceIndex :
        Fin.cast (by exact List.length_append)
            (Fin.cast hsourceLength.symm
              (Fin.natAdd source.exposedWires.length hidden)) =
          Fin.natAdd source.exposedWires.length hidden := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [htargetIndex, hsourceIndex]
    simp [extendWireEnv]

/-- The non-root counterpart of `spawnNodeRaw_rootExtendWireEnv`: both root
parts are position-preserving old-wire images, so no target-local valuation
must be discarded. -/
theorem spawnNodeRaw_rootExtendWireEnvAway
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hne : source.diagram.root ≠ scope)
    (D : Type)
    (outerEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).exposedWires.length → D)
    (localEnv : Fin
      (spawnNodeRawOpen source node scope portCount port).hiddenWires.length → D) :
    let embedding := spawnNodeRawOpenRootEmbeddingAway source node scope
      portCount port hne
    let sourceOuter : Fin source.exposedWires.length → D :=
      outerEnv ∘ spawnNodeRawOpenExternalClass source node scope portCount port
    let hiddenLength :
        (spawnNodeRawOpen source node scope portCount port).hiddenWires.length =
          source.hiddenWires.length := by
      rw [spawnNodeRawOpen_hiddenWires, if_neg hne, List.append_nil]
      exact List.length_map _
    let sourceLocal : Fin source.hiddenWires.length → D :=
      localEnv ∘ Fin.cast hiddenLength.symm
    (extendWireEnv outerEnv localEnv ∘
        Fin.cast (by exact List.length_append) ∘ embedding.index) =
      (extendWireEnv sourceOuter sourceLocal ∘
        Fin.cast (by exact List.length_append)) := by
  dsimp only
  funext index
  let sourceLength : source.rootWires.length =
      source.exposedWires.length + source.hiddenWires.length :=
    List.length_append
  let split := Fin.cast sourceLength index
  have hindex : index = Fin.cast sourceLength.symm split := by
    apply Fin.ext
    rfl
  rw [hindex]
  refine Fin.addCases (motive := fun current =>
      (extendWireEnv outerEnv localEnv ∘
          Fin.cast (by exact List.length_append) ∘
          (spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
            hne).index) (Fin.cast sourceLength.symm current) =
        (extendWireEnv
            (outerEnv ∘ spawnNodeRawOpenExternalClass source node scope
              portCount port)
            (localEnv ∘ Fin.cast (by
              rw [spawnNodeRawOpen_hiddenWires, if_neg hne, List.append_nil]
              exact (List.length_map (as := source.hiddenWires)
                (Fin.castAdd portCount)).symm)) ∘
          Fin.cast (by exact List.length_append))
          (Fin.cast sourceLength.symm current))
    (fun external => ?_) (fun hidden => ?_) split
  · simp only [Function.comp_apply]
    have htarget :
        (Fin.cast (by exact List.length_append)
          ((spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
            hne).index
            (Fin.cast sourceLength.symm
              (Fin.castAdd source.hiddenWires.length external)))).val =
          (spawnNodeRawOpenExternalClass source node scope portCount port
            external).val := by
      simp only [Fin.val_cast]
      rw [spawnNodeRawOpenRootEmbeddingAway_index_val]
      rfl
    have hsource :
        (Fin.cast (by exact List.length_append)
          (Fin.cast sourceLength.symm
            (Fin.castAdd source.hiddenWires.length external))).val =
          external.val := by rfl
    rw [show Fin.cast (by exact List.length_append)
        ((spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
          hne).index
          (Fin.cast sourceLength.symm
            (Fin.castAdd source.hiddenWires.length external))) =
      Fin.castAdd
        (spawnNodeRawOpen source node scope portCount port).hiddenWires.length
        (spawnNodeRawOpenExternalClass source node scope portCount port external)
      by apply Fin.ext; exact htarget]
    rw [show Fin.cast (by exact List.length_append)
        (Fin.cast sourceLength.symm
          (Fin.castAdd source.hiddenWires.length external)) =
      Fin.castAdd source.hiddenWires.length external
      by apply Fin.ext; exact hsource]
    simp [extendWireEnv]
  · simp only [Function.comp_apply]
    have hexposed :
        (spawnNodeRawOpen source node scope portCount port).exposedWires.length =
          source.exposedWires.length := by
      rw [spawnNodeRawOpen_exposedWires]
      exact List.length_map _
    let hiddenLength :
        (spawnNodeRawOpen source node scope portCount port).hiddenWires.length =
          source.hiddenWires.length := by
      rw [spawnNodeRawOpen_hiddenWires, if_neg hne, List.append_nil]
      exact List.length_map _
    rw [show Fin.cast (by exact List.length_append)
        ((spawnNodeRawOpenRootEmbeddingAway source node scope portCount port
          hne).index
          (Fin.cast sourceLength.symm
            (Fin.natAdd source.exposedWires.length hidden))) =
      Fin.natAdd
        (spawnNodeRawOpen source node scope portCount port).exposedWires.length
        (Fin.cast hiddenLength.symm hidden) by
      apply Fin.ext
      simp only [Fin.val_cast]
      rw [spawnNodeRawOpenRootEmbeddingAway_index_val]
      simp only [Fin.val_natAdd]
      rw [hexposed]
      rfl]
    rw [show Fin.cast (by exact List.length_append)
        (Fin.cast sourceLength.symm
          (Fin.natAdd source.exposedWires.length hidden)) =
      Fin.natAdd source.exposedWires.length hidden by
      apply Fin.ext
      rfl]
    simp [extendWireEnv, hiddenLength]
/-- Spawn preserves the exact quotient map from ordered boundary positions to
external wire classes, including repeated boundary aliases. -/
theorem spawnNodeRawOpen_boundaryClass
    (source : OpenConcreteDiagram)
    (node : CNode source.diagram.regionCount)
    (scope : Fin source.diagram.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (position : Fin source.boundary.length) :
    (spawnNodeRawOpen source node scope portCount port).boundaryClass
        (spawnNodeRawOpenBoundaryPosition source node scope portCount port
          position) =
      spawnNodeRawOpenExternalClass source node scope portCount port
        (source.boundaryClass position) := by
  symm
  apply OpenConcreteDiagram.boundaryClass_complete
  have hleft := get_map_cast source.exposedWires
    (Fin.castAdd portCount) (source.boundaryClass position)
  have hleftTarget :
      (spawnNodeRawOpen source node scope portCount port).exposedWires.get
          (spawnNodeRawOpenExternalClass source node scope portCount port
            (source.boundaryClass position)) =
        Fin.castAdd portCount
          (source.exposedWires.get (source.boundaryClass position)) := by
    let target := spawnNodeRawOpen source node scope portCount port
    have heq : target.exposedWires =
        source.exposedWires.map (Fin.castAdd portCount) :=
      spawnNodeRawOpen_exposedWires source node scope portCount port
    let mappedIndex : Fin
        (source.exposedWires.map (Fin.castAdd portCount)).length :=
      Fin.cast (List.length_map (as := source.exposedWires)
        (Fin.castAdd portCount)).symm (source.boundaryClass position)
    have hindex :
        spawnNodeRawOpenExternalClass source node scope portCount port
            (source.boundaryClass position) =
          Fin.cast (congrArg List.length heq).symm mappedIndex := by
      apply Fin.ext
      rfl
    rw [hindex]
    apply Eq.trans (get_of_eq heq mappedIndex)
    exact hleft
  apply Eq.trans hleftTarget
  rw [OpenConcreteDiagram.boundaryClass_sound]
  simp [spawnNodeRawOpenBoundaryPosition, spawnNodeRawOpen]

/-- Away from the spawn scope, extending a positional old-wire context is
exactly the positional image of extending the source context. -/
theorem SpawnContextEmbedding.mapOldContext_extend_of_ne
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (hne : region ≠ scope) :
    ConcreteElaboration.WireContext.extend
        (d := spawnNodeRaw input node scope portCount port)
        (SpawnContextEmbedding.mapOldContext input portCount source) region =
      SpawnContextEmbedding.mapOldContext input portCount
        (source.extend region) := by
  unfold ConcreteElaboration.WireContext.extend
  rw [spawnNodeRaw_exactScopeWires, if_neg hne, List.append_nil]
  simp [SpawnContextEmbedding.mapOldContext, List.map_append]
  rfl

/-- Away from the spawn scope, exact-scope traversal has the same number of
local wires as before the spawn. -/
theorem spawnNodeRaw_exactScopeWires_length_of_ne
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (hne : region ≠ scope) :
    (ConcreteElaboration.exactScopeWires
        (spawnNodeRaw input node scope portCount port) region).length =
      (ConcreteElaboration.exactScopeWires input region).length := by
  rw [spawnNodeRaw_exactScopeWires, if_neg hne, List.append_nil]
  exact List.length_map _

/-- The explicit lexical wire map below a strict descendant of the spawn
scope.  Inherited indices use the ambient embedding; local indices retain
their intrinsic position because no fresh wire is bound at that descendant. -/
noncomputable def spawnNodeRaw_extendedWireMapOfNe
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (region : Fin input.regionCount) (hne : region ≠ scope) :
    Fin (source.extend region).length → Fin (target.extend region).length :=
  fun index =>
    Fin.cast
      ((congrArg (fun localCount => target.length + localCount)
          (spawnNodeRaw_exactScopeWires_length_of_ne input node scope region
            portCount port hne).symm).trans
        (ConcreteElaboration.WireContext.length_extend target region).symm)
      (extendWireRenaming embedding.index
        (ConcreteElaboration.exactScopeWires input region).length
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region) index))

/-- The explicit strict-descendant map carries each source lexical wire to
the corresponding old wire in the spawned diagram. -/
theorem spawnNodeRaw_extendedWireMapOfNe_spec
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (region : Fin input.regionCount) (hne : region ≠ scope)
    (index : Fin (source.extend region).length) :
    (target.extend region).get
        (spawnNodeRaw_extendedWireMapOfNe embedding region hne index) =
      Fin.castAdd portCount ((source.extend region).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source region) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : spawnNodeRaw_extendedWireMapOfNe embedding region hne
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input region).length outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (spawnNodeRaw input node scope portCount port) region).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [spawnNodeRaw_extendedWireMapOfNe, extendWireRenaming]
    rw [hmap]
    simpa [ConcreteElaboration.WireContext.extend] using embedding.get outer
  · let hlength := spawnNodeRaw_exactScopeWires_length_of_ne input node scope
      region portCount port hne
    have hmap : spawnNodeRaw_extendedWireMapOfNe embedding region hne
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length (Fin.cast hlength.symm localIndex)) := by
      apply Fin.ext
      simp [spawnNodeRaw_extendedWireMapOfNe, extendWireRenaming]
    rw [hmap]
    have hlist := spawnNodeRaw_exactScopeWires input node scope region
      portCount port
    rw [if_neg hne] at hlist
    simp only [List.append_nil] at hlist
    simp [ConcreteElaboration.WireContext.extend, hlist]
    exact List.getElem_map _

/-- In a duplicate-free extended context, the canonical lookup embedding is
exactly the explicit ambient-plus-local strict-descendant map. -/
theorem SpawnContextEmbedding.extend_index_eq_map_of_ne
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (region : Fin input.regionCount) (hne : region ≠ scope)
    (targetNodup : (target.extend region).Nodup)
    (index : Fin (source.extend region).length) :
    (embedding.extend region).index index =
      spawnNodeRaw_extendedWireMapOfNe embedding region hne index := by
  symm
  apply SpawnContextEmbedding.index_eq_of_get
    (embedding.extend region) targetNodup index
  exact spawnNodeRaw_extendedWireMapOfNe_spec embedding region hne index

/-- At the spawn scope, the local wire block consists of the old local prefix
followed by exactly the fresh port wires. -/
theorem spawnNodeRaw_exactScopeWires_length_at_scope
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    (ConcreteElaboration.exactScopeWires
        (spawnNodeRaw input node scope portCount port) scope).length =
      (ConcreteElaboration.exactScopeWires input scope).length + portCount := by
  rw [spawnNodeRaw_exactScopeWires]
  simp only [allFin_eq_finRange]
  calc
    (List.map (Fin.castAdd portCount)
          (ConcreteElaboration.exactScopeWires input scope) ++
        List.map (Fin.natAdd input.wireCount)
          (List.finRange portCount)).length =
        (ConcreteElaboration.exactScopeWires input scope).length +
          (List.finRange portCount).length := by
            rw [List.length_append, List.length_map, List.length_map]
    _ = (ConcreteElaboration.exactScopeWires input scope).length +
          portCount := by simp

/-- Embed the source context extended at the spawn scope into the target
extension.  Old local wires retain their positions in the local prefix; fresh
port wires have no source preimage. -/
noncomputable def spawnNodeRaw_extendedWireMapAtScope
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target) :
    Fin (source.extend scope).length → Fin (target.extend scope).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend target scope).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (spawnNodeRaw input node scope portCount port) scope).length
          (embedding.index outer))
        (fun localIndex => Fin.natAdd target.length
          (Fin.cast
            (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
              portCount port).symm
            (Fin.castAdd portCount localIndex)))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source scope) index))

theorem spawnNodeRaw_extendedWireMapAtScope_spec
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (index : Fin (source.extend scope).length) :
    (target.extend scope).get
        (spawnNodeRaw_extendedWireMapAtScope embedding index) =
      Fin.castAdd portCount ((source.extend scope).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source scope) index
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source scope).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have hmap : spawnNodeRaw_extendedWireMapAtScope embedding
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source scope).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input scope).length outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target scope).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (spawnNodeRaw input node scope portCount port) scope).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [spawnNodeRaw_extendedWireMapAtScope]
    rw [hmap]
    simpa [ConcreteElaboration.WireContext.extend] using embedding.get outer
  · let hlength := spawnNodeRaw_exactScopeWires_length_at_scope input node scope
      portCount port
    have hmap : spawnNodeRaw_extendedWireMapAtScope embedding
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source scope).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target scope).symm
          (Fin.natAdd target.length
            (Fin.cast hlength.symm (Fin.castAdd portCount localIndex))) := by
      apply Fin.ext
      simp [spawnNodeRaw_extendedWireMapAtScope]
    rw [hmap]
    have hlist := spawnNodeRaw_exactScopeWires input node scope scope
      portCount port
    simp [ConcreteElaboration.WireContext.extend, hlist]
    change (List.map (Fin.castAdd portCount)
      (ConcreteElaboration.exactScopeWires input scope) ++
      List.map (Fin.natAdd input.wireCount) (allFin portCount))[localIndex.val] =
        Fin.castAdd portCount
          (ConcreteElaboration.exactScopeWires input scope)[localIndex.val]
    rw [List.getElem_append_left (by
      rw [List.length_map]
      exact localIndex.isLt)]
    exact List.getElem_map _

theorem SpawnContextEmbedding.extend_index_eq_map_at_scope
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (targetNodup : (target.extend scope).Nodup)
    (index : Fin (source.extend scope).length) :
    (embedding.extend scope).index index =
      spawnNodeRaw_extendedWireMapAtScope embedding index := by
  symm
  apply SpawnContextEmbedding.index_eq_of_get
    (embedding.extend scope) targetNodup index
  exact spawnNodeRaw_extendedWireMapAtScope_spec embedding index

/-- Restricting a target valuation to the old-local prefix agrees with the
explicit ambient-plus-local embedding at the spawn scope. -/
theorem spawnNodeRaw_extendWireEnv_at_scope
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (outerEnv : Fin target.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires
      (spawnNodeRaw input node scope portCount port) scope).length → D) :
    (extendWireEnv outerEnv localEnv ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend target scope)) ∘
        spawnNodeRaw_extendedWireMapAtScope embedding =
      extendWireEnv (outerEnv ∘ embedding.index)
          (fun localWire => localEnv
            (Fin.cast
              (spawnNodeRaw_exactScopeWires_length_at_scope input node scope
                portCount port).symm
              (Fin.castAdd portCount localWire))) ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend source scope) := by
  funext wire
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source scope) wire
  have hrecover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source scope).symm
      split = wire := by
    apply Fin.ext
    rfl
  rw [← hrecover]
  refine Fin.addCases (fun outer => ?_) (fun localWire => ?_) split
  · simp [spawnNodeRaw_extendedWireMapAtScope, extendWireEnv,
      Function.comp_def]
  · simp [spawnNodeRaw_extendedWireMapAtScope, extendWireEnv,
      Function.comp_def]

/-- Local traversal inserts the appended node after all old nodes in its
region and before the unchanged child-region occurrences. -/
theorem spawnNodeRaw_localOccurrences
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) :
    ConcreteElaboration.localOccurrences
        (spawnNodeRaw input node scope portCount port) region =
      (filterFin fun old => decide ((input.nodes old).region = region)).map
          (fun old => ConcreteElaboration.LocalOccurrence.node old.castSucc) ++
        (if node.region = region then
          [ConcreteElaboration.LocalOccurrence.node (Fin.last input.nodeCount)]
        else []) ++
        (filterFin fun child =>
          decide ((input.regions child).parent? = some region)).map
            ConcreteElaboration.LocalOccurrence.child := by
  unfold ConcreteElaboration.localOccurrences filterFin
  change (List.filter _ (allFin (input.nodeCount + 1))).map _ ++
      (List.filter _ (allFin input.regionCount)).map _ = _
  rw [allFin_succ_last, List.filter_append, List.map_append]
  have hold :
      (List.filter
          (fun current => decide
            (((spawnNodeRaw input node scope portCount port).nodes current).region =
              region))
          ((allFin input.nodeCount).map (Fin.castAdd 1))).map
            (ConcreteElaboration.LocalOccurrence.node
              (regions := input.regionCount)) =
        (filterFin fun old => decide ((input.nodes old).region = region)).map
          (fun old => ConcreteElaboration.LocalOccurrence.node
            (regions := input.regionCount) old.castSucc) := by
    simp only [List.filter_map, List.map_map, filterFin]
    calc
      List.map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := input.regionCount) ∘ Fin.castAdd 1)
          (List.filter _ (allFin input.nodeCount)) =
        List.map
          (fun old : Fin input.nodeCount =>
            ConcreteElaboration.LocalOccurrence.node
              (regions := input.regionCount) old.castSucc)
          (List.filter _ (allFin input.nodeCount)) := by
            apply List.map_congr_left
            intro old _
            congr 1
      _ = _ := by
        apply congrArg (List.map fun old : Fin input.nodeCount =>
          ConcreteElaboration.LocalOccurrence.node
            (regions := input.regionCount) old.castSucc)
        apply congrArg (fun predicate =>
          List.filter predicate (allFin input.nodeCount))
        funext old
        simp only [Function.comp_apply]
        have hcast : Fin.castAdd 1 old = old.castSucc := by
          apply Fin.ext
          rfl
        rw [hcast]
        rw [spawnNodeRaw_oldNode]
        rfl
  have hnew :
      (List.filter
          (fun current => decide
            (((spawnNodeRaw input node scope portCount port).nodes current).region =
              region))
          [Fin.last input.nodeCount]).map
            (ConcreteElaboration.LocalOccurrence.node
              (regions := input.regionCount)) =
        if node.region = region then
          [ConcreteElaboration.LocalOccurrence.node
            (regions := input.regionCount) (Fin.last input.nodeCount)]
        else [] := by
    by_cases hregion : node.region = region
    · rw [if_pos hregion]
      have hfiltered :
          List.filter
              (fun current => decide
                (((spawnNodeRaw input node scope portCount port).nodes current).region =
                  region))
              [Fin.last input.nodeCount] =
            [Fin.last input.nodeCount] := by
        apply List.filter_eq_self.mpr
        intro current hmem
        have hcurrent : current = Fin.last input.nodeCount := by
          simpa only [List.mem_singleton] using hmem
        subst current
        rw [spawnNodeRaw_newNode]
        exact decide_eq_true hregion
      rw [hfiltered]
      rfl
    · rw [if_neg hregion]
      have hfiltered :
          List.filter
              (fun current => decide
                (((spawnNodeRaw input node scope portCount port).nodes current).region =
                  region))
              [Fin.last input.nodeCount] = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro current hmem htest
        have hcurrent : current = Fin.last input.nodeCount := by
          simpa only [List.mem_singleton] using hmem
        subst current
        rw [spawnNodeRaw_newNode] at htest
        exact hregion (of_decide_eq_true htest)
      rw [hfiltered]
      rfl
  dsimp only [spawnNodeRaw] at hold hnew ⊢
  rw [hold, hnew]
  rfl

/-- Embed every pre-existing local occurrence into the append-only spawned
diagram.  Region occurrences are unchanged; node occurrences use the old-node
prefix injection. -/
def spawnNodeRaw_oldOccurrence (input : ConcreteDiagram) :
    ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount →
      ConcreteElaboration.LocalOccurrence input.regionCount
        (input.nodeCount + 1)
  | .node old => .node old.castSucc
  | .child child => .child child

/-- At every region other than the spawn scope, local traversal is exactly
the mapped traversal of the source diagram. -/
theorem spawnNodeRaw_localOccurrences_old_of_ne
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (hnode : node.region = scope)
    (hne : region ≠ scope) :
    ConcreteElaboration.localOccurrences
        (spawnNodeRaw input node scope portCount port) region =
      (ConcreteElaboration.localOccurrences input region).map
        (spawnNodeRaw_oldOccurrence input) := by
  rw [spawnNodeRaw_localOccurrences]
  have hnodeNe : node.region ≠ region := by
    intro heq
    exact hne (heq.symm.trans hnode)
  rw [if_neg hnodeNe]
  unfold ConcreteElaboration.localOccurrences
  simp only [List.append_nil, List.map_append, List.map_map]
  congr 1

/-- Local traversal is unchanged away from the appended node's actual region,
even when its fresh wire is scoped at a distinct ancestor. -/
theorem spawnNodeRaw_localOccurrences_old_of_region_ne
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort) (hne : region ≠ node.region) :
    ConcreteElaboration.localOccurrences
        (spawnNodeRaw input node scope portCount port) region =
      (ConcreteElaboration.localOccurrences input region).map
        (spawnNodeRaw_oldOccurrence input) := by
  rw [spawnNodeRaw_localOccurrences, if_neg (Ne.symm hne)]
  unfold ConcreteElaboration.localOccurrences
  simp only [List.append_nil, List.map_append, List.map_map]
  congr 1

/-- Compilation of any pre-existing direct occurrence commutes with spawn,
provided the recursive child compilers commute with the same lexical wire
embedding.  This covers nodes, cuts, and binder-extending bubbles. -/
theorem spawnNodeRaw_compileOccurrenceWith?_old
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (context : ConcreteElaboration.WireContext input) →
      ConcreteElaboration.BinderContext input rels →
      Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (context : ConcreteElaboration.WireContext
        (spawnNodeRaw input node scope portCount port)) →
      ConcreteElaboration.BinderContext
        (spawnNodeRaw input node scope portCount port) rels →
      Option (Region signature context.length rels))
    (binders : ConcreteElaboration.BinderContext input rels)
    (occurrence : ConcreteElaboration.LocalOccurrence input.regionCount
      input.nodeCount)
    (targetNodup : target.Nodup)
    (targetDisjoint :
      (spawnNodeRaw input node scope portCount port).WireEndpointsAreDisjoint)
    (hrecurse : ∀ {childRels : RelCtx}
      (child : Fin input.regionCount)
      (childBinders : ConcreteElaboration.BinderContext input childRels),
      occurrence = .child child →
      targetRecurse child target childBinders =
        (sourceRecurse child source childBinders).map
          (Region.renameWires embedding.index)) :
    ConcreteElaboration.compileOccurrenceWith? signature
        (spawnNodeRaw input node scope portCount port) targetRecurse target
        binders (spawnNodeRaw_oldOccurrence input occurrence) =
      (ConcreteElaboration.compileOccurrenceWith? signature input sourceRecurse
        source binders occurrence).map (Item.renameWires embedding.index) := by
  cases occurrence with
  | node old =>
      exact spawnNodeRaw_compileNode?_old input node scope portCount port source
        target embedding binders targetNodup targetDisjoint old
  | child child =>
      cases hregion : input.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, spawnNodeRaw,
            spawnNodeRaw_oldOccurrence, hregion]
      | cut parent =>
          have hrec := hrecurse child binders rfl
          cases hsource : sourceRecurse child source binders with
          | none =>
              simp [hsource] at hrec
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence]
              rw [show (spawnNodeRaw input node scope portCount port).regions
                child = input.regions child by rfl, hregion]
              simp only
              rw [hsource]
              cases htarget : targetRecurse child target binders with
              | none => rfl
              | some targetBody => simp [htarget] at hrec
          | some body =>
              simp [hsource] at hrec
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence]
              rw [show (spawnNodeRaw input node scope portCount port).regions
                child = input.regions child by rfl, hregion]
              simp only
              rw [hsource]
              cases htarget : targetRecurse child target binders with
              | none => simp [htarget] at hrec
              | some targetBody =>
                  simp [htarget] at hrec
                  subst targetBody
                  rfl
      | bubble parent arity =>
          have hrec := hrecurse child (binders.push child arity) rfl
          cases hsource : sourceRecurse child source
              (binders.push child arity) with
          | none =>
              simp [hsource] at hrec
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence]
              rw [show (spawnNodeRaw input node scope portCount port).regions
                child = input.regions child by rfl, hregion]
              simp only
              rw [hsource]
              cases htarget : targetRecurse child target
                  (binders.push child arity) with
              | none =>
                  change (targetRecurse child target
                    (binders.push child arity)).bind
                      (fun body => some (Item.bubble arity body)) = none
                  rw [htarget]
                  rfl
              | some targetBody => simp [htarget] at hrec
          | some body =>
              simp [hsource] at hrec
              simp only [ConcreteElaboration.compileOccurrenceWith?,
                spawnNodeRaw_oldOccurrence]
              rw [show (spawnNodeRaw input node scope portCount port).regions
                child = input.regions child by rfl, hregion]
              simp only
              rw [hsource]
              cases htarget : targetRecurse child target
                  (binders.push child arity) with
              | none => simp [htarget] at hrec
              | some targetBody =>
                  simp [htarget] at hrec
                  subst targetBody
                  change (targetRecurse child target
                    (binders.push child arity)).bind
                      (fun current => some (Item.bubble arity current)) =
                    some (Item.bubble arity
                      (Region.renameWires embedding.index body))
                  rw [htarget]
                  rfl

private theorem region_mk_eq_of_local_eq
    {outer leftLocal rightLocal : Nat}
    (hlocal : leftLocal = rightLocal)
    (left : ItemSeq signature (outer + leftLocal) rels)
    (right : ItemSeq signature (outer + rightLocal) rels)
    (hitems : left.castWiresEq
      (congrArg (fun localCount => outer + localCount) hlocal) = right) :
    Region.mk leftLocal left = Region.mk rightLocal right := by
  subst rightLocal
  cases hitems
  rfl

/-- Finishing a strict-descendant region after compiling its mapped items
commutes with the ambient spawn embedding. -/
theorem spawnNodeRaw_finishRegion_old_of_ne
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope region : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (hne : region ≠ scope)
    (items : ItemSeq signature (source.extend region).length rels) :
    ConcreteElaboration.finishRegion
        (spawnNodeRaw input node scope portCount port) target region
        (items.renameWires
          (spawnNodeRaw_extendedWireMapOfNe embedding region hne)) =
      (ConcreteElaboration.finishRegion input source region items).renameWires
        embedding.index := by
  unfold ConcreteElaboration.finishRegion
  simp only [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp, Region.renameWires]
  let hlength := spawnNodeRaw_exactScopeWires_length_of_ne input node scope
    region portCount port hne
  apply region_mk_eq_of_local_eq hlength
  rw [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp]
  congr 1

private theorem direct_child_encloses
    {d : ConcreteDiagram} {parent child : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    d.Encloses parent child := by
  have hpositive : 0 < d.regionCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  change (match (d.regions child).parent? with
    | none => none
    | some directParent => d.climb 0 directParent) = some parent
  rw [hparent]
  rfl

/-- A concrete route records an actual ancestor chain. -/
theorem regionRoute_encloses
    (input : ConcreteDiagram)
    (hinput : input.WellFormed signature)
    {start target : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start target path) :
    input.Encloses start target := by
  induction route with
  | here region => exact ConcreteDiagram.Encloses.refl input region
  | @step start child target rest hparent position hposition tail ih =>
      exact ConcreteElaboration.checked_encloses_trans hinput
        (direct_child_encloses hparent) ih

/-- Distinct children of a well-founded parent cannot both enclose one
descendant.  This is the tree fact needed to classify every non-focused
compiler occurrence as an unaffected side branch. -/
private theorem checked_sibling_not_encloses_descendant
    (input : ConcreteDiagram)
    (hinput : input.WellFormed signature)
    {parent selected other descendant : Fin input.regionCount}
    (hselected : (input.regions selected).parent? = some parent)
    (hother : (input.regions other).parent? = some parent)
    (hselectedDescendant : input.Encloses selected descendant)
    (hne : other ≠ selected) :
    ¬ input.Encloses other descendant := by
  intro hotherDescendant
  obtain ⟨selectedSteps, hselectedClimb⟩ := hselectedDescendant
  obtain ⟨otherSteps, hotherClimb⟩ := hotherDescendant
  obtain ⟨rootSteps, hparentRoot⟩ :=
    hinput.all_regions_reach_root parent
  have hselectedParent : input.climb (selectedSteps.val + 1) descendant =
      some parent := by
    apply ConcreteElaboration.climb_add hselectedClimb
    simp [ConcreteDiagram.climb, hselected]
  have hotherParent : input.climb (otherSteps.val + 1) descendant =
      some parent := by
    apply ConcreteElaboration.climb_add hotherClimb
    simp [ConcreteDiagram.climb, hother]
  have hselectedRoot :
      input.climb ((selectedSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add hselectedParent hparentRoot
  have hotherRoot :
      input.climb ((otherSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add hotherParent hparentRoot
  have hsteps :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique input
      hinput.root_is_sheet hselectedRoot hotherRoot
  have hsameSteps : selectedSteps.val = otherSteps.val := by omega
  rw [hsameSteps] at hselectedClimb
  exact hne (Option.some.inj (hotherClimb.symm.trans hselectedClimb))

/-- Away from both the appended node's ancestor chain and the wire-introduction
site, compilation is the old intrinsic region renamed through the lexical
embedding. This is the routed closed-anchor variant where node region and wire
scope may differ. -/
theorem spawnNodeRaw_compileRegion?_old_of_not_encloses_node
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (scopeEnclosesNode : input.Encloses scope node.region) :
    ∀ {rels : RelCtx} (fuel : Nat) (region : Fin input.regionCount)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input node scope portCount port))
      (embedding : SpawnContextEmbedding input node scope portCount port
        source target)
      (binders : ConcreteElaboration.BinderContext input rels),
      ¬ input.Encloses region node.region →
      (source.extend region).Exact region →
      (target.extend region).Exact region →
      ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel region target
          binders =
        (ConcreteElaboration.compileRegion? signature input fuel region source
          binders).map (Region.renameWires embedding.index) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region source target embedding binders hnotAbove hsource htargetExact
      rfl
  | succ fuel ih =>
      intro region source target embedding binders hnotAbove hsource htargetExact
      have hnodeNe : region ≠ node.region := by
        intro equality
        subst region
        exact hnotAbove (ConcreteDiagram.Encloses.refl input node.region)
      have hscopeNe : region ≠ scope := by
        intro equality
        subst region
        exact hnotAbove scopeEnclosesNode
      simp only [ConcreteElaboration.compileRegion?]
      rw [spawnNodeRaw_localOccurrences_old_of_region_ne input node scope region
        portCount port hnodeNe]
      let sourceExtended := source.extend region
      let targetExtended := target.extend region
      let extendedEmbedding := embedding.extend region
      have hoccurrence : ∀ occurrence,
          occurrence ∈ ConcreteElaboration.localOccurrences input region →
          ConcreteElaboration.compileOccurrenceWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              targetExtended binders
              (spawnNodeRaw_oldOccurrence input occurrence) =
            (ConcreteElaboration.compileOccurrenceWith? signature input
              (ConcreteElaboration.compileRegion? signature input fuel)
              sourceExtended binders occurrence).map
                (Item.renameWires extendedEmbedding.index) := by
        intro occurrence hmem
        apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount
          port sourceExtended targetExtended extendedEmbedding
          (ConcreteElaboration.compileRegion? signature input fuel)
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input node scope portCount port) fuel)
          binders occurrence htargetExact.nodup
          htarget.wire_endpoints_are_disjoint
        intro childRels child childBinders heq
        subst occurrence
        have hparent :=
          (ConcreteElaboration.mem_localOccurrences_child input region child).mp
            hmem
        have hregionChild : input.Encloses region child :=
          direct_child_encloses hparent
        have hchildNotAbove : ¬ input.Encloses child node.region := by
          intro hchildAbove
          exact hnotAbove (ConcreteElaboration.checked_encloses_trans hinput
            hregionChild hchildAbove)
        have hsourceChild := hsource.extend_child hinput hparent
        have htargetChild := htargetExact.extend_child htarget hparent
        exact ih child sourceExtended targetExtended extendedEmbedding
          childBinders hchildNotAbove hsourceChild htargetChild
      have hsequence := ConcreteElaboration.compileOccurrencesWith?_map
        (ConcreteElaboration.compileRegion? signature input fuel)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        sourceExtended targetExtended binders binders
        (spawnNodeRaw_oldOccurrence input) extendedEmbedding.index
        (ConcreteElaboration.localOccurrences input region) hoccurrence
      have hsequence' :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              (target.extend region) binders
              ((ConcreteElaboration.localOccurrences input region).map
                (spawnNodeRaw_oldOccurrence input)) =
            (ConcreteElaboration.compileOccurrencesWith? signature input
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend region) binders
              (ConcreteElaboration.localOccurrences input region)).map
                (ItemSeq.renameWires extendedEmbedding.index) := by
        simpa only [sourceExtended, targetExtended] using hsequence
      cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
          input (ConcreteElaboration.compileRegion? signature input fuel)
          sourceExtended binders
          (ConcreteElaboration.localOccurrences input region) with
      | none =>
          have htargetItems := hsequence'
          rw [hsourceItems] at htargetItems
          simp only [Option.map_none] at htargetItems
          change (ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node scope portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node scope portCount port) fuel)
            (target.extend region) binders
            ((ConcreteElaboration.localOccurrences input region).map
              (spawnNodeRaw_oldOccurrence input))).bind
              (fun current => some (ConcreteElaboration.finishRegion
                (spawnNodeRaw input node scope portCount port) target region
                current)) = none
          rw [htargetItems]
          rfl
      | some items =>
          have htargetItems := hsequence'
          rw [hsourceItems] at htargetItems
          simp only [Option.map_some] at htargetItems
          change (ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node scope portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node scope portCount port) fuel)
            (target.extend region) binders
            ((ConcreteElaboration.localOccurrences input region).map
              (spawnNodeRaw_oldOccurrence input))).bind
              (fun current => some (ConcreteElaboration.finishRegion
                (spawnNodeRaw input node scope portCount port) target region
                current)) =
            some (Region.renameWires embedding.index
              (ConcreteElaboration.finishRegion input source region items))
          rw [htargetItems]
          simp only [Option.bind_some]
          have hwire : extendedEmbedding.index =
              spawnNodeRaw_extendedWireMapOfNe embedding region hscopeNe := by
            funext index
            exact SpawnContextEmbedding.extend_index_eq_map_of_ne embedding
              region hscopeNe htargetExact.nodup index
          rw [hwire]
          exact congrArg some
            (spawnNodeRaw_finishRegion_old_of_ne input node scope region
              portCount port source target embedding hscopeNe items)

/-- Every region outside the ancestor chain of the spawn scope compiles to its
original intrinsic region renamed through the ambient lexical embedding.  This
includes strict descendants and incomparable side branches.  The proof is by
the sole concrete compiler's fuel recursion and introduces no second compiler. -/
theorem spawnNodeRaw_compileRegion?_old_of_not_encloses
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope) :
    ∀ {rels : RelCtx} (fuel : Nat) (region : Fin input.regionCount)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input node scope portCount port))
      (embedding : SpawnContextEmbedding input node scope portCount port
        source target)
      (binders : ConcreteElaboration.BinderContext input rels),
      ¬ input.Encloses region scope →
      (source.extend region).Exact region →
      (target.extend region).Exact region →
      ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel region target
          binders =
        (ConcreteElaboration.compileRegion? signature input fuel region source
          binders).map (Region.renameWires embedding.index) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region source target embedding binders hnotAbove hsource htargetExact
      rfl
  | succ fuel ih =>
      intro region source target embedding binders hnotAbove hsource htargetExact
      have hne : region ≠ scope := by
        intro heq
        subst region
        exact hnotAbove (ConcreteDiagram.Encloses.refl input scope)
      simp only [ConcreteElaboration.compileRegion?]
      rw [spawnNodeRaw_localOccurrences_old_of_ne input node scope region
        portCount port hnode hne]
      let sourceExtended := source.extend region
      let targetExtended := target.extend region
      let extendedEmbedding := embedding.extend region
      have hoccurrence : ∀ occurrence,
          occurrence ∈ ConcreteElaboration.localOccurrences input region →
          ConcreteElaboration.compileOccurrenceWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              targetExtended binders
              (spawnNodeRaw_oldOccurrence input occurrence) =
            (ConcreteElaboration.compileOccurrenceWith? signature input
              (ConcreteElaboration.compileRegion? signature input fuel)
              sourceExtended binders occurrence).map
                (Item.renameWires extendedEmbedding.index) := by
        intro occurrence hmem
        apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount
          port sourceExtended targetExtended extendedEmbedding
          (ConcreteElaboration.compileRegion? signature input fuel)
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input node scope portCount port) fuel)
          binders occurrence htargetExact.nodup
          htarget.wire_endpoints_are_disjoint
        intro childRels child childBinders heq
        subst occurrence
        have hparent :=
          (ConcreteElaboration.mem_localOccurrences_child input region child).mp
            hmem
        have hregionChild : input.Encloses region child :=
          direct_child_encloses hparent
        have hchildNotAbove : ¬ input.Encloses child scope := by
          intro hchildAbove
          exact hnotAbove (ConcreteElaboration.checked_encloses_trans hinput
            hregionChild hchildAbove)
        have hsourceChild := hsource.extend_child hinput hparent
        have htargetChild := htargetExact.extend_child htarget hparent
        exact ih child sourceExtended targetExtended extendedEmbedding
          childBinders hchildNotAbove hsourceChild htargetChild
      have hsequence := ConcreteElaboration.compileOccurrencesWith?_map
        (ConcreteElaboration.compileRegion? signature input fuel)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        sourceExtended targetExtended binders binders
        (spawnNodeRaw_oldOccurrence input) extendedEmbedding.index
        (ConcreteElaboration.localOccurrences input region) hoccurrence
      have hsequence' :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input node scope portCount port)
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input node scope portCount port) fuel)
              (target.extend region) binders
              ((ConcreteElaboration.localOccurrences input region).map
                (spawnNodeRaw_oldOccurrence input)) =
            (ConcreteElaboration.compileOccurrencesWith? signature input
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend region) binders
              (ConcreteElaboration.localOccurrences input region)).map
                (ItemSeq.renameWires extendedEmbedding.index) := by
        simpa only [sourceExtended, targetExtended] using hsequence
      cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
          input (ConcreteElaboration.compileRegion? signature input fuel)
          sourceExtended binders
          (ConcreteElaboration.localOccurrences input region) with
      | none =>
          have htargetItems := hsequence'
          rw [hsourceItems] at htargetItems
          simp only [Option.map_none] at htargetItems
          change (ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node scope portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node scope portCount port) fuel)
            (target.extend region) binders
            ((ConcreteElaboration.localOccurrences input region).map
              (spawnNodeRaw_oldOccurrence input))).bind
              (fun current => some (ConcreteElaboration.finishRegion
                (spawnNodeRaw input node scope portCount port) target region
                current)) = none
          rw [htargetItems]
          rfl
      | some items =>
          have htargetItems := hsequence'
          rw [hsourceItems] at htargetItems
          simp only [Option.map_some] at htargetItems
          change (ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input node scope portCount port)
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input node scope portCount port) fuel)
            (target.extend region) binders
            ((ConcreteElaboration.localOccurrences input region).map
              (spawnNodeRaw_oldOccurrence input))).bind
              (fun current => some (ConcreteElaboration.finishRegion
                (spawnNodeRaw input node scope portCount port) target region
                current)) =
            some (Region.renameWires embedding.index
              (ConcreteElaboration.finishRegion input source region items))
          rw [htargetItems]
          simp only [Option.bind_some]
          have hwire : extendedEmbedding.index =
              spawnNodeRaw_extendedWireMapOfNe embedding region hne := by
            funext index
            exact SpawnContextEmbedding.extend_index_eq_map_of_ne embedding
              region hne htargetExact.nodup index
          rw [hwire]
          exact congrArg some
            (spawnNodeRaw_finishRegion_old_of_ne input node scope region
              portCount port source target embedding hne items)

/-- Split the deterministic local traversal at the route-selected child.
Nodup of local occurrences certifies that neither frame contains the focus. -/
theorem localOccurrences_split_at_child
    (input : ConcreteDiagram) (parent selected : Fin input.regionCount)
    (position : Fin
      (ConcreteElaboration.localOccurrences input parent).length)
    (hposition : indexOf? (ConcreteElaboration.localOccurrences input parent)
      (.child selected) = some position) :
    ∃ before after,
      ConcreteElaboration.localOccurrences input parent =
        before ++ .child selected :: after ∧
      ConcreteElaboration.LocalOccurrence.child selected ∉ before ∧
      ConcreteElaboration.LocalOccurrence.child selected ∉ after := by
  let occurrences := ConcreteElaboration.localOccurrences input parent
  let before := occurrences.take position.val
  let after := occurrences.drop (position.val + 1)
  have hget : occurrences[position.val] =
      ConcreteElaboration.LocalOccurrence.child selected := by
    have hsound := indexOf?_sound hposition
    simpa only [occurrences, List.get_eq_getElem] using hsound
  have hdrop : occurrences.drop position.val =
      ConcreteElaboration.LocalOccurrence.child selected :: after := by
    rw [List.drop_eq_getElem_cons position.isLt, hget]
  have hdecomp : occurrences =
      before ++ ConcreteElaboration.LocalOccurrence.child selected :: after := by
    rw [← List.take_append_drop position.val occurrences, hdrop]
  have hnodup := ConcreteElaboration.localOccurrences_nodup input parent
  change occurrences.Nodup at hnodup
  rw [hdecomp] at hnodup
  have hparts := List.nodup_append.mp hnodup
  have hfocusParts := List.nodup_cons.mp hparts.2.1
  have hawayBefore :
      ConcreteElaboration.LocalOccurrence.child selected ∉ before := by
    intro hmem
    exact (hparts.2.2 _ hmem _ (by simp)) rfl
  have hawayAfter :
      ConcreteElaboration.LocalOccurrence.child selected ∉ after := by
    exact hfocusParts.1
  exact ⟨before, after, hdecomp, hawayBefore, hawayAfter⟩

/-- Compilation of a prefix or suffix disjoint from the route's focused child
is entirely unaffected by spawn.  Node occurrences commute directly; child
occurrences are side branches by well-founded sibling disjointness. -/
theorem spawnNodeRaw_compileOccurrencesAway
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope parent selected : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (hparent : (input.regions selected).parent? = some parent)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input selected scope rest)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend parent).Exact parent)
    (htargetExact : (target.extend parent).Exact parent)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input parent)
    (haway : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        (target.extend parent) binders
        (occurrences.map (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        (source.extend parent) binders occurrences).map
          (ItemSeq.renameWires (embedding.extend parent).index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    (source.extend parent) (target.extend parent) (embedding.extend parent)
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    binders occurrence htargetExact.nodup
    htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hchildParent :=
    (ConcreteElaboration.mem_localOccurrences_child input parent child).mp
      (hlocal (.child child) hmem)
  have hchildNe : child ≠ selected := by
    intro heq
    subst child
    exact haway hmem
  have hselectedScope := regionRoute_encloses input hinput tail
  have hchildNotAbove := checked_sibling_not_encloses_descendant input hinput
    hparent hchildParent hselectedScope hchildNe
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses input node scope
    portCount port hinput htarget hnode fuel child (source.extend parent)
    (target.extend parent) (embedding.extend parent) childBinders
    hchildNotAbove (hsourceExact.extend_child hinput hchildParent)
    (htargetExact.extend_child htarget hchildParent)

/-- Root-sheet analogue of `spawnNodeRaw_compileOccurrencesAway`.  The open
compiler supplies its complete root context directly rather than extending an
inherited context at the sheet. -/
theorem spawnNodeRaw_compileRootOccurrencesAway
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope selected : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (hparent : (input.regions selected).parent? = some input.root)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input selected scope rest)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (hsourceExact : source.Exact input.root)
    (htargetExact : target.Exact input.root)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input input.root)
    (haway : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        target ConcreteElaboration.BinderContext.empty
        (occurrences.map (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        source ConcreteElaboration.BinderContext.empty occurrences).map
          (ItemSeq.renameWires embedding.index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    source target embedding
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    ConcreteElaboration.BinderContext.empty occurrence htargetExact.nodup
    htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hchildParent :=
    (ConcreteElaboration.mem_localOccurrences_child input input.root child).mp
      (hlocal (.child child) hmem)
  have hchildNe : child ≠ selected := by
    intro heq
    subst child
    exact haway hmem
  have hselectedScope := regionRoute_encloses input hinput tail
  have hchildNotAbove := checked_sibling_not_encloses_descendant input hinput
    hparent hchildParent hselectedScope hchildNe
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses input node scope
    portCount port hinput htarget hnode fuel child source target embedding
    childBinders hchildNotAbove
    (hsourceExact.extend_child hinput hchildParent)
    (htargetExact.extend_child htarget hchildParent)

/-- In a positional old-wire context, unaffected regions compile to the source
body transported only across the propositionally equal wire carrier. -/
theorem spawnNodeRaw_compileRegion?_positional_unaffected
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (fuel : Nat) (region : Fin input.regionCount)
    (source : ConcreteElaboration.WireContext input)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hnotAbove : ¬ input.Encloses region scope)
    (hsourceExact : (source.extend region).Exact region)
    (htargetExact :
      (ConcreteElaboration.WireContext.extend
        (d := spawnNodeRaw input node scope portCount port)
        (SpawnContextEmbedding.mapOldContext input portCount source)
        region).Exact region) :
    ConcreteElaboration.compileRegion? signature
        (spawnNodeRaw input node scope portCount port) fuel region
        (SpawnContextEmbedding.mapOldContext input portCount source) binders =
      (ConcreteElaboration.compileRegion? signature input fuel region source
        binders).map
          (Region.castWiresEq
            (SpawnContextEmbedding.mapOldContext_length input portCount
              source).symm) := by
  have h := spawnNodeRaw_compileRegion?_old_of_not_encloses input node scope
    portCount port hinput htarget hnode fuel region source
    (SpawnContextEmbedding.mapOldContext input portCount source)
    (SpawnContextEmbedding.positional input node scope portCount port source)
    binders hnotAbove hsourceExact htargetExact
  have hwire :
      (SpawnContextEmbedding.positional input node scope portCount port
        source).index =
      Fin.cast (SpawnContextEmbedding.mapOldContext_length input portCount
        source).symm := by
    rfl
  rw [hwire] at h
  cases hsource : ConcreteElaboration.compileRegion? signature input fuel
      region source binders with
  | none => simpa [hsource] using h
  | some body =>
      simp only [hsource, Option.map_some] at h ⊢
      rw [Region.castWiresEq_eq_renameWires]
      exact h

/-- At the spawn scope, compiling all pre-existing occurrences commutes with
the non-surjective lexical embedding.  Direct child regions use the strict-
descendant compiler theorem; the fresh node is deliberately absent here. -/
theorem spawnNodeRaw_compileOldOccurrencesAtSite
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsource : (source.extend scope).Exact scope)
    (htargetExact : (target.extend scope).Exact scope) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        (target.extend scope) binders
        ((ConcreteElaboration.localOccurrences input scope).map
          (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        (source.extend scope) binders
        (ConcreteElaboration.localOccurrences input scope)).map
          (ItemSeq.renameWires (embedding.extend scope).index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    (source.extend scope) (target.extend scope) (embedding.extend scope)
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    binders occurrence htargetExact.nodup htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hparent :=
    (ConcreteElaboration.mem_localOccurrences_child input scope child).mp hmem
  have hchildNotAbove : ¬ input.Encloses child scope :=
    ConcreteElaboration.checked_direct_child_not_encloses_parent hinput hparent
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses input node scope
    portCount port
    hinput htarget hnode fuel child (source.extend scope)
    (target.extend scope) (embedding.extend scope) childBinders hchildNotAbove
    (hsource.extend_child hinput hparent)
    (htargetExact.extend_child htarget hparent)

/-- At the appended node's actual region, all old occurrences compile through
the old-wire embedding even when the fresh wire was introduced at an ancestor
scope. -/
theorem spawnNodeRaw_compileOldOccurrencesAtNodeSite
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (scopeEnclosesNode : input.Encloses scope node.region)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsource : (source.extend node.region).Exact node.region)
    (htargetExact : (target.extend node.region).Exact node.region) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        (target.extend node.region) binders
        ((ConcreteElaboration.localOccurrences input node.region).map
          (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        (source.extend node.region) binders
        (ConcreteElaboration.localOccurrences input node.region)).map
          (ItemSeq.renameWires (embedding.extend node.region).index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    (source.extend node.region) (target.extend node.region)
    (embedding.extend node.region)
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    binders occurrence htargetExact.nodup htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hparent :=
    (ConcreteElaboration.mem_localOccurrences_child input node.region child).mp
      hmem
  have hchildNotAbove : ¬ input.Encloses child node.region :=
    ConcreteElaboration.checked_direct_child_not_encloses_parent hinput hparent
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses_node input node scope
    portCount port hinput htarget scopeEnclosesNode fuel child
    (source.extend node.region) (target.extend node.region)
    (embedding.extend node.region) childBinders hchildNotAbove
    (hsource.extend_child hinput hparent)
    (htargetExact.extend_child htarget hparent)

/-- A prefix or suffix away from the focused routed child compiles unchanged
when the appended node lies below a distinct wire-introduction scope. -/
theorem spawnNodeRaw_compileOccurrencesAwayFromNode
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope parent selected : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (scopeEnclosesNode : input.Encloses scope node.region)
    (hparent : (input.regions selected).parent? = some parent)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input selected node.region rest)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend parent).Exact parent)
    (htargetExact : (target.extend parent).Exact parent)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input parent)
    (haway : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        (target.extend parent) binders
        (occurrences.map (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        (source.extend parent) binders occurrences).map
          (ItemSeq.renameWires (embedding.extend parent).index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    (source.extend parent) (target.extend parent) (embedding.extend parent)
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    binders occurrence htargetExact.nodup
    htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hchildParent :=
    (ConcreteElaboration.mem_localOccurrences_child input parent child).mp
      (hlocal (.child child) hmem)
  have hchildNe : child ≠ selected := by
    intro equality
    subst child
    exact haway hmem
  have hselectedNode := regionRoute_encloses input hinput tail
  have hchildNotAbove := checked_sibling_not_encloses_descendant input hinput
    hparent hchildParent hselectedNode hchildNe
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses_node input node scope
    portCount port hinput htarget scopeEnclosesNode fuel child
    (source.extend parent) (target.extend parent) (embedding.extend parent)
    childBinders hchildNotAbove
    (hsourceExact.extend_child hinput hchildParent)
    (htargetExact.extend_child htarget hchildParent)

/-- Open-root analogue of `spawnNodeRaw_compileOccurrencesAwayFromNode`. -/
theorem spawnNodeRaw_compileRootOccurrencesAwayFromNode
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope selected : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (scopeEnclosesNode : input.Encloses scope node.region)
    (hparent : (input.regions selected).parent? = some input.root)
    {rest : List Nat}
    (tail : Diagram.Splice.RegionRoute input selected node.region rest)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (hsourceExact : source.Exact input.root)
    (htargetExact : target.Exact input.root)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input input.root)
    (haway : ConcreteElaboration.LocalOccurrence.child selected ∉ occurrences) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        target ConcreteElaboration.BinderContext.empty
        (occurrences.map (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        source ConcreteElaboration.BinderContext.empty occurrences).map
          (ItemSeq.renameWires embedding.index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    source target embedding
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    ConcreteElaboration.BinderContext.empty occurrence htargetExact.nodup
    htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hchildParent :=
    (ConcreteElaboration.mem_localOccurrences_child input input.root child).mp
      (hlocal (.child child) hmem)
  have hchildNe : child ≠ selected := by
    intro equality
    subst child
    exact haway hmem
  have hselectedNode := regionRoute_encloses input hinput tail
  have hchildNotAbove := checked_sibling_not_encloses_descendant input hinput
    hparent hchildParent hselectedNode hchildNe
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses_node input node scope
    portCount port hinput htarget scopeEnclosesNode fuel child source target
    embedding childBinders hchildNotAbove
    (hsourceExact.extend_child hinput hchildParent)
    (htargetExact.extend_child htarget hchildParent)

/-- At a root spawn, all pre-existing direct occurrences compile through the
old root-wire prefix.  Direct children are handled by the strict-descendant
compiler theorem; the fresh node is intentionally excluded. -/
theorem spawnNodeRaw_compileOldOccurrencesAtRoot
    (input : ConcreteDiagram) (node : CNode input.regionCount)
    (scope : Fin input.regionCount) (portCount : Nat)
    (port : Fin portCount → CPort)
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input node scope portCount port).WellFormed signature)
    (hnode : node.region = scope)
    (hroot : input.root = scope)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input node scope portCount port))
    (embedding : SpawnContextEmbedding input node scope portCount port
      source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsource : source.Exact input.root)
    (htargetExact : target.Exact input.root) :
    ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input node scope portCount port)
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input node scope portCount port) fuel)
        target binders
        ((ConcreteElaboration.localOccurrences input input.root).map
          (spawnNodeRaw_oldOccurrence input)) =
      (ConcreteElaboration.compileOccurrencesWith? signature input
        (ConcreteElaboration.compileRegion? signature input fuel)
        source binders
        (ConcreteElaboration.localOccurrences input input.root)).map
          (ItemSeq.renameWires embedding.index) := by
  apply ConcreteElaboration.compileOccurrencesWith?_map
  intro occurrence hmem
  apply spawnNodeRaw_compileOccurrenceWith?_old input node scope portCount port
    source target embedding
    (ConcreteElaboration.compileRegion? signature input fuel)
    (ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input node scope portCount port) fuel)
    binders occurrence htargetExact.nodup htarget.wire_endpoints_are_disjoint
  intro childRels child childBinders heq
  subst occurrence
  have hparent :=
    (ConcreteElaboration.mem_localOccurrences_child input input.root child).mp
      hmem
  have hchildNotAbove : ¬ input.Encloses child scope := by
    rw [← hroot]
    exact ConcreteElaboration.checked_direct_child_not_encloses_parent hinput
      hparent
  exact spawnNodeRaw_compileRegion?_old_of_not_encloses input node scope
    portCount port hinput htarget hnode fuel child source target embedding
    childBinders hchildNotAbove
    (hsource.extend_child hinput hparent)
    (htargetExact.extend_child htarget hparent)

end VisualProof.Rule
