import VisualProof.Concrete.Subgraph.Splice.AliasMaterialization

namespace VisualProof.Concrete.Splice

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AttachmentAliasMaterialization

variable {Host : Type} [DecidableEq Host]

/-- The semantic identity of an open-boundary incidence is its intrinsic
pattern wire together with the host wire selected for that incidence. -/
abbrev Key (pattern : OpenDiagram) :=
  Fin pattern.diagram.wireCount × Host

def key (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) : Key (Host := Host) pattern :=
  (pattern.boundary.get position, attachment position)

def keys (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    List (Key (Host := Host) pattern) :=
  List.ofFn (key pattern attachment)

omit [DecidableEq Host] in
@[simp] theorem keys_length (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    (keys pattern attachment).length = pattern.boundary.length := by
  simp [keys]

omit [DecidableEq Host] in
@[simp] theorem keys_get (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin (keys pattern attachment).length) :
    (keys pattern attachment).get position =
      key pattern attachment ⟨position.val, by simpa using position.isLt⟩ := by
  simp [keys]

/-- The first ordered occurrence of the same `(intrinsic, host)` key. -/
def pairOrigin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) : Fin pattern.boundary.length :=
  let found := indexOf? (keys pattern attachment) (key pattern attachment position)
  have present : found.isSome = true := by
    change (indexOf? (keys pattern attachment)
      (key pattern attachment position)).isSome = true
    rw [indexOf?_isSome_iff]
    exact List.mem_ofFn.mpr ⟨position, rfl⟩
  ⟨(found.get present).val, by
    simpa [found] using (found.get present).isLt⟩

/-- The first ordered occurrence of the intrinsic pattern wire, ignoring its
host attachment. -/
def wireOrigin (pattern : OpenDiagram)
    (position : Fin pattern.boundary.length) : Fin pattern.boundary.length :=
  let found := indexOf? pattern.boundary (pattern.boundary.get position)
  have present : found.isSome = true := by
    rw [indexOf?_isSome_iff]
    exact List.get_mem pattern.boundary position
  found.get present

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

theorem pairOrigin_key (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    key pattern attachment (pairOrigin pattern attachment position) =
      key pattern attachment position := by
  unfold pairOrigin
  dsimp only
  let found := indexOf? (keys pattern attachment) (key pattern attachment position)
  have present : found.isSome = true := by
    change (indexOf? (keys pattern attachment)
      (key pattern attachment position)).isSome = true
    rw [indexOf?_isSome_iff]
    exact List.mem_ofFn.mpr ⟨position, rfl⟩
  have hsome : found = some (found.get present) := by
    exact Option.some_get present |>.symm
  have hs := indexOf?_sound hsome
  simpa [found, keys] using hs

theorem wireOrigin_wire (pattern : OpenDiagram)
    (position : Fin pattern.boundary.length) :
    pattern.boundary.get (wireOrigin pattern position) =
      pattern.boundary.get position := by
  unfold wireOrigin
  dsimp only
  let found := indexOf? pattern.boundary (pattern.boundary.get position)
  have present : found.isSome = true := by
    rw [indexOf?_isSome_iff]
    exact List.get_mem pattern.boundary position
  have hsome : found = some (found.get present) := by
    exact Option.some_get present |>.symm
  exact indexOf?_sound hsome

theorem pairOrigin_minimal (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position prior : Fin pattern.boundary.length)
    (hprior : prior.val < (pairOrigin pattern attachment position).val) :
    key pattern attachment prior ≠ key pattern attachment position := by
  unfold pairOrigin at hprior
  dsimp only at hprior ⊢
  let found := indexOf? (keys pattern attachment) (key pattern attachment position)
  have present : found.isSome = true := by
    change (indexOf? (keys pattern attachment)
      (key pattern attachment position)).isSome = true
    rw [indexOf?_isSome_iff]
    exact List.mem_ofFn.mpr ⟨position, rfl⟩
  have hindex : indexOf? (keys pattern attachment)
      (key pattern attachment position) = some (found.get present) :=
    Option.some_get present |>.symm
  have hminimal := indexOf?_minimal hindex
    ⟨prior.val, by simp [prior.isLt]⟩ (by simpa [found] using hprior)
  simpa [keys] using hminimal

theorem wireOrigin_minimal (pattern : OpenDiagram)
    (position prior : Fin pattern.boundary.length)
    (hprior : prior.val < (wireOrigin pattern position).val) :
    pattern.boundary.get prior ≠ pattern.boundary.get position := by
  unfold wireOrigin at hprior
  dsimp only at hprior ⊢
  let found := indexOf? pattern.boundary (pattern.boundary.get position)
  have present : found.isSome = true := by
    rw [indexOf?_isSome_iff]
    exact List.get_mem pattern.boundary position
  have hsome : found = some (found.get present) := by
    exact Option.some_get present |>.symm
  exact indexOf?_minimal hsome prior hprior

theorem pairOrigin_eq_iff (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (left right : Fin pattern.boundary.length) :
    pairOrigin pattern attachment left = pairOrigin pattern attachment right ↔
      key pattern attachment left = key pattern attachment right := by
  constructor
  · intro originsEqual
    rw [← pairOrigin_key pattern attachment left,
      ← pairOrigin_key pattern attachment right, originsEqual]
  · intro keysEqual
    unfold pairOrigin
    simp only [keysEqual]

theorem wireOrigin_eq_iff (pattern : OpenDiagram)
    (left right : Fin pattern.boundary.length) :
    wireOrigin pattern left = wireOrigin pattern right ↔
      pattern.boundary.get left = pattern.boundary.get right := by
  constructor
  · intro originsEqual
    rw [← wireOrigin_wire pattern left, ← wireOrigin_wire pattern right,
      originsEqual]
  · intro wiresEqual
    unfold wireOrigin
    simp only [wiresEqual]

theorem wireOrigin_pairOrigin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    wireOrigin pattern (pairOrigin pattern attachment position) =
      wireOrigin pattern position := by
  rw [wireOrigin_eq_iff]
  exact congrArg Prod.fst (pairOrigin_key pattern attachment position)

theorem pairOrigin_idem (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    pairOrigin pattern attachment (pairOrigin pattern attachment position) =
      pairOrigin pattern attachment position := by
  rw [pairOrigin_eq_iff]
  exact pairOrigin_key pattern attachment position

/-- A later distinct host attachment for an already-seen intrinsic wire. -/
def IsAliasOrigin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) : Prop :=
  pairOrigin pattern attachment position = position ∧
    wireOrigin pattern position ≠ position

instance (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    Decidable (IsAliasOrigin pattern attachment position) := by
  unfold IsAliasOrigin
  infer_instance

def aliasOrigins (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    List (Fin pattern.boundary.length) :=
  (allFin pattern.boundary.length).filter fun position =>
    decide (IsAliasOrigin pattern attachment position)

@[simp] theorem mem_aliasOrigins (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    position ∈ aliasOrigins pattern attachment ↔
      IsAliasOrigin pattern attachment position := by
  simp [aliasOrigins]

theorem aliasOrigins_nodup (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    (aliasOrigins pattern attachment).Nodup := by
  exact List.Sublist.nodup List.filter_sublist
    (allFin_nodup pattern.boundary.length)

def aliasCount (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host) : Nat :=
  (aliasOrigins pattern attachment).length

theorem pairOrigin_mem_aliasOrigins_iff (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    pairOrigin pattern attachment position ∈ aliasOrigins pattern attachment ↔
      pairOrigin pattern attachment position ≠ wireOrigin pattern position := by
  rw [mem_aliasOrigins]
  constructor
  · rintro ⟨_, hne⟩
    intro heq
    exact hne (by
      rw [wireOrigin_pairOrigin pattern attachment position]
      exact heq.symm)
  · intro hne
    exact ⟨pairOrigin_idem pattern attachment position,
      by
        intro heq
        exact hne (by
          rw [wireOrigin_pairOrigin pattern attachment position] at heq
          exact heq.symm)⟩

def aliasIndex? (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    Option (Fin (aliasCount pattern attachment)) :=
  indexOf? (aliasOrigins pattern attachment)
    (pairOrigin pattern attachment position)

@[simp] theorem aliasIndex?_isSome_iff (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    (aliasIndex? pattern attachment position).isSome = true ↔
      pairOrigin pattern attachment position ≠ wireOrigin pattern position := by
  rw [← pairOrigin_mem_aliasOrigins_iff]
  exact indexOf?_isSome_iff

def aliasNode (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    Fin (pattern.diagram.nodeCount + aliasCount pattern attachment) :=
  Fin.natAdd pattern.diagram.nodeCount aliasIndex

def aliasWire (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    Fin (pattern.diagram.wireCount + aliasCount pattern attachment) :=
  Fin.natAdd pattern.diagram.wireCount aliasIndex

def liftOldNode (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (node : Fin pattern.diagram.nodeCount) :
    Fin (pattern.diagram.nodeCount + aliasCount pattern attachment) :=
  Fin.castAdd (aliasCount pattern attachment) node

def liftOldWire (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (wire : Fin pattern.diagram.wireCount) :
    Fin (pattern.diagram.wireCount + aliasCount pattern attachment) :=
  Fin.castAdd (aliasCount pattern attachment) wire

def liftOldEndpoint (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (endpoint : CEndpoint pattern.diagram.nodeCount) :
    CEndpoint (pattern.diagram.nodeCount + aliasCount pattern attachment) := {
  node := liftOldNode pattern attachment endpoint.node
  port := endpoint.port
}

def aliasOrigin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    Fin pattern.boundary.length :=
  (aliasOrigins pattern attachment).get aliasIndex

/-- Every alias equation is attached to the lifted original intrinsic stub.
The fresh stub is its sole input. -/
def aliasOutputs (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (wire : Fin pattern.diagram.wireCount) :
    List (CEndpoint (pattern.diagram.nodeCount + aliasCount pattern attachment)) :=
  (allFin (aliasCount pattern attachment)).filterMap fun aliasIndex =>
    if pattern.boundary.get (aliasOrigin pattern attachment aliasIndex) = wire then
      some { node := aliasNode pattern attachment aliasIndex, port := .arg 0 }
    else
      none

def materializedDiagram (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) : Diagram where
  regionCount := pattern.diagram.regionCount
  nodeCount := pattern.diagram.nodeCount + aliasCount pattern attachment
  wireCount := pattern.diagram.wireCount + aliasCount pattern attachment
  root := pattern.diagram.root
  regions := pattern.diagram.regions
  nodes := Fin.addCases pattern.diagram.nodes fun _ =>
    .identity bodyContainer 2
  wires := Fin.addCases
    (fun wire => {
      scope := (pattern.diagram.wires wire).scope
      endpoints :=
        (pattern.diagram.wires wire).endpoints.map
          (liftOldEndpoint pattern attachment) ++
          aliasOutputs pattern attachment wire
    })

    (fun aliasIndex => {
      scope := pattern.diagram.root
      endpoints := [{
        node := aliasNode pattern attachment aliasIndex
        port := .arg 1
      }]
    })

@[simp] theorem materialized_regionCount (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    (materializedDiagram pattern attachment bodyContainer).regionCount =
      pattern.diagram.regionCount := rfl

@[simp] theorem materialized_regions (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (region : Fin pattern.diagram.regionCount) :
    (materializedDiagram pattern attachment bodyContainer).regions region =
      pattern.diagram.regions region := rfl

@[simp] theorem materialized_old_node (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (node : Fin pattern.diagram.nodeCount) :
    (materializedDiagram pattern attachment bodyContainer).nodes
        (liftOldNode pattern attachment node) = pattern.diagram.nodes node := by
  simp [materializedDiagram, liftOldNode]

@[simp] theorem materialized_old_wire_scope (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin pattern.diagram.wireCount) :
    ((materializedDiagram pattern attachment bodyContainer).wires
      (liftOldWire pattern attachment wire)).scope =
        (pattern.diagram.wires wire).scope := by
  simp [materializedDiagram, liftOldWire]

@[simp] theorem materialized_old_wire_endpoints (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin pattern.diagram.wireCount) :
    ((materializedDiagram pattern attachment bodyContainer).wires
      (liftOldWire pattern attachment wire)).endpoints =
        (pattern.diagram.wires wire).endpoints.map
            (liftOldEndpoint pattern attachment) ++
          aliasOutputs pattern attachment wire := by
  simp [materializedDiagram, liftOldWire]

/-- Ordered boundary normalization. Equal exact keys deliberately reuse their
stub; distinct attachments of one intrinsic wire receive distinct fresh stubs. -/
def rawBoundaryWire (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    Fin (pattern.diagram.wireCount + aliasCount pattern attachment) :=
  match aliasIndex? pattern attachment position with
  | some aliasIndex => aliasWire pattern attachment aliasIndex
  | none => liftOldWire pattern attachment (pattern.boundary.get position)

def raw (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) : OpenDiagram where
  diagram := materializedDiagram pattern attachment bodyContainer
  boundary := List.ofFn (rawBoundaryWire pattern attachment)

@[simp] theorem raw_boundary_length (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    (raw pattern attachment bodyContainer).boundary.length =
      pattern.boundary.length := by
  simp [raw]

@[simp] theorem raw_nodeCount (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    (raw pattern attachment bodyContainer).diagram.nodeCount =
      pattern.diagram.nodeCount + aliasCount pattern attachment := rfl

@[simp] theorem raw_wireCount (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    (raw pattern attachment bodyContainer).diagram.wireCount =
      pattern.diagram.wireCount + aliasCount pattern attachment := rfl

theorem aliasIndex?_sound (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    {position : Fin pattern.boundary.length}
    {aliasIndex : Fin (aliasCount pattern attachment)}
    (hindex : aliasIndex? pattern attachment position = some aliasIndex) :
    aliasOrigin pattern attachment aliasIndex =
      pairOrigin pattern attachment position := by
  exact indexOf?_sound hindex

theorem aliasIndex?_none_origin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    {position : Fin pattern.boundary.length}
    (hindex : aliasIndex? pattern attachment position = none) :
    pairOrigin pattern attachment position = wireOrigin pattern position := by
  by_cases heq : pairOrigin pattern attachment position = wireOrigin pattern position
  · exact heq
  · have hsome := (aliasIndex?_isSome_iff pattern attachment position).2 heq
    simp [hindex] at hsome

theorem rawBoundaryWire_eq_of_key_eq (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    {left right : Fin pattern.boundary.length}
    (hkey : key pattern attachment left = key pattern attachment right) :
    rawBoundaryWire pattern attachment left =
      rawBoundaryWire pattern attachment right := by
  have horigin := (pairOrigin_eq_iff pattern attachment left right).2 hkey
  have hwire := congrArg Prod.fst hkey
  change pattern.boundary.get left = pattern.boundary.get right at hwire
  have hindex : aliasIndex? pattern attachment left =
      aliasIndex? pattern attachment right := by
    simp [aliasIndex?, horigin]
  unfold rawBoundaryWire
  rw [hindex]
  cases aliasIndex? pattern attachment right with
  | none => exact congrArg (liftOldWire pattern attachment) hwire
  | some aliasIndex => rfl

theorem key_eq_of_rawBoundaryWire_eq (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    {left right : Fin pattern.boundary.length}
    (hraw : rawBoundaryWire pattern attachment left =
      rawBoundaryWire pattern attachment right) :
    key pattern attachment left = key pattern attachment right := by
  cases hleft : aliasIndex? pattern attachment left with
  | none =>
      cases hright : aliasIndex? pattern attachment right with
      | none =>
          simp only [rawBoundaryWire, hleft, hright] at hraw
          have hwires : pattern.boundary.get left =
              pattern.boundary.get right := by
            apply Fin.ext
            simpa [liftOldWire] using congrArg Fin.val hraw
          have origins : pairOrigin pattern attachment left =
              pairOrigin pattern attachment right := by
            rw [aliasIndex?_none_origin pattern attachment hleft,
              aliasIndex?_none_origin pattern attachment hright,
              (wireOrigin_eq_iff pattern left right).2 hwires]
          exact (pairOrigin_eq_iff pattern attachment left right).1 origins
      | some rightAlias =>
          simp only [rawBoundaryWire, hleft, hright] at hraw
          have impossible := congrArg Fin.val hraw
          have oldBound := (pattern.boundary.get left).isLt
          exfalso
          simp [liftOldWire, aliasWire] at impossible
          omega
  | some leftAlias =>
      cases hright : aliasIndex? pattern attachment right with
      | none =>
          simp only [rawBoundaryWire, hleft, hright] at hraw
          have impossible := congrArg Fin.val hraw
          have oldBound := (pattern.boundary.get right).isLt
          exfalso
          simp [liftOldWire, aliasWire] at impossible
          omega
      | some rightAlias =>
          simp only [rawBoundaryWire, hleft, hright] at hraw
          have aliasesEqual : leftAlias = rightAlias := by
            apply Fin.ext
            simpa [aliasWire] using congrArg Fin.val hraw
          subst rightAlias
          have origins : pairOrigin pattern attachment left =
              pairOrigin pattern attachment right :=
            (aliasIndex?_sound pattern attachment hleft).symm.trans
              (aliasIndex?_sound pattern attachment hright)
          exact (pairOrigin_eq_iff pattern attachment left right).1 origins

/-- The core representation theorem used by executors and soundness proofs. -/
theorem rawBoundaryWire_eq_iff (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (left right : Fin pattern.boundary.length) :
    rawBoundaryWire pattern attachment left =
        rawBoundaryWire pattern attachment right ↔
      pattern.boundary.get left = pattern.boundary.get right ∧
        attachment left = attachment right := by
  constructor
  · intro hraw
    have hkey := key_eq_of_rawBoundaryWire_eq pattern attachment hraw
    exact ⟨congrArg Prod.fst hkey, congrArg Prod.snd hkey⟩
  · rintro ⟨hwire, hattachment⟩
    apply rawBoundaryWire_eq_of_key_eq pattern attachment
    exact Prod.ext hwire hattachment

theorem raw_boundary_get_eq_iff (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (left right : Fin pattern.boundary.length) :
    (raw pattern attachment bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern attachment bodyContainer).symm left) =
        (raw pattern attachment bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern attachment bodyContainer).symm right) ↔
      pattern.boundary.get left = pattern.boundary.get right ∧
        attachment left = attachment right := by
  simpa [raw] using rawBoundaryWire_eq_iff pattern attachment left right

theorem pairOrigin_le (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    (pairOrigin pattern attachment position).val ≤ position.val := by
  by_cases hle : (pairOrigin pattern attachment position).val ≤ position.val
  · exact hle
  · have hlt : position.val < (pairOrigin pattern attachment position).val := by
      omega
    exact (pairOrigin_minimal pattern attachment position position hlt rfl).elim

theorem wireOrigin_le (pattern : OpenDiagram)
    (position : Fin pattern.boundary.length) :
    (wireOrigin pattern position).val ≤ position.val := by
  by_cases hle : (wireOrigin pattern position).val ≤ position.val
  · exact hle
  · have hlt : position.val < (wireOrigin pattern position).val := by omega
    exact (wireOrigin_minimal pattern position position hlt rfl).elim

theorem wireOrigin_idem (pattern : OpenDiagram)
    (position : Fin pattern.boundary.length) :
    wireOrigin pattern (wireOrigin pattern position) = wireOrigin pattern position := by
  rw [wireOrigin_eq_iff]
  exact wireOrigin_wire pattern position

theorem pairOrigin_wireOrigin (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (position : Fin pattern.boundary.length) :
    pairOrigin pattern attachment (wireOrigin pattern position) =
      wireOrigin pattern position := by
  let first := wireOrigin pattern position
  have hle := pairOrigin_le pattern attachment first
  apply Fin.ext
  by_cases heq : (pairOrigin pattern attachment first).val = first.val
  · exact heq
  · have hlt : (pairOrigin pattern attachment first).val < first.val := by omega
    have sameWire : pattern.boundary.get
        (pairOrigin pattern attachment first) = pattern.boundary.get first :=
      congrArg Prod.fst (pairOrigin_key pattern attachment first)
    exact (wireOrigin_minimal pattern first
      (pairOrigin pattern attachment first)
      (by simpa [first, wireOrigin_idem] using hlt)
      (by simpa [first, wireOrigin_idem] using sameWire)).elim

theorem liftOldWire_mem_raw_boundary (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (wire : Fin pattern.diagram.wireCount) (hwire : wire ∈ pattern.boundary) :
    liftOldWire pattern attachment wire ∈
      (raw pattern attachment bodyContainer).boundary := by
  obtain ⟨position, hposition⟩ := indexOf?_complete hwire
  let first := wireOrigin pattern position
  have hfirstWire : pattern.boundary.get first = wire := by
    exact (wireOrigin_wire pattern position).trans (indexOf?_sound hposition)
  have hpair : pairOrigin pattern attachment first = first := by
    exact pairOrigin_wireOrigin pattern attachment position
  have hwireOrigin : wireOrigin pattern first = first := by
    exact wireOrigin_idem pattern position
  have hnone : aliasIndex? pattern attachment first = none := by
    cases hindex : aliasIndex? pattern attachment first with
    | none => rfl
    | some aliasIndex =>
        have hsome : (aliasIndex? pattern attachment first).isSome = true := by
          simp [hindex]
        have hne := (aliasIndex?_isSome_iff pattern attachment first).1 hsome
        exact (hne (hpair.trans hwireOrigin.symm)).elim
  change liftOldWire pattern attachment wire ∈ List.ofFn
    (rawBoundaryWire pattern attachment)
  rw [List.mem_ofFn]
  refine ⟨first, ?_⟩
  simp only [rawBoundaryWire, hnone]
  exact congrArg (liftOldWire pattern attachment) hfirstWire

theorem aliasWire_mem_raw_boundary (pattern : OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (aliasIndex : Fin (aliasCount pattern attachment)) :
    aliasWire pattern attachment aliasIndex ∈
      (raw pattern attachment bodyContainer).boundary := by
  let origin := aliasOrigin pattern attachment aliasIndex
  have horiginMem : origin ∈ aliasOrigins pattern attachment :=
    List.get_mem (aliasOrigins pattern attachment) aliasIndex
  have horigin : pairOrigin pattern attachment origin = origin :=
    (mem_aliasOrigins pattern attachment origin).1 horiginMem |>.1
  have hlookup : indexOf? (aliasOrigins pattern attachment) origin =
      some aliasIndex :=
    indexOf?_get_eq_some_of_nodup
      (aliasOrigins_nodup pattern attachment) aliasIndex
  have hindex : aliasIndex? pattern attachment origin = some aliasIndex := by
    unfold aliasIndex?
    rw [horigin]
    exact hlookup
  change aliasWire pattern attachment aliasIndex ∈ List.ofFn
    (rawBoundaryWire pattern attachment)
  rw [List.mem_ofFn]
  exact ⟨origin, by simp [rawBoundaryWire, hindex]⟩

/-- Regions are unchanged, so a source binder spine transports definitionally. -/
def binderSpine (pattern : CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram) :
    BinderSpine (raw pattern.val attachment spine.bodyContainer).diagram where
  proxyCount := spine.proxyCount
  proxy := spine.proxy
  arity := spine.arity
  bodyContainer := spine.bodyContainer
  proxy_injective := spine.proxy_injective
  proxy_ne_root := spine.proxy_ne_root
  body_eq_root_of_empty := spine.body_eq_root_of_empty
  body_eq_terminal_of_nonempty := spine.body_eq_terminal_of_nonempty
  proxy_region := spine.proxy_region

theorem terminalBody (pattern : CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val) :
    (binderSpine pattern attachment spine).TerminalBodyContract
      (raw pattern.val attachment spine.bodyContainer) where
  root_direct_child := contract.root_direct_child
  nonterminal_direct_child := contract.nonterminal_direct_child
  root_has_no_nodes := by
    intro hnonzero node
    refine Fin.addCases (motive := fun node =>
      ((raw pattern.val attachment spine.bodyContainer).diagram.nodes node).region ≠
        (raw pattern.val attachment spine.bodyContainer).diagram.root) ?_ ?_ node
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
      ((raw pattern.val attachment spine.bodyContainer).diagram.nodes node).region ≠
        (binderSpine pattern attachment spine).proxy proxyIndex) ?_ ?_ node
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
      wire ∉ (raw pattern.val attachment spine.bodyContainer).boundary →
        ((raw pattern.val attachment spine.bodyContainer).diagram.wires wire).scope ≠
          (raw pattern.val attachment spine.bodyContainer).diagram.root) ?_ ?_ wire
        hnotBoundary
    · intro old hold
      have oldNotBoundary : old ∉ pattern.val.boundary := by
        intro oldBoundary
        exact hold (liftOldWire_mem_raw_boundary pattern.val attachment
          spine.bodyContainer old oldBoundary)
      simpa [raw, materializedDiagram] using
        contract.root_has_no_nonboundary_wires hnonzero old oldNotBoundary
    · intro aliasIndex halias
      exact (halias (aliasWire_mem_raw_boundary pattern.val attachment
        spine.bodyContainer aliasIndex)).elim
  nonterminal_has_no_nonboundary_wires := by
    intro proxyIndex hnonterminal wire hnotBoundary
    refine Fin.addCases (motive := fun wire =>
      wire ∉ (raw pattern.val attachment spine.bodyContainer).boundary →
        ((raw pattern.val attachment spine.bodyContainer).diagram.wires wire).scope ≠
          (binderSpine pattern attachment spine).proxy proxyIndex) ?_ ?_ wire
        hnotBoundary
    · intro old hold
      have oldNotBoundary : old ∉ pattern.val.boundary := by
        intro oldBoundary
        exact hold (liftOldWire_mem_raw_boundary pattern.val attachment
          spine.bodyContainer old oldBoundary)
      simpa [raw, materializedDiagram, binderSpine] using
        contract.nonterminal_has_no_nonboundary_wires proxyIndex hnonterminal
          old oldNotBoundary
    · intro aliasIndex halias
      exact (halias (aliasWire_mem_raw_boundary pattern.val attachment
        spine.bodyContainer aliasIndex)).elim
  boundary_is_root_scoped := by
    intro wire hwire
    simp only [raw] at hwire
    obtain ⟨position, hposition⟩ := List.mem_ofFn.mp hwire
    cases hindex : aliasIndex? pattern.val attachment position with
    | none =>
        simp only [rawBoundaryWire, hindex] at hposition
        subst wire
        simpa [raw, materializedDiagram, liftOldWire] using
          contract.boundary_is_root_scoped
            (pattern.val.boundary.get position)
            (List.get_mem pattern.val.boundary position)
    | some aliasIndex =>
        simp only [rawBoundaryWire, hindex] at hposition
        subst wire
        simp [raw, materializedDiagram, aliasWire]

/-- Proof-bearing checked normalization, locked to the exact raw graph. -/
structure Certificate (pattern : CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram) : Type where
  wellFormed : (raw pattern.val attachment spine.bodyContainer).WellFormed
  sourceTerminalBody : spine.TerminalBodyContract pattern.val

namespace Certificate

def result {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine) :
    CheckedOpen  :=
  ⟨raw pattern.val attachment originalSpine.bodyContainer, certificate.wellFormed⟩

def spine {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (_certificate : Certificate pattern attachment originalSpine) :
    BinderSpine (raw pattern.val attachment originalSpine.bodyContainer).diagram :=
  binderSpine pattern attachment originalSpine

theorem terminalBody {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (_certificate : Certificate pattern attachment originalSpine)
    (contract : originalSpine.TerminalBodyContract pattern.val) :
    (binderSpine pattern attachment originalSpine).TerminalBodyContract
      (raw pattern.val attachment originalSpine.bodyContainer) :=
  AttachmentAliasMaterialization.terminalBody pattern attachment originalSpine
    contract

@[simp] theorem boundary_length {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine) :
    certificate.result.val.boundary.length = pattern.val.boundary.length :=
  raw_boundary_length pattern.val attachment originalSpine.bodyContainer

@[simp] theorem nodeCount {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine) :
    certificate.result.val.diagram.nodeCount =
      pattern.val.diagram.nodeCount + aliasCount pattern.val attachment := rfl

end Certificate

/-- Uses the authoritative diagram checker for exactly the graph returned by
`raw`; structural open/binder obligations are transported from the source. -/
def check (pattern : CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val) :
    Except WFError (Certificate pattern attachment spine) :=
  match hcheck : checkWellFormed
      (materializedDiagram pattern.val attachment spine.bodyContainer) with
  | .error error => .error error
  | .ok checked =>
      let diagramWellFormed :
          (materializedDiagram pattern.val attachment
            spine.bodyContainer).WellFormed  :=
        checkWellFormed_iff.mp ⟨checked, hcheck,
          checkWellFormed_preserves_input hcheck⟩
      .ok {
        wellFormed := {
          diagram_well_formed := diagramWellFormed
          boundary_is_root_scoped :=
            (terminalBody pattern attachment spine contract).boundary_is_root_scoped
        }
        sourceTerminalBody := contract
      }

theorem check_success {pattern : CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    {contract : spine.TerminalBodyContract pattern.val}
    {certificate : Certificate pattern attachment spine}
    (_hcheck : check pattern attachment spine contract = .ok certificate) :
    certificate.result.val = raw pattern.val attachment spine.bodyContainer := by
  rfl


end AttachmentAliasMaterialization

end VisualProof.Concrete.Splice
