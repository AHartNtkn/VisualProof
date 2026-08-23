import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Scope.Rename
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.WirePrimitive.Transform

open Theory
open Diagram

/-- The contexts participating in one uniform rewrite. The common context
contains exactly the retained wires. -/
structure Frame (arguments common sourceWires targetWires : List Sig) where
  sourceKeep : WireRenaming common sourceWires
  targetKeep : WireRenaming common targetWires
  selected : Var sourceWires (.rel arguments)

namespace Frame

/-- Retain the wires on either side of a replaced local binder segment. -/
def localKeep (before inserted after : List Sig) :
    WireRenaming (before ++ after) (before ++ (inserted ++ after)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (inserted ++ after))
    (fun wire => Var.appendRight before (Var.appendRight inserted wire))⟩

@[simp] theorem localKeep_cons_there
    (head : Sig) (before inserted after : List Sig)
    (wire : Var (before ++ after) signature) :
    localKeep (head :: before) inserted after (.there wire) =
      .there (localKeep before inserted after wire) := by
  apply Var.appendCases
    (motive := fun wire =>
      localKeep (head :: before) inserted after (.there wire) =
        .there (localKeep before inserted after wire))
  · intro signature retained
    calc
      localKeep (head :: before) inserted after
          (Var.there (retained.appendLeft after)) =
        (Var.there retained).appendLeft (inserted ++ after) := by
          change localKeep (head :: before) inserted after
              ((Var.there retained).appendLeft after) = _
          simp [localKeep]
      _ = Var.there (localKeep before inserted after
          (retained.appendLeft after)) := by
        simp [localKeep, Var.appendLeft]
  · intro signature trailing
    calc
      localKeep (head :: before) inserted after
          (Var.there (Var.appendRight before trailing)) =
        Var.appendRight (head :: before) (Var.appendRight inserted trailing) := by
          change localKeep (head :: before) inserted after
              (Var.appendRight (head :: before) trailing) = _
          simp [localKeep]
      _ = Var.there (localKeep before inserted after
          (Var.appendRight before trailing)) := by
        simp [localKeep, Var.appendRight]

/-- Retain the inherited context and the unaffected local binders. -/
def keep (outer before inserted after : List Sig) :
    WireRenaming (outer ++ (before ++ after))
      (outer ++ (before ++ (inserted ++ after))) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (before ++ (inserted ++ after)))
    (fun wire => Var.appendRight outer (localKeep before inserted after wire))⟩

theorem keep_index_eq_of_length_eq
    (lengthEq : firstInserted.length = secondInserted.length)
    (wire : Var (outer ++ (before ++ after)) signature) :
    (keep outer before firstInserted after wire).index.val =
      (keep outer before secondInserted after wire).index.val := by
  refine Var.appendCases (left := outer) (right := before ++ after)
    (motive := fun wire =>
      (keep outer before firstInserted after wire).index.val =
        (keep outer before secondInserted after wire).index.val) ?_ ?_ wire
  · intro inheritedSignature inherited
    simp [keep]
  · intro localSignature localWire
    refine Var.appendCases (left := before) (right := after)
      (motive := fun selected =>
        (keep outer before firstInserted after
            (Var.appendRight outer selected)).index.val =
          (keep outer before secondInserted after
            (Var.appendRight outer selected)).index.val) ?_ ?_ localWire
    · intro beforeSignature beforeWire
      simp [keep, localKeep]
    · intro afterSignature afterWire
      simp [keep, localKeep, lengthEq]

theorem keep_index_eq_iff
    (left : Var (outer ++ (before ++ after)) leftSignature)
    (right : Var (outer ++ (before ++ after)) rightSignature) :
    (keep outer before inserted after left).index.val =
        (keep outer before inserted after right).index.val ↔
      left.index.val = right.index.val := by
  apply Var.appendCases (left := outer) (right := before ++ after)
    (motive := fun left => ∀ {rightSignature}
      (right : Var (outer ++ (before ++ after)) rightSignature),
      (keep outer before inserted after left).index.val =
          (keep outer before inserted after right).index.val ↔
        left.index.val = right.index.val)
  · intro inheritedSignature inherited rightSignature right
    apply Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun right =>
        (keep outer before inserted after
            (inherited.appendLeft (before ++ after))).index.val =
            (keep outer before inserted after right).index.val ↔
          (inherited.appendLeft (before ++ after)).index.val =
            right.index.val)
    · intro otherSignature other
      simp [keep]
    · intro otherSignature other
      apply Var.appendCases (left := before) (right := after)
        (motive := fun other =>
          (keep outer before inserted after
              (inherited.appendLeft (before ++ after))).index.val =
              (keep outer before inserted after
                (Var.appendRight outer other)).index.val ↔
            (inherited.appendLeft (before ++ after)).index.val =
              (Var.appendRight outer other).index.val)
      · intro beforeSignature beforeWire
        simp [keep, localKeep]
      · intro afterSignature afterWire
        simp [keep, localKeep]
        omega
  · intro localSignature localWire rightSignature right
    apply Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun right =>
        (keep outer before inserted after
            (Var.appendRight outer localWire)).index.val =
            (keep outer before inserted after right).index.val ↔
          (Var.appendRight outer localWire).index.val = right.index.val)
    · intro inheritedSignature inherited
      apply Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          (keep outer before inserted after
              (Var.appendRight outer localWire)).index.val =
              (keep outer before inserted after
                (inherited.appendLeft (before ++ after))).index.val ↔
            (Var.appendRight outer localWire).index.val =
              (inherited.appendLeft (before ++ after)).index.val)
      · intro beforeSignature beforeWire
        simp [keep, localKeep]
      · intro afterSignature afterWire
        simp [keep, localKeep]
        omega
    · intro otherSignature other
      apply Var.appendCases (left := before) (right := after)
        (motive := fun localWire => ∀ {otherSignature}
          (other : Var (before ++ after) otherSignature),
          (keep outer before inserted after
              (Var.appendRight outer localWire)).index.val =
              (keep outer before inserted after
                (Var.appendRight outer other)).index.val ↔
            (Var.appendRight outer localWire).index.val =
              (Var.appendRight outer other).index.val) ?_ ?_ localWire other
      · intro beforeSignature beforeWire otherSignature other
        apply Var.appendCases (left := before) (right := after)
          (motive := fun other =>
            (keep outer before inserted after
                (Var.appendRight outer
                  (beforeWire.appendLeft after))).index.val =
                (keep outer before inserted after
                  (Var.appendRight outer other)).index.val ↔
              (Var.appendRight outer
                (beforeWire.appendLeft after)).index.val =
                (Var.appendRight outer other).index.val)
        · intro otherSignature other
          simp [keep, localKeep]
        · intro otherSignature other
          simp [keep, localKeep]
          omega
      · intro afterSignature afterWire otherSignature other
        apply Var.appendCases (left := before) (right := after)
          (motive := fun other =>
            (keep outer before inserted after
                (Var.appendRight outer
                  (Var.appendRight before afterWire))).index.val =
                (keep outer before inserted after
                  (Var.appendRight outer other)).index.val ↔
              (Var.appendRight outer
                (Var.appendRight before afterWire)).index.val =
                (Var.appendRight outer other).index.val)
        · intro otherSignature other
          simp [keep, localKeep]
          omega
        · intro otherSignature other
          simp [keep, localKeep]

/-- The first wire in a nonempty replacement binder segment. -/
def insertedHead (outer before after : List Sig) (signature : Sig) :
    Var (outer ++ (before ++ signature :: after)) signature :=
  Var.appendRight outer (Var.appendRight before .here)

theorem insertedHead_ne_keep
    (wire : Var (outer ++ (before ++ after)) signature) :
    (insertedHead outer before after selectedSignature).index.val ≠
      (keep outer before (selectedSignature :: inserted) after wire).index.val := by
  apply Var.appendCases (left := outer) (right := before ++ after)
    (motive := fun wire =>
      (insertedHead outer before after selectedSignature).index.val ≠
        (keep outer before (selectedSignature :: inserted) after wire).index.val)
  · intro inheritedSignature inherited
    simp [insertedHead, keep]
    omega
  · intro localSignature localWire
    apply Var.appendCases (left := before) (right := after)
      (motive := fun wire =>
        (insertedHead outer before after selectedSignature).index.val ≠
          (keep outer before (selectedSignature :: inserted) after
            (Var.appendRight outer wire)).index.val)
    · intro beforeSignature beforeWire
      simp [insertedHead, keep, localKeep]
      omega
    · intro afterSignature afterWire
      simp [insertedHead, keep, localKeep]
      have positive : 0 <
          (Var.appendRight (selectedSignature :: inserted) afterWire).index.val := by
        rw [Var.index_appendRight]
        simp
        omega
      exact Nat.ne_of_lt positive

/-- The second wire in a replacement binder segment. -/
def insertedSecond (outer before after : List Sig)
    (first second : Sig) :
    Var (outer ++ (before ++ first :: second :: after)) second :=
  Var.appendRight outer (Var.appendRight before (.there .here))

/-- The standard frame for replacing one selected relation binder. -/
def replace (outer before after targetInserted : List Sig)
    (arguments : List Sig) :
    Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ (targetInserted ++ after))) where
  sourceKeep := keep outer before [.rel arguments] after
  targetKeep := keep outer before targetInserted after
  selected := insertedHead outer before after (.rel arguments)

/-- Recursive descent preserves newly encountered local wires on both sides. -/
def append (frame : Frame arguments common sourceWires targetWires)
    (locals : List Sig) :
    Frame arguments (common ++ locals) (sourceWires ++ locals)
      (targetWires ++ locals) where
  sourceKeep := frame.sourceKeep.appendRight locals
  targetKeep := frame.targetKeep.appendRight locals
  selected := frame.selected.appendLeft locals

end Frame

namespace Values

/-- Insert a typed segment between retained prefix and suffix values. -/
def insertSegment (before : List Sig) (inserted : Values model additions) :
    Values model (before ++ after) →
      Values model (before ++ (additions ++ after)) :=
  match before with
  | [] => fun retained =>
      @Values.append model additions after inserted retained
  | _ :: rest => fun retained =>
      (retained.1, insertSegment rest inserted retained.2)

/-- Split values at an appended context boundary. -/
def splitAppend (left : List Sig) :
    Values model (left ++ right) → Values model left × Values model right :=
  match left with
  | [] => fun values => (PUnit.unit, values)
  | _ :: rest => fun values =>
      let split := splitAppend rest values.2
      ((values.1, split.1), split.2)

/-- Extract an inserted segment and the retained values around it. -/
def splitSegment (before additions after : List Sig) :
    Values model (before ++ (additions ++ after)) →
      Values model additions × Values model (before ++ after) :=
  match before with
  | [] => splitAppend additions
  | _ :: rest => fun values =>
      let split := splitSegment rest additions after values.2
      (split.1, (values.1, split.2))

theorem append_splitAppend
    (left right : List Sig) (values : Values model (left ++ right)) :
    Values.append (splitAppend left values).1 (splitAppend left values).2 =
      values := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [splitAppend, Values.append]
        rw [induction rest]

theorem splitAppend_append
    (leftValues : Values model left) (rightValues : Values model right) :
    splitAppend left (Values.append leftValues rightValues) =
      (leftValues, rightValues) := by
  induction left with
  | nil =>
      cases leftValues
      rfl
  | cons head tail induction =>
      cases leftValues with
      | mk first rest =>
        simp only [Values.append, splitAppend]
        rw [induction rest]

theorem insertSegment_splitSegment
    (before additions after : List Sig)
    (values : Values model (before ++ (additions ++ after))) :
    insertSegment before (splitSegment before additions after values).1
        (splitSegment before additions after values).2 = values := by
  induction before with
  | nil =>
      exact append_splitAppend additions after values
  | cons head tail induction =>
      cases values with
      | mk first rest =>
        simp only [splitSegment, insertSegment]
        rw [induction rest]

theorem lookup_insertSegment_keep
    (before additions after : List Sig)
    (inserted : Values model additions)
    (retained : Values model (before ++ after))
    (wire : Var (before ++ after) signature) :
    (insertSegment before inserted retained).lookup
        (Frame.localKeep before additions after wire) =
      retained.lookup wire := by
  induction before with
  | nil =>
      change (Values.append inserted retained).lookup
        (Var.appendRight additions wire) = retained.lookup wire
      exact Values.lookup_append_right inserted retained wire
  | cons head rest induction =>
      cases retained with
      | mk first tail =>
        cases wire with
        | here => rfl
        | there wire =>
            rw [Frame.localKeep_cons_there]
            exact induction tail wire

theorem lookup_insertSegment_head
    (before after : List Sig) (value : denoteSig model signature)
    (rest : Values model additions)
    (retained : Values model (before ++ after)) :
    (insertSegment (additions := signature :: additions) before
      (value, rest) retained).lookup
        (Frame.insertedHead before [] (additions ++ after) signature) =
      value := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases retained with
      | mk first remaining => exact induction remaining

theorem lookup_insertSegment_second
    (before after : List Sig)
    (firstValue : denoteSig model firstSignature)
    (secondValue : denoteSig model secondSignature)
    (rest : Values model additions)
    (retained : Values model (before ++ after)) :
    (insertSegment
      (additions := firstSignature :: secondSignature :: additions) before
      (firstValue, secondValue, rest) retained).lookup
        (Frame.insertedSecond before [] (additions ++ after)
          firstSignature secondSignature) = secondValue := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases retained with
      | mk first remaining => exact induction remaining

end Values

/-- The retained common wires have the same semantic values on both sides. -/
def EnvironmentsAgree
    (frame : Frame arguments common sourceWires targetWires)
    (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires) : Prop :=
  ∀ {signature} (wire : Var common signature),
    sourceEnv.lookup (frame.sourceKeep wire) =
      targetEnv.lookup (frame.targetKeep wire)

theorem EnvironmentsAgree.replace
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (sourceRelation : denoteSig model (.rel arguments))
    (targetInserted : Values model additions) :
    EnvironmentsAgree (Frame.replace outer before after additions arguments)
      (Values.append outerEnv
        (Values.insertSegment (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit) commonLocal))
      (Values.append outerEnv
        (Values.insertSegment before targetInserted commonLocal)) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (Values.append outerEnv
        (Values.insertSegment (additions := [.rel arguments]) before
          (sourceRelation, PUnit.unit)
          commonLocal)).lookup
          ((Frame.replace outer before after additions arguments).sourceKeep
            wire) =
      (Values.append outerEnv
        (Values.insertSegment before targetInserted commonLocal)).lookup
          ((Frame.replace outer before after additions arguments).targetKeep
            wire))
  · intro signature inherited
    simp [Frame.replace, Frame.keep]
  · intro signature localWire
    simp only [Frame.replace, Frame.keep, Var.appendMap_right,
      Values.lookup_append_right]
    rw [Values.lookup_insertSegment_keep,
      Values.lookup_insertSegment_keep]

theorem lookup_replace_selected
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (sourceRelation : denoteSig model (.rel arguments)) :
    (Values.append outerEnv
      (Values.insertSegment (additions := [.rel arguments]) before
        (sourceRelation, PUnit.unit)
        commonLocal)).lookup
        (Frame.replace outer before after additions arguments).selected =
      sourceRelation := by
  rw [show (Frame.replace outer before after additions arguments).selected =
    Var.appendRight outer
      (Frame.insertedHead before [] after (.rel arguments)) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_head (additions := []) before after
        sourceRelation (PUnit.unit : Values model []) commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

theorem lookup_replace_targetHead
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (targetValue : denoteSig model signature)
    (targetRest : Values model additions) :
      (Values.append outerEnv
        (Values.insertSegment (additions := signature :: additions) before
          (targetValue, targetRest)
        commonLocal)).lookup
        (Frame.insertedHead outer before (additions ++ after) signature) =
      targetValue := by
  rw [show Frame.insertedHead outer before (additions ++ after) signature =
    Var.appendRight outer
      (Frame.insertedHead before [] (additions ++ after) signature) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_head before after targetValue
        targetRest commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

theorem lookup_replace_targetSecond
    (outerEnv : Values model outer)
    (commonLocal : Values model (before ++ after))
    (firstValue : denoteSig model firstSignature)
    (secondValue : denoteSig model secondSignature)
    (targetRest : Values model additions) :
    (Values.append outerEnv
      (Values.insertSegment
        (additions := firstSignature :: secondSignature :: additions) before
        (firstValue, secondValue, targetRest) commonLocal)).lookup
        (Frame.insertedSecond outer before (additions ++ after)
          firstSignature secondSignature) = secondValue := by
  rw [show Frame.insertedSecond outer before (additions ++ after)
      firstSignature secondSignature =
    Var.appendRight outer (Frame.insertedSecond before []
      (additions ++ after) firstSignature secondSignature) by rfl]
  induction outer with
  | nil =>
      exact Values.lookup_insertSegment_second before after firstValue
        secondValue targetRest commonLocal
  | cons head tail induction =>
      cases outerEnv with
      | mk first rest => exact induction rest

/-- The semantically trivial unary identity used when the selected relation
wire is pinned at a transformation site. -/
def unaryPin (wire : Var wires signature) : Region wires :=
  Region.singleton (.identity signature 1 (fun _ => wire))

/-- A uniform operation supplies its target-side distinguished wires, their
lifting beneath local binders, source-side site choices, and the targets
computed from those choices. -/
structure Operation (arguments : List Sig) where
  Data : ∀ {common sourceWires targetWires},
    Frame arguments common sourceWires targetWires → Type
  appendData :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → ∀ locals, Data (frame.append locals)
  SiteData :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → Vars common arguments → Type
  site :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      (data : Data frame) → (ports : Vars common arguments) →
      SiteData frame data ports → Region targetWires
  pin :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      Data frame → Region targetWires

namespace Operation

/-- Semantic evidence for a syntactic uniform operation. Kept separate so a
rule relation contains no model-indexed premise. -/
structure Sound (operation : Operation arguments) where
  Realizes :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires),
      operation.Data frame → (model : Model) → Values model sourceWires →
        Values model targetWires → Prop
  realizes_append :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : operation.Data frame) (model : Model)
      (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires),
      Realizes frame data model sourceEnv targetEnv →
      ∀ {locals} (localEnv : Values model locals),
        Realizes (frame.append locals)
          (operation.appendData frame data locals) model
          (Values.append sourceEnv localEnv)
          (Values.append targetEnv localEnv)
  site_sound :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : operation.Data frame) (ports : Vars common arguments)
      (siteData : operation.SiteData frame data ports),
      ∀ (model : Model) (sourceEnv : Values model sourceWires)
        (targetEnv : Values model targetWires),
        EnvironmentsAgree frame sourceEnv targetEnv →
        Realizes frame data model sourceEnv targetEnv →
          (sourceEnv.lookup frame.selected
            (evaluateVars
              (ports.map fun wire => frame.sourceKeep wire) sourceEnv) ↔
          denoteRegion model targetEnv
            (operation.site frame data ports siteData))
  pin_sound :
    ∀ {common sourceWires targetWires}
      (frame : Frame arguments common sourceWires targetWires)
      (data : operation.Data frame) (model : Model)
      (targetEnv : Values model targetWires),
      denoteRegion model targetEnv (operation.pin frame data)

end Operation

mutual
  /-- Source-indexed recursive edit beneath locally bound wires. -/
  inductive RegionEdit (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      Region sourceWires → Type
    | mk
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        (itemsEdit : ItemsEdit operation (frame.append locals)
          (operation.appendData frame data locals) items) :
        RegionEdit operation frame data (.mk locals items)

  /-- Source-indexed edits for a conjunction. -/
  inductive ItemsEdit (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      ItemSeq sourceWires → Type
    | nil
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame} :
        ItemsEdit operation frame data .nil
    | cons
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        (itemEdit : ItemEdit operation frame data item)
        (tailEdit : ItemsEdit operation frame data tail) :
        ItemsEdit operation frame data (.cons item tail)

  /-- Source-indexed edit for one item. -/
  inductive ItemEdit (operation : Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      (frame : Frame arguments common sourceWires targetWires) →
      operation.Data frame →
      Item sourceWires → Type
    | atom
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemEdit operation frame data
          (.atom (frame.sourceKeep head)
            (ports.map fun wire => frame.sourceKeep wire))
    | selectedAtom
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (ports : Vars common arguments)
        (siteData : operation.SiteData frame data ports) :
        ItemEdit operation frame data
          (.atom frame.selected
            (ports.map fun wire => frame.sourceKeep wire))
    | selectedPin
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (ports : Fin 1 → Var sourceWires (.rel arguments))
        (selected : ports 0 = frame.selected) :
        ItemEdit operation frame data
          (.identity (.rel arguments) 1 ports)
    | identity
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemEdit operation frame data
          (.identity signature arity
            (fun index => frame.sourceKeep (ports index)))
    | cut
        {frame : Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {body : Region sourceWires}
        (bodyEdit : RegionEdit operation frame data body) :
        ItemEdit operation frame data (.cut body)
end

/-- A frame reflects equality of retained-wire indices on both sides and
keeps the selected source wire disjoint from every retained wire.  Unlike
`IndexedHeadInvariant`, this remains meaningful when a rule removes its
selected binder and the raw source/target contexts therefore have different
lengths. -/
structure RetainedIndexInvariant
    (frame : Frame arguments common sourceWires targetWires) : Prop where
  reflects : ∀ {leftSignature rightSignature}
    (left : Var common leftSignature) (right : Var common rightSignature),
    (frame.sourceKeep left).index.val =
        (frame.sourceKeep right).index.val ↔
      (frame.targetKeep left).index.val =
        (frame.targetKeep right).index.val
  selectedFresh : ∀ {signature} (wire : Var common signature),
    frame.selected.index.val ≠ (frame.sourceKeep wire).index.val

theorem RetainedIndexInvariant.replace
    (outer before after targetInserted arguments : List Sig) :
    RetainedIndexInvariant
      (Frame.replace outer before after targetInserted arguments) := by
  constructor
  · intro leftSignature rightSignature left right
    exact (Frame.keep_index_eq_iff
      (inserted := [.rel arguments]) left right).trans
      (Frame.keep_index_eq_iff
        (inserted := targetInserted) left right).symm
  · intro signature wire
    exact Frame.insertedHead_ne_keep
      (selectedSignature := .rel arguments) (inserted := []) wire

theorem RetainedIndexInvariant.append
    {arguments common sourceWires targetWires : List Sig}
    {frame : Frame arguments common sourceWires targetWires}
    (invariant : RetainedIndexInvariant frame) (locals : List Sig) :
    RetainedIndexInvariant (frame.append locals) := by
  constructor
  · intro leftSignature rightSignature left right
    apply Var.appendCases (left := common) (right := locals)
      (motive := fun left => ∀ {rightSignature}
        (right : Var (common ++ locals) rightSignature),
        (((frame.append locals).sourceKeep left).index.val =
            ((frame.append locals).sourceKeep right).index.val ↔
          ((frame.append locals).targetKeep left).index.val =
            ((frame.append locals).targetKeep right).index.val))
    · intro inheritedSignature inherited rightSignature right
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun right =>
          (((frame.append locals).sourceKeep
              (inherited.appendLeft locals)).index.val =
              ((frame.append locals).sourceKeep right).index.val ↔
            ((frame.append locals).targetKeep
              (inherited.appendLeft locals)).index.val =
              ((frame.append locals).targetKeep right).index.val))
      · intro otherSignature other
        simpa [Frame.append, WireRenaming.appendRight] using
          invariant.reflects inherited other
      · intro otherSignature other
        simp [Frame.append, WireRenaming.appendRight]
        omega
    · intro localSignature localWire leftRightSignature right
      apply Var.appendCases (left := common) (right := locals)
        (motive := fun right =>
          (((frame.append locals).sourceKeep
              (Var.appendRight common localWire)).index.val =
              ((frame.append locals).sourceKeep right).index.val ↔
            ((frame.append locals).targetKeep
              (Var.appendRight common localWire)).index.val =
              ((frame.append locals).targetKeep right).index.val))
      · intro inheritedSignature inherited
        simp [Frame.append, WireRenaming.appendRight]
        omega
      · intro otherSignature other
        simp [Frame.append, WireRenaming.appendRight]
  · intro signature wire
    apply Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        (frame.append locals).selected.index.val ≠
          ((frame.append locals).sourceKeep wire).index.val)
    · intro inheritedSignature inherited
      simpa [Frame.append, WireRenaming.appendRight] using
        invariant.selectedFresh inherited
    · intro localSignature localWire
      simp [Frame.append, WireRenaming.appendRight]
      omega

theorem Vars.countIndex_map_eq_of_reflection
    (variables : Vars common signatures)
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (wire : Var common wireSignature) :
    (variables.map fun selected => sourceKeep selected).countIndex
        (sourceKeep wire).index.val =
      (variables.map fun selected => targetKeep selected).countIndex
        (targetKeep wire).index.val := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex]
      by_cases sourceEq : (sourceKeep head).index.val =
          (sourceKeep wire).index.val
      · have targetEq := (reflects head wire).mp sourceEq
        simp [sourceEq, targetEq, induction]
      · have targetNe := not_congr (reflects head wire) |>.mp sourceEq
        simp [sourceEq, targetNe, induction]

mutual
  def RegionEdit.run
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {source : Region sourceWires}
      (edit : RegionEdit operation frame data source) : Region targetWires :=
    match edit with
    | .mk itemsEdit => Region.adjoinAt _ .nil itemsEdit.run

  def ItemsEdit.run
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {source : ItemSeq sourceWires}
      (edit : ItemsEdit operation frame data source) : Region targetWires :=
    match edit with
    | .nil => Region.blank targetWires
    | .cons itemEdit tailEdit => itemEdit.run.conjoin tailEdit.run

  def ItemEdit.run
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {source : Item sourceWires}
      (edit : ItemEdit operation frame data source) : Region targetWires :=
    match edit with
    | .atom head ports =>
        Region.singleton (.atom (frame.targetKeep head)
          (ports.map fun wire => frame.targetKeep wire))
    | .selectedAtom ports siteData =>
        operation.site frame data ports siteData
    | .selectedPin _ _ => operation.pin frame data
    | .identity signature arity ports =>
        Region.singleton (.identity signature arity
          (fun index => frame.targetKeep (ports index)))
    | .cut bodyEdit => Region.singleton (.cut bodyEdit.run)
end

/-- Which endpoint of a uniform edit supplies scope validity. -/
inductive ScopeDirection
  | sourceToTarget
  | targetToSource

/-- Canonicality and rooted-incidence transfer for a uniform edit whose
source and target wire contexts have the same raw indexing. -/
def ScopeTransfer (direction : ScopeDirection)
    (source : Region sourceWires) (target : Region targetWires) : Prop :=
  match direction with
  | .sourceToTarget =>
      source.Canonical →
        target.Canonical ∧
          ∀ wireIndex, wireIndex < sourceWires.length →
            (source.incidencePaths wireIndex).Sublist
              (target.incidencePaths wireIndex)
  | .targetToSource =>
      target.Canonical →
        source.Canonical ∧
          ∀ wireIndex, wireIndex < sourceWires.length →
            (target.incidencePaths wireIndex).Sublist
              (source.incidencePaths wireIndex)

/-- The raw-index invariant shared by argument-edit operations whose datum is
the replacement head wire. -/
def IndexedHeadInvariant
    (frame : Frame arguments common sourceWires targetWires)
    (head : Var targetWires targetSignature) : Prop :=
  sourceWires.length = targetWires.length ∧
    (∀ {wireSignature} (wire : Var common wireSignature),
      (frame.sourceKeep wire).index.val =
        (frame.targetKeep wire).index.val) ∧
    frame.selected.index.val = head.index.val

theorem IndexedHeadInvariant.append
    {arguments common sourceWires targetWires : List Sig}
    {targetSignature : Sig}
    {frame : Frame arguments common sourceWires targetWires}
    {head : Var targetWires targetSignature}
    (invariant : IndexedHeadInvariant frame head) (locals : List Sig) :
    IndexedHeadInvariant (frame.append locals) (head.appendLeft locals) := by
  refine ⟨by simp [invariant.1], ?_, ?_⟩
  · intro wireSignature wire
    apply Var.appendCases (left := common) (right := locals)
      (motive := fun wire =>
        ((frame.append locals).sourceKeep wire).index.val =
          ((frame.append locals).targetKeep wire).index.val)
    · intro inheritedSignature inherited
      simpa [Frame.append, WireRenaming.appendRight] using
        invariant.2.1 inherited
    · intro localSignature localWire
      simp [Frame.append, WireRenaming.appendRight, invariant.1]
  · simpa [Frame.append] using invariant.2.2

mutual
  theorem RegionEdit.scopeTransfer
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (direction : ScopeDirection)
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (contextLength : sourceWires.length = targetWires.length)
      (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
        (frame.sourceKeep wire).index.val =
          (frame.targetKeep wire).index.val)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        ScopeTransfer direction
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (selectedPinTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Fin 1 → Var siteSourceWires (.rel arguments))
        (selected : ports 0 = siteFrame.selected),
        ScopeTransfer direction
          (Region.singleton (.identity (.rel arguments) 1 ports))
          (operation.pin siteFrame siteData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires}
        {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : Region sourceWires}
      (dataInvariant : invariant frame data)
      (edit : RegionEdit operation frame data source) :
      ScopeTransfer direction source edit.run :=
    match edit with
    | @RegionEdit.mk _ _ _ _ _ _ _ locals items itemsEdit => by
        have appendedKeepIndex : ∀ {wireSignature}
            (wire : Var (common ++ locals) wireSignature),
            (((frame.append locals).sourceKeep wire).index.val) =
              (((frame.append locals).targetKeep wire).index.val) := by
          intro wireSignature wire
          apply Var.appendCases (left := common) (right := locals)
            (motive := fun wire =>
              ((frame.append locals).sourceKeep wire).index.val =
                ((frame.append locals).targetKeep wire).index.val)
          · intro inheritedSignature inherited
            simpa [Frame.append, WireRenaming.appendRight] using
              keepIndex inherited
          · intro localSignature localWire
            simp [Frame.append, WireRenaming.appendRight, contextLength]
        have child := ItemsEdit.scopeTransfer direction invariant
          appendInvariant
          (by simp [contextLength]) appendedKeepIndex selectedAtomTransfer
            selectedPinTransfer runItemsLength
            (appendInvariant frame data locals dataInvariant) itemsEdit
        cases direction with
        | targetToSource =>
            intro targetCanonical
            have materialCanonical : itemsEdit.run.Canonical :=
              Region.Canonical.material_of_adjoinAt locals .nil itemsEdit.run
                targetCanonical
            have childResult := child materialCanonical
            have sourceAdjoinedCanonical :
                (Region.adjoinAt locals .nil
                  (Region.ofItems items)).Canonical := by
              apply Region.Canonical.adjoinAt_of_material_roots locals .nil
                (Region.ofItems items) True.intro childResult.1
              intro localIndex
              let commonWire : Var (common ++ locals)
                  (locals.get localIndex) :=
                Var.appendRight common (Var.ofIndex localIndex)
              have targetRoot :=
                Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
                  itemsEdit.run targetCanonical localIndex
              have paths := childResult.2
                ((frame.append locals).targetKeep commonWire).index.val (by
                  rw [← appendedKeepIndex commonWire]
                  exact ((frame.append locals).sourceKeep commonWire).index.isLt)
              have sourceIndex :
                  ((frame.append locals).sourceKeep commonWire).index.val =
                    sourceWires.length + localIndex.val := by
                simp [commonWire, Frame.append, WireRenaming.appendRight]
              have targetIndex :
                  ((frame.append locals).targetKeep commonWire).index.val =
                    targetWires.length + localIndex.val := by
                simp [commonWire, Frame.append, WireRenaming.appendRight]
              rw [targetIndex] at paths
              rw [← contextLength] at paths
              rw [← contextLength] at targetRoot
              exact RegionPath.RootedTwo.of_sublist paths targetRoot
            refine ⟨(RegionIso.adjoinAtOfItems locals items).canonical_iff.mp
              sourceAdjoinedCanonical, ?_⟩
            intro wireIndex wireBound
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetPaths := Region.incidencePaths_adjoinAt_nil
              itemsEdit.run (targetWire.appendLeft locals)
            have sourcePaths := Region.incidencePaths_ofItems items
              (sourceWire.appendLeft locals)
            simp [targetWire, sourceWire] at targetPaths sourcePaths
            simp only [RegionEdit.run]
            rw [targetPaths]
            change (itemsEdit.run.incidencePaths wireIndex).Sublist
              (items.incidencePaths wireIndex 0)
            rw [← sourcePaths]
            exact childResult.2 wireIndex (by simp; omega)
        | sourceToTarget =>
            intro sourceCanonical
            have sourceAdjoinedCanonical :
                (Region.adjoinAt locals .nil
                  (Region.ofItems items)).Canonical :=
              (RegionIso.adjoinAtOfItems locals items).canonical_iff.mpr
                sourceCanonical
            have materialCanonical : (Region.ofItems items).Canonical :=
              Region.Canonical.material_of_adjoinAt locals .nil
                (Region.ofItems items) sourceAdjoinedCanonical
            have childResult := child materialCanonical
            have targetCanonical :
                (Region.adjoinAt locals .nil itemsEdit.run).Canonical := by
              apply Region.Canonical.adjoinAt_of_material_roots locals .nil
                itemsEdit.run True.intro childResult.1
              intro localIndex
              let commonWire : Var (common ++ locals)
                  (locals.get localIndex) :=
                Var.appendRight common (Var.ofIndex localIndex)
              have sourceRoot :=
                Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
                  (Region.ofItems items) sourceAdjoinedCanonical localIndex
              have paths := childResult.2
                ((frame.append locals).sourceKeep commonWire).index.val
                ((frame.append locals).sourceKeep commonWire).index.isLt
              have sourceIndex :
                  ((frame.append locals).sourceKeep commonWire).index.val =
                    sourceWires.length + localIndex.val := by
                simp [commonWire, Frame.append, WireRenaming.appendRight]
              have targetIndex :
                  ((frame.append locals).targetKeep commonWire).index.val =
                    targetWires.length + localIndex.val := by
                simp [commonWire, Frame.append, WireRenaming.appendRight]
              rw [sourceIndex] at paths
              rw [contextLength] at paths sourceRoot
              exact RegionPath.RootedTwo.of_sublist paths sourceRoot
            refine ⟨targetCanonical, ?_⟩
            intro wireIndex wireBound
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetPaths := Region.incidencePaths_adjoinAt_nil
              itemsEdit.run (targetWire.appendLeft locals)
            have sourcePaths := Region.incidencePaths_ofItems items
              (sourceWire.appendLeft locals)
            simp [targetWire, sourceWire] at targetPaths sourcePaths
            simp only [RegionEdit.run]
            rw [targetPaths]
            change (items.incidencePaths wireIndex 0).Sublist
              (itemsEdit.run.incidencePaths wireIndex)
            rw [← sourcePaths]
            exact childResult.2 wireIndex (by simp; omega)
  termination_by structural edit

  theorem ItemsEdit.scopeTransfer
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (direction : ScopeDirection)
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (contextLength : sourceWires.length = targetWires.length)
      (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
        (frame.sourceKeep wire).index.val =
          (frame.targetKeep wire).index.val)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        ScopeTransfer direction
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (selectedPinTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Fin 1 → Var siteSourceWires (.rel arguments))
        (selected : ports 0 = siteFrame.selected),
        ScopeTransfer direction
          (Region.singleton (.identity (.rel arguments) 1 ports))
          (operation.pin siteFrame siteData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires}
        {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : ItemSeq sourceWires}
      (dataInvariant : invariant frame data)
      (edit : ItemsEdit operation frame data source) :
      ScopeTransfer direction (Region.ofItems source) edit.run :=
    match edit with
    | .nil => by
        cases direction <;> intro canonical <;>
          exact ⟨by simpa [ItemsEdit.run] using canonical,
            fun _ _ => List.Sublist.refl _⟩
    | @ItemsEdit.cons _ _ _ _ _ _ _ item tail itemEdit tailEdit => by
        have itemChild := ItemEdit.scopeTransfer direction invariant
          appendInvariant contextLength
          keepIndex selectedAtomTransfer selectedPinTransfer runItemsLength
            dataInvariant itemEdit
        have tailChild := ItemsEdit.scopeTransfer direction invariant
          appendInvariant contextLength
          keepIndex selectedAtomTransfer selectedPinTransfer runItemsLength
            dataInvariant tailEdit
        cases direction with
        | targetToSource =>
            intro targetCanonical
            have split := (Region.Canonical.conjoin_iff _ _).mp targetCanonical
            have itemResult := itemChild split.1
            have tailResult := tailChild split.2
            have sourceCanonical :
                (Region.ofItems (.cons item tail)).Canonical := by
              rw [← Region.singleton_conjoin_ofItems]
              exact (Region.Canonical.conjoin_iff _ _).mpr
                ⟨itemResult.1, tailResult.1⟩
            refine ⟨sourceCanonical, ?_⟩
            intro wireIndex wireBound
            simp only [ItemsEdit.run]
            rw [← Region.singleton_conjoin_ofItems]
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetPaths := Region.incidencePaths_conjoin itemEdit.run
              tailEdit.run targetWire
            have sourcePaths := Region.incidencePaths_conjoin
              (Region.singleton item) (Region.ofItems tail) sourceWire
            simp [targetWire, sourceWire] at targetPaths sourcePaths
            rw [targetPaths, sourcePaths]
            simpa [runItemsLength itemEdit] using
              (itemResult.2 wireIndex wireBound).append
              ((tailResult.2 wireIndex wireBound).map
                (RegionPath.shiftHead 1))
        | sourceToTarget =>
            intro sourceCanonical
            rw [← Region.singleton_conjoin_ofItems] at sourceCanonical
            have split := (Region.Canonical.conjoin_iff _ _).mp sourceCanonical
            have itemResult := itemChild split.1
            have tailResult := tailChild split.2
            have targetCanonical := (Region.Canonical.conjoin_iff _ _).mpr
              ⟨itemResult.1, tailResult.1⟩
            refine ⟨targetCanonical, ?_⟩
            intro wireIndex wireBound
            simp only [ItemsEdit.run]
            rw [← Region.singleton_conjoin_ofItems]
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetPaths := Region.incidencePaths_conjoin itemEdit.run
              tailEdit.run targetWire
            have sourcePaths := Region.incidencePaths_conjoin
              (Region.singleton item) (Region.ofItems tail) sourceWire
            simp [targetWire, sourceWire] at targetPaths sourcePaths
            rw [targetPaths, sourcePaths]
            simpa [runItemsLength itemEdit] using
              (itemResult.2 wireIndex wireBound).append
              ((tailResult.2 wireIndex wireBound).map
                (RegionPath.shiftHead 1))
  termination_by structural edit

  theorem ItemEdit.scopeTransfer
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (direction : ScopeDirection)
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (contextLength : sourceWires.length = targetWires.length)
      (keepIndex : ∀ {wireSignature} (wire : Var common wireSignature),
        (frame.sourceKeep wire).index.val =
          (frame.targetKeep wire).index.val)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        ScopeTransfer direction
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (selectedPinTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Fin 1 → Var siteSourceWires (.rel arguments))
        (selected : ports 0 = siteFrame.selected),
        ScopeTransfer direction
          (Region.singleton (.identity (.rel arguments) 1 ports))
          (operation.pin siteFrame siteData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires}
        {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : Item sourceWires}
      (dataInvariant : invariant frame data)
      (edit : ItemEdit operation frame data source) :
      ScopeTransfer direction (Region.singleton source) edit.run :=
    match edit with
    | .atom head ports => by
        cases direction <;> intro _ <;>
          refine ⟨⟨fun index => Fin.elim0 index,
            ⟨True.intro, True.intro⟩⟩, ?_⟩ <;>
          intro wireIndex wireBound <;>
          simp only [ItemEdit.run, Region.singleton, Region.ofItems,
            Region.incidencePaths, ItemSeq.renameWires,
            Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
            List.append_nil, Var.index_appendLeft] <;>
          apply (List.replicate_sublist_replicate []).mpr <;>
          simp only [Vars.countIndex_map_appendLeft_nil]
        · have countEq := Vars.countIndex_map_eq_of_index_eq ports
            (fun selected => frame.sourceKeep selected)
            (fun selected => frame.targetKeep selected)
            (fun selected => keepIndex selected) wireIndex
          rw [countEq, ← keepIndex head]
          exact Nat.le_refl _
        · have countEq := Vars.countIndex_map_eq_of_index_eq ports
            (fun selected => frame.targetKeep selected)
            (fun selected => frame.sourceKeep selected)
            (fun selected => (keepIndex selected).symm) wireIndex
          rw [countEq, keepIndex head]
          exact Nat.le_refl _
    | .selectedAtom ports siteData =>
        selectedAtomTransfer dataInvariant ports siteData
    | .selectedPin ports selected =>
        selectedPinTransfer dataInvariant ports selected
    | .identity identitySignature arity ports => by
        cases direction <;> intro _ <;>
          refine ⟨⟨fun index => Fin.elim0 index,
            ⟨True.intro, True.intro⟩⟩, ?_⟩ <;>
          intro wireIndex wireBound <;>
          simp only [ItemEdit.run, Region.singleton, Region.ofItems,
            Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
            ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
            Var.index_appendLeft] <;>
          apply (List.replicate_sublist_replicate []).mpr
        · have indicesEq :
              List.ofFn (fun i =>
                (frame.sourceKeep (ports i)).index.val) =
              List.ofFn (fun i =>
                (frame.targetKeep (ports i)).index.val) := by
            apply List.ext_get
            · simp
            · intro n hn hn'
              simp [List.get_eq_getElem, keepIndex]
          rw [indicesEq]
          exact Nat.le_refl _
        · have indicesEq :
              List.ofFn (fun i =>
                (frame.targetKeep (ports i)).index.val) =
              List.ofFn (fun i =>
                (frame.sourceKeep (ports i)).index.val) := by
            apply List.ext_get
            · simp
            · intro n hn hn'
              simp [List.get_eq_getElem, keepIndex]
          rw [indicesEq]
          exact Nat.le_refl _
    | @ItemEdit.cut _ _ _ _ _ _ _ body bodyEdit => by
        have child := RegionEdit.scopeTransfer direction invariant
          appendInvariant contextLength keepIndex selectedAtomTransfer
            selectedPinTransfer runItemsLength dataInvariant bodyEdit
        cases direction with
        | targetToSource =>
            intro targetCanonical
            have childResult := child
              ((Region.singleton_cut_canonical_iff _).mp targetCanonical)
            refine ⟨(Region.singleton_cut_canonical_iff _).mpr childResult.1,
              ?_⟩
            intro wireIndex wireBound
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetRename :=
              Region.incidencePaths_renameWires_appendLeft_nil
                bodyEdit.run targetWire
            have sourceRename :=
              Region.incidencePaths_renameWires_appendLeft_nil body sourceWire
            simp [targetWire, sourceWire] at targetRename sourceRename
            simp only [ItemEdit.run, Region.singleton, Region.ofItems,
              Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
              ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
              Var.index_appendLeft]
            rw [targetRename, sourceRename]
            exact (childResult.2 wireIndex wireBound).map (List.cons 0)
        | sourceToTarget =>
            intro sourceCanonical
            have childResult := child
              ((Region.singleton_cut_canonical_iff _).mp sourceCanonical)
            refine ⟨(Region.singleton_cut_canonical_iff _).mpr childResult.1,
              ?_⟩
            intro wireIndex wireBound
            let targetWire : Var targetWires
                (targetWires.get ⟨wireIndex, by omega⟩) :=
              Var.ofIndex ⟨wireIndex, by omega⟩
            let sourceWire : Var sourceWires
                (sourceWires.get ⟨wireIndex, wireBound⟩) :=
              Var.ofIndex ⟨wireIndex, wireBound⟩
            have targetRename :=
              Region.incidencePaths_renameWires_appendLeft_nil
                bodyEdit.run targetWire
            have sourceRename :=
              Region.incidencePaths_renameWires_appendLeft_nil body sourceWire
            simp [targetWire, sourceWire] at targetRename sourceRename
            simp only [ItemEdit.run, Region.singleton, Region.ofItems,
              Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
              ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
              Var.index_appendLeft]
            rw [targetRename, sourceRename]
            exact (childResult.2 wireIndex wireBound).map (List.cons 0)
  termination_by structural edit
end

/-- Canonicality transfer across an edit which removes a source-only selected
binder.  Retained wires are compared through the frame embeddings instead of
by raw indices, so this is the owner theorem needed by leaf rules whose source
and target contexts have different lengths. -/
def RetainedScopeTransfer
    (frame : Frame arguments common sourceWires targetWires)
    (source : Region sourceWires) (target : Region targetWires) : Prop :=
  target.Canonical → source.Canonical ∧
    ∀ {signature} (wire : Var common signature),
      target.incidencePaths (frame.targetKeep wire).index.val =
        source.incidencePaths (frame.sourceKeep wire).index.val

mutual
  /-- The edit contains no selected-pin case.  Comprehension instantiation
  evidence has this property structurally. -/
  def RegionEdit.NoSelectedPin :
      {source : Region sourceWires} →
        RegionEdit operation frame data source → Prop
    | _, .mk itemsEdit => itemsEdit.NoSelectedPin

  def ItemsEdit.NoSelectedPin :
      {source : ItemSeq sourceWires} →
        ItemsEdit operation frame data source → Prop
    | _, .nil => True
    | _, .cons itemEdit tailEdit =>
        itemEdit.NoSelectedPin ∧ tailEdit.NoSelectedPin

  def ItemEdit.NoSelectedPin :
      {source : Item sourceWires} →
        ItemEdit operation frame data source → Prop
    | _, .selectedPin _ _ => False
    | _, .cut bodyEdit => bodyEdit.NoSelectedPin
    | _, _ => True
end

theorem countPorts_map_eq_of_reflection
    (arity : Nat) (ports : Fin arity → Var common signature)
    (sourceKeep : WireRenaming common sourceWires)
    (targetKeep : WireRenaming common targetWires)
    (reflects : ∀ {leftSignature rightSignature}
      (left : Var common leftSignature) (right : Var common rightSignature),
      (sourceKeep left).index.val = (sourceKeep right).index.val ↔
        (targetKeep left).index.val = (targetKeep right).index.val)
    (wire : Var common wireSignature) :
    (List.ofFn fun position : Fin arity =>
        (sourceKeep (ports position)).index.val).count
          (sourceKeep wire).index.val =
      (List.ofFn fun position : Fin arity =>
        (targetKeep (ports position)).index.val).count
          (targetKeep wire).index.val := by
  induction arity with
  | zero => rfl
  | succ arity induction =>
      rw [List.ofFn_succ, List.ofFn_succ]
      have tailEq := induction (fun position => ports position.succ)
      by_cases sourceEq : (sourceKeep (ports 0)).index.val =
          (sourceKeep wire).index.val
      · have targetEq := (reflects (ports 0) wire).mp sourceEq
        simp [sourceEq, targetEq, tailEq]
      · have targetNe := not_congr (reflects (ports 0) wire) |>.mp sourceEq
        simp [sourceEq, targetNe, tailEq]

mutual
  theorem RegionEdit.retainedTargetToSource
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (indexInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        {invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget} {invariantData : operation.Data invariantFrame},
        invariant invariantFrame invariantData →
          RetainedIndexInvariant invariantFrame)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires} {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        RetainedScopeTransfer siteFrame
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires} {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.NoSelectedPin → itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : Region sourceWires}
      (dataInvariant : invariant frame data)
      (edit : RegionEdit operation frame data source)
      (noPin : edit.NoSelectedPin) :
      RetainedScopeTransfer frame source edit.run :=
    match edit with
    | @RegionEdit.mk _ _ _ _ _ _ _ locals items itemsEdit => by
        intro targetCanonical
        have child := ItemsEdit.retainedTargetToSource invariant
          appendInvariant indexInvariant selectedAtomTransfer runItemsLength
          (appendInvariant frame data locals dataInvariant) itemsEdit
          noPin
          (Region.Canonical.material_of_adjoinAt locals .nil itemsEdit.run
            targetCanonical)
        have sourceAdjoined : (Region.adjoinAt locals .nil
            (Region.ofItems items)).Canonical := by
          apply Region.Canonical.adjoinAt_of_material_roots locals .nil
            (Region.ofItems items) True.intro child.1
          intro localIndex
          let localWire : Var (common ++ locals) (locals.get localIndex) :=
            Var.appendRight common (Var.ofIndex localIndex)
          have targetRoot :=
            Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
              itemsEdit.run targetCanonical localIndex
          have paths := child.2 localWire
          have targetRoot' : RegionPath.RootedTwo
              (itemsEdit.run.incidencePaths
                ((frame.append locals).targetKeep localWire).index.val) := by
            simpa [localWire, Frame.append, WireRenaming.appendRight] using
              targetRoot
          have sourceRoot' : RegionPath.RootedTwo
              ((Region.ofItems items).incidencePaths
                ((frame.append locals).sourceKeep localWire).index.val) := by
            rw [← paths]
            exact targetRoot'
          simpa [localWire, Frame.append, WireRenaming.appendRight] using
            sourceRoot'
        refine ⟨(RegionIso.adjoinAtOfItems locals items).canonical_iff.mp
          sourceAdjoined, ?_⟩
        intro signature wire
        have targetPaths := Region.incidencePaths_adjoinAt_nil itemsEdit.run
          ((frame.targetKeep wire).appendLeft locals)
        have targetPaths' :
            (Region.adjoinAt locals .nil itemsEdit.run).incidencePaths
                (frame.targetKeep wire).index.val =
              itemsEdit.run.incidencePaths
                (frame.targetKeep wire).index.val := by
          simpa using targetPaths
        have childEq := child.2 (wire.appendLeft locals)
        have childEq' : itemsEdit.run.incidencePaths
              (frame.targetKeep wire).index.val =
            (Region.ofItems items).incidencePaths
              (frame.sourceKeep wire).index.val := by
          simpa [Frame.append, WireRenaming.appendRight] using childEq
        have sourcePaths := Region.incidencePaths_ofItems items
          ((frame.sourceKeep wire).appendLeft locals)
        have sourcePaths' : (Region.ofItems items).incidencePaths
              (frame.sourceKeep wire).index.val =
            items.incidencePaths (frame.sourceKeep wire).index.val 0 := by
          simpa using sourcePaths
        simpa [RegionEdit.run] using
          targetPaths'.trans (childEq'.trans sourcePaths')
  termination_by structural edit

  theorem ItemsEdit.retainedTargetToSource
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (indexInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        {invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget} {invariantData : operation.Data invariantFrame},
        invariant invariantFrame invariantData →
          RetainedIndexInvariant invariantFrame)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires} {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        RetainedScopeTransfer siteFrame
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires} {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.NoSelectedPin → itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : ItemSeq sourceWires}
      (dataInvariant : invariant frame data)
      (edit : ItemsEdit operation frame data source)
      (noPin : edit.NoSelectedPin) :
      RetainedScopeTransfer frame (Region.ofItems source) edit.run :=
    match edit with
    | .nil => by
        intro targetCanonical
        exact ⟨by simpa [ItemsEdit.run] using targetCanonical,
          fun _ => rfl⟩
    | @ItemsEdit.cons _ _ _ _ _ _ _ item tail itemEdit tailEdit => by
        intro targetCanonical
        have split := (Region.Canonical.conjoin_iff _ _).mp targetCanonical
        have headResult := ItemEdit.retainedTargetToSource invariant
          appendInvariant indexInvariant selectedAtomTransfer runItemsLength
          dataInvariant itemEdit noPin.1 split.1
        have tailResult := ItemsEdit.retainedTargetToSource invariant
          appendInvariant indexInvariant selectedAtomTransfer runItemsLength
          dataInvariant tailEdit noPin.2 split.2
        refine ⟨by
          rw [← Region.singleton_conjoin_ofItems]
          exact (Region.Canonical.conjoin_iff _ _).mpr
            ⟨headResult.1, tailResult.1⟩, ?_⟩
        intro signature wire
        have targetPaths := Region.incidencePaths_conjoin itemEdit.run
          tailEdit.run (frame.targetKeep wire)
        have sourcePaths := Region.incidencePaths_conjoin
          (Region.singleton item) (Region.ofItems tail) (frame.sourceKeep wire)
        have singletonLength : (Region.singleton item).items.length = 1 := by
          rfl
        simp only [ItemsEdit.run, ← Region.singleton_conjoin_ofItems]
        rw [targetPaths, sourcePaths, headResult.2 wire, tailResult.2 wire]
        rw [runItemsLength itemEdit noPin.1,
          singletonLength]
  termination_by structural edit

  theorem ItemEdit.retainedTargetToSource
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      {frame : Frame arguments common sourceWires targetWires}
      (invariant : ∀ {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget), operation.Data invariantFrame → Prop)
      (appendInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        (invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget) (invariantData : operation.Data invariantFrame)
        (locals : List Sig), invariant invariantFrame invariantData →
          invariant (invariantFrame.append locals)
            (operation.appendData invariantFrame invariantData locals))
      (indexInvariant : ∀
        {invariantCommon invariantSource invariantTarget}
        {invariantFrame : Frame arguments invariantCommon invariantSource
          invariantTarget} {invariantData : operation.Data invariantFrame},
        invariant invariantFrame invariantData →
          RetainedIndexInvariant invariantFrame)
      (selectedAtomTransfer : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        {siteFrame : Frame arguments siteCommon siteSourceWires
          siteTargetWires} {siteData : operation.Data siteFrame}
        (_siteInvariant : invariant siteFrame siteData)
        (ports : Vars siteCommon arguments)
        (selectedData : operation.SiteData siteFrame siteData ports),
        RetainedScopeTransfer siteFrame
          (Region.singleton (.atom siteFrame.selected
            (ports.map fun wire => siteFrame.sourceKeep wire)))
          (operation.site siteFrame siteData ports selectedData))
      (runItemsLength : ∀
        {itemCommon itemSourceWires itemTargetWires : List Sig}
        {itemFrame : Frame arguments itemCommon itemSourceWires
          itemTargetWires} {itemData : operation.Data itemFrame}
        {itemSource : Item itemSourceWires}
        (itemEdit : ItemEdit operation itemFrame itemData itemSource),
        itemEdit.NoSelectedPin → itemEdit.run.items.length = 1)
      {data : operation.Data frame} {source : Item sourceWires}
      (dataInvariant : invariant frame data)
      (edit : ItemEdit operation frame data source)
      (noPin : edit.NoSelectedPin) :
      RetainedScopeTransfer frame (Region.singleton source) edit.run :=
    match edit with
    | .atom head ports => by
        intro _
        refine ⟨⟨fun index => Fin.elim0 index,
          ⟨True.intro, True.intro⟩⟩, ?_⟩
        intro signature wire
        have index := indexInvariant dataInvariant
        have portsEq := Vars.countIndex_map_eq_of_reflection ports
          frame.sourceKeep frame.targetKeep index.reflects wire
        have targetAppend := Vars.countIndex_map_eq_of_index_eq ports
          (fun selected => (frame.targetKeep selected).appendLeft [])
          (fun selected => frame.targetKeep selected)
          (fun selected => Var.index_appendLeft _ _) (frame.targetKeep wire).index.val
        have sourceAppend := Vars.countIndex_map_eq_of_index_eq ports
          (fun selected => (frame.sourceKeep selected).appendLeft [])
          (fun selected => frame.sourceKeep selected)
          (fun selected => Var.index_appendLeft _ _) (frame.sourceKeep wire).index.val
        simp only [ItemEdit.run, Region.singleton, Region.ofItems,
          Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
          ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
          Var.index_appendLeft]
        by_cases sourceEq : (frame.sourceKeep head).index.val =
            (frame.sourceKeep wire).index.val
        · have targetEq := (index.reflects head wire).mp sourceEq
          simp [sourceEq, targetEq]
          exact targetAppend.trans (portsEq.symm.trans sourceAppend.symm)
        · have targetNe := not_congr (index.reflects head wire) |>.mp sourceEq
          simp [sourceEq, targetNe]
          exact targetAppend.trans (portsEq.symm.trans sourceAppend.symm)
    | .selectedAtom ports siteData =>
        selectedAtomTransfer dataInvariant ports siteData
    | .selectedPin ports selected => False.elim noPin
    | .identity identitySignature arity ports => by
        intro _
        refine ⟨⟨fun index => Fin.elim0 index,
          ⟨True.intro, True.intro⟩⟩, ?_⟩
        intro signature wire
        have index := indexInvariant dataInvariant
        have portsEq := countPorts_map_eq_of_reflection arity ports
          frame.sourceKeep frame.targetKeep index.reflects wire
        simp only [ItemEdit.run, Region.singleton, Region.ofItems,
          Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
          ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
          Var.index_appendLeft]
        rw [portsEq]
    | @ItemEdit.cut _ _ _ _ _ _ _ body bodyEdit => by
        intro targetCanonical
        have child := RegionEdit.retainedTargetToSource invariant
          appendInvariant indexInvariant selectedAtomTransfer runItemsLength
          dataInvariant bodyEdit noPin
          ((Region.singleton_cut_canonical_iff _).mp targetCanonical)
        refine ⟨(Region.singleton_cut_canonical_iff _).mpr child.1, ?_⟩
        intro signature wire
        have targetRename := Region.incidencePaths_renameWires_appendLeft_nil
          bodyEdit.run (frame.targetKeep wire)
        have sourceRename := Region.incidencePaths_renameWires_appendLeft_nil
          body (frame.sourceKeep wire)
        simp only [ItemEdit.run, Region.singleton, Region.ofItems,
          Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
          ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
          Var.index_appendLeft]
        rw [targetRename, sourceRename, child.2 wire]
  termination_by structural edit
end

private theorem EnvironmentsAgree.append
    {arguments common sourceWires targetWires locals : List Sig}
    {frame : Frame arguments common sourceWires targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (agree : EnvironmentsAgree frame sourceEnv targetEnv)
    (localEnv : Values model locals) :
    EnvironmentsAgree (frame.append locals)
      (Values.append sourceEnv localEnv)
      (Values.append targetEnv localEnv) := by
  intro signature wire
  apply Var.appendCases
    (motive := fun wire =>
      (sourceEnv.append localEnv).lookup
          ((frame.append locals).sourceKeep wire) =
        (targetEnv.append localEnv).lookup
          ((frame.append locals).targetKeep wire))
  · intro signature inherited
    simpa [Frame.append, WireRenaming.appendRight] using agree inherited
  · intro signature localWire
    simp [Frame.append, WireRenaming.appendRight]

theorem evaluate_retained_eq
    {arguments common sourceWires targetWires signatures : List Sig}
    {frame : Frame arguments common sourceWires targetWires}
    {model : Model} {sourceEnv : Values model sourceWires}
    {targetEnv : Values model targetWires}
    (ports : Vars common signatures)
    (agree : EnvironmentsAgree frame sourceEnv targetEnv) :
    evaluateVars (ports.map fun wire => frame.sourceKeep wire) sourceEnv =
      evaluateVars (ports.map fun wire => frame.targetKeep wire) targetEnv := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, evaluateVars]
      rw [agree head, induction]

theorem denote_singleton_iff
    (item : Item wires) (model : Model) (env : Values model wires) :
    denoteRegion model env (Region.singleton item) ↔
      denoteItem model env item := by
  unfold Region.singleton Region.ofItems
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  change (∃ localEnv : Values model [],
      denoteItemSeq model (env.append localEnv)
        ((ItemSeq.cons item .nil).renameWires appendNil)) ↔ _
  have envEq (localEnv : Values model []) :
      Values.rename appendNil (env.append localEnv) = env := by
    apply Values.ext
    intro signature wire
    simp [appendNil]
  constructor
  · rintro ⟨localEnv, itemDenotes, _⟩
    have renamed := (denoteItem_renameWires model appendNil
      (env.append localEnv) item).mp itemDenotes
    rwa [envEq] at renamed
  · intro itemDenotes
    refine ⟨PUnit.unit, ?_, trivial⟩
    apply (denoteItem_renameWires model appendNil
      (env.append PUnit.unit) item).mpr
    rwa [envEq]

theorem denote_blank_iff (model : Model) (env : Values model wires) :
    denoteRegion model env (Region.blank wires) ↔ True := by
  unfold Region.blank
  constructor
  · intro
    trivial
  · intro
    exact ⟨PUnit.unit, trivial⟩

mutual
  theorem RegionEdit.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires}
      (edit : RegionEdit operation frame data source)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteRegion model sourceEnv source ↔
        denoteRegion model targetEnv edit.run := by
    cases edit with
    | mk itemsEdit =>
      simp only [RegionEdit.run]
      simp only [denoteRegion_mk]
      rw [Region.denote_adjoinAt]
      constructor
      · rintro ⟨localEnv, itemsDenote⟩
        exact ⟨localEnv, trivial,
          (itemsEdit.sound_iff operationSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operationSound.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mp itemsDenote⟩
      · rintro ⟨localEnv, _, resultDenotes⟩
        exact ⟨localEnv,
          (itemsEdit.sound_iff operationSound model
            (Values.append sourceEnv localEnv)
            (Values.append targetEnv localEnv)
            (agree.append localEnv)
            (operationSound.realizes_append frame data model sourceEnv targetEnv
              realizes localEnv)).mpr resultDenotes⟩

  theorem ItemsEdit.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {items : ItemSeq sourceWires}
      (edit : ItemsEdit operation frame data items)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteItemSeq model sourceEnv items ↔
        denoteRegion model targetEnv edit.run := by
    cases edit with
    | nil =>
      simp only [ItemsEdit.run]
      change True ↔ ∃ localEnv : Values model [], True
      constructor
      · intro
        exact ⟨PUnit.unit, trivial⟩
      · intro
        trivial
    | cons itemEdit tailEdit =>
      simp only [ItemsEdit.run]
      rw [denoteItemSeq_cons, Region.denote_conjoin]
      exact and_congr
        (itemEdit.sound_iff operationSound model sourceEnv targetEnv
          agree realizes)
        (tailEdit.sound_iff operationSound model sourceEnv targetEnv
          agree realizes)

  theorem ItemEdit.sound_iff
      {arguments common sourceWires targetWires : List Sig}
      {operation : Operation arguments}
      (operationSound : operation.Sound)
      {frame : Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {item : Item sourceWires}
      (edit : ItemEdit operation frame data item)
      (model : Model) (sourceEnv : Values model sourceWires)
      (targetEnv : Values model targetWires)
      (agree : EnvironmentsAgree frame sourceEnv targetEnv)
      (realizes : operationSound.Realizes frame data model sourceEnv targetEnv) :
      denoteItem model sourceEnv item ↔
        denoteRegion model targetEnv edit.run := by
    cases edit with
    | atom head ports =>
      simp only [ItemEdit.run]
      rw [denote_singleton_iff]
      simp only [denoteItem_atom]
      rw [agree head, evaluate_retained_eq ports agree]
    | selectedAtom ports siteData =>
      simp only [ItemEdit.run]
      exact operationSound.site_sound frame data ports siteData model sourceEnv
        targetEnv agree realizes
    | selectedPin ports selected =>
      simp only [ItemEdit.run]
      simp only [denoteItem_identity]
      constructor
      · intro _
        exact operationSound.pin_sound frame data model targetEnv
      · intro _ left right
        have positionsEqual : left = right := Subsingleton.elim _ _
        subst right
        rfl
    | identity signature arity ports =>
      simp only [ItemEdit.run]
      rw [denote_singleton_iff]
      simp only [denoteItem_identity]
      constructor
      · intro sourceDenotes left right
        rw [← agree (ports left), ← agree (ports right)]
        exact sourceDenotes left right
      · intro targetDenotes left right
        rw [agree (ports left), agree (ports right)]
        exact targetDenotes left right
    | cut bodyEdit =>
      simp only [ItemEdit.run]
      rw [denote_singleton_iff]
      simp only [denoteItem_cut]
      exact not_congr
        (bodyEdit.sound_iff operationSound model sourceEnv targetEnv agree
          realizes)
end

end VisualProof.Rule.WirePrimitive.Transform
