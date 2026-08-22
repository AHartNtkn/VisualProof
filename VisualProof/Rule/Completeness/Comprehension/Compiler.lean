import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Rule.Completeness.Erasure.Exposure
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Compiler


/-- Compile one complete selected-application layer through formal
application. Boundary and equality compilation prepare the authoritative
instantiation endpoint to the exact all-sites transform endpoint; this theorem
owns the mandatory primitive at the comprehension binder's home occurrence. -/
private theorem itemsFormal
    {outer localBefore localAfter before after : List Sig}
    {pattern : OpenDiagram
      (before ++ .rel (before ++ after) :: after)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (before ++ .rel (before ++ after) :: after) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).sourceKeep
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).selected
        source result)
    (sites : ItemsSites (Leaf.Formal.operation before after) PUnit.unit
      evidence)
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil result)
      (.mk
        (localBefore ++
          .rel (before ++ .rel (before ++ after) :: after) :: localAfter)
        source))
    (prepare : ∀ output : ExactEdit
      (Transform.ItemsEdit (Leaf.Formal.operation before after)
        (Leaf.Formal.rootFrame outer localBefore localAfter before after)
        PUnit.unit source)
      (fun edit => edit.run),
      request.Preparation
        (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
          output.endpoint)) :
    request.Result := by
  exact items (operation := Leaf.Formal.operation before after)
    (frame := Leaf.Formal.rootFrame outer localBefore localAfter before after)
    PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Formal.Applies.Description outer := {
            before := before
            after := after
            localBefore := localBefore
            localAfter := localAfter
            items := source
            itemsEdit := edit
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          let supplied := prepare {
            edit := edit
            endpoint := staged
            run_eq := runEq
          }
          let preparation : request.Preparation description.target :=
            stagedEq ▸ supplied
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source : Region outer) = description.source := by
            rfl
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source)
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch preparation.prepared := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Formal.Local
            inject := fun step => Step.formalApplication step
            preparedCanonical := preparation.preparedCanonical
            preparedExternalTwoEnded :=
              preparation.preparedExternalTwoEnded
            rawPreparedCanonical := preparation.rawPreparedCanonical
            rawPreparedExternalTwoEnded :=
              preparation.rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparation.preparedIso
            pendingIso := pendingIso
            localStep := .abstractFormal (.mk description)
            preparation := preparation.telescope
          }
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

/-- Compile one complete selected-application layer through identity leaf.
Boundary and equality compilation prepare the authoritative instantiation
endpoint to the exact all-sites transform endpoint; this theorem owns the
mandatory primitive at the comprehension binder's home occurrence. -/
private theorem itemsIdentity
    {outer localBefore localAfter : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram (List.replicate arity signature)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).sourceKeep
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).selected
        source result)
    (sites : ItemsSites (Leaf.Identity.operation signature arity) PUnit.unit
      evidence)
    (request : Telescope.Request
      (Region.adjoinAt (localBefore ++ localAfter) .nil result)
      (.mk
        (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
        source))
    (prepare : ∀ output : ExactEdit
      (Transform.ItemsEdit (Leaf.Identity.operation signature arity)
        (Leaf.Identity.rootFrame outer localBefore localAfter signature arity)
        PUnit.unit source)
      (fun edit => edit.run),
      request.Preparation
        (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
          output.endpoint)) :
    request.Result := by
  exact items (operation := Leaf.Identity.operation signature arity)
    (frame := Leaf.Identity.rootFrame outer localBefore localAfter signature
      arity)
    PUnit.unit evidence sites request {
    close := fun output => by
      cases output with
      | mk edit staged runEq =>
          let description : Leaf.Identity.Leaves.Description outer := {
            signature := signature
            arity := arity
            localBefore := localBefore
            localAfter := localAfter
            items := source
            itemsEdit := edit
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          let supplied := prepare {
            edit := edit
            endpoint := staged
            run_eq := runEq
          }
          let preparation : request.Preparation description.target :=
            stagedEq ▸ supplied
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                source : Region outer) = description.source := by
            rfl
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (List.replicate arity signature) :: localAfter)
                source)
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch preparation.prepared := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Identity.Local
            inject := fun step => Step.identityLeaf step
            preparedCanonical := preparation.preparedCanonical
            preparedExternalTwoEnded :=
              preparation.preparedExternalTwoEnded
            rawPreparedCanonical := preparation.rawPreparedCanonical
            rawPreparedExternalTwoEnded :=
              preparation.rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparation.preparedIso
            pendingIso := pendingIso
            localStep := .abstractIdentity (.mk description)
            preparation := preparation.telescope
          }
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact .primitive branch stagedIso
  }

namespace PatternCompiler

namespace EqualityNormalization

def formalPorts (arguments : List Sig) : Vars arguments arguments :=
  Erasure.Exposure.identityBoundary arguments

private theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : ∀ {signature}, Var source signature → Var target signature)
    (position : Fin signatures.length) :
    (variables.map rename).get position = rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

private theorem formalPorts_get_index (position : Fin arguments.length) :
    ((formalPorts arguments).get position).index = position := by
  exact Erasure.Exposure.identityBoundary_get_index position

private theorem formalPorts_surjective (wire : Fin arguments.length) :
    ∃ position : Fin arguments.length,
      ((formalPorts arguments).get position).index = wire :=
  ⟨wire, formalPorts_get_index wire⟩

private theorem equalityItems_left_mem_nil
    (left right : Vars wires signatures)
    (position : Fin signatures.length) (itemIndex : Nat) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      left right).incidencePaths (left.get position).index.val itemIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; exact Fin.elim0 position
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          revert itemIndex
          refine Fin.cases (fun itemIndex => ?_)
            (fun rest itemIndex => ?_) position
          · change [] ∈
              (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
                (.cons leftHead leftTail)
                (.cons rightHead rightTail)).incidencePaths
                  leftHead.index.val itemIndex
            simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityPorts,
              List.mem_append, List.mem_replicate]
            apply Or.inl
            constructor
            · intro countZero
              have absent := List.count_eq_zero.mp countZero
              exact absent (by simp)
            · trivial
          · simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, List.mem_append]
            exact Or.inr (induction rightTail rest (itemIndex + 1))

/-- Exact local list produced by the defining instantiation operations. -/
private def locals (pattern : OpenDiagram arguments) : List Sig :=
  pattern.external ++ (pattern.body.locals ++ [])

private def bodyEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming (pattern.external ++ pattern.body.locals)
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (WireRenaming.comp
      (Region.conjoinLeftWire (targetWires ++ pattern.external)
        pattern.body.locals [])
      ((⟨fun wire => Var.appendRight targetWires wire⟩ :
        WireRenaming pattern.external
          (targetWires ++ pattern.external)).appendRight pattern.body.locals))

private def equalityEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming ((targetWires ++ pattern.external) ++ [])
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (Region.conjoinRightWire (targetWires ++ pattern.external)
      pattern.body.locals [])

private def actualEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming targetWires (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((wire.appendLeft pattern.external).appendLeft [])⟩

private def patternEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming pattern.external (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((Var.appendRight targetWires wire).appendLeft [])⟩

private def items (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    ItemSeq (targetWires ++ locals pattern) :=
  (pattern.body.items.renameWires (bodyEmbedding pattern targetWires)).append
    (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      (ports.map fun wire => actualEmbedding pattern targetWires wire)
      (pattern.boundaryWire.map
        fun wire => patternEmbedding pattern targetWires wire))

private theorem bodyEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (bodyEmbedding pattern sourceWires) =
      bodyEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire =>
      WireRenaming.comp (rename.appendRight (locals pattern))
          (bodyEmbedding pattern sourceWires) wire =
        bodyEmbedding pattern targetWires wire)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

private theorem actualEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (actualEmbedding pattern sourceWires) =
      WireRenaming.comp (actualEmbedding pattern targetWires) rename := by
  apply WireRenaming.ext
  intro signature wire
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

private theorem patternEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (patternEmbedding pattern sourceWires) =
      patternEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

@[simp] private theorem actualEmbedding_index_val
    (pattern : OpenDiagram arguments)
    (wire : Var targetWires signature) :
    (actualEmbedding pattern targetWires wire).index.val = wire.index.val := by
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

private theorem bodyEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var (pattern.external ++ pattern.body.locals) signature) :
    targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val := by
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire => targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

private theorem patternEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var pattern.external signature) :
    targetWires.length ≤
      (patternEmbedding pattern targetWires wire).index.val := by
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

private theorem Vars.map_comp4
    (variables : Vars first signatures)
    (firstMap : ∀ {signature}, Var first signature → Var second signature)
    (secondMap : ∀ {signature}, Var second signature → Var third signature)
    (thirdMap : ∀ {signature}, Var third signature → Var fourth signature)
    (fourthMap : ∀ {signature}, Var fourth signature → Var fifth signature) :
    (((variables.map fun wire => firstMap wire).map
      fun wire => secondMap wire).map fun wire => thirdMap wire).map
        (fun wire => fourthMap wire) =
      variables.map fun wire =>
        fourthMap (thirdMap (secondMap (firstMap wire))) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons
        (fourthMap (thirdMap (secondMap (firstMap head))))) induction

private theorem instantiate_eq_presentation
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports = .mk (locals pattern) (items pattern ports) := by
  cases pattern with
  | mk external boundaryWire boundarySurjective body canonical
      externalTwoEnded =>
    cases body with
    | mk bodyLocals bodyItems =>
      simp only [
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate,
        _root_.VisualProof.Rule.Comprehension.Instantiation.Equalities_eq_ofItems,
        items, bodyEmbedding, actualEmbedding, patternEmbedding,
        equalityEmbedding, locals,
        Region.locals, Region.items, Region.renameWires, Region.conjoin,
        Region.adjoinAt, Region.ofItems, ItemSeq.renameWires_append,
        ItemSeq.renameWires_comp,
        _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
      simp only [ItemSeq.renameWires, ItemSeq.nil_append,
        Vars.map_comp4, WireRenaming.comp]

private theorem instantiate_renameWires
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).renameWires rename =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire) := by
  have actualMap :
      (ports.map fun wire => actualEmbedding pattern sourceWires wire).map
          (fun wire => rename.appendRight (locals pattern) wire) =
        (ports.map fun wire => rename wire).map
          (fun wire => actualEmbedding pattern targetWires wire) := by
    calc
      _ = ports.map (fun wire =>
          rename.appendRight (locals pattern)
            (actualEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp ports (actualEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = ports.map (fun wire =>
          actualEmbedding pattern targetWires (rename wire)) := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming sourceWires
              (targetWires ++ locals pattern) =>
            ports.map fun wire => map wire)
          (actualEmbedding_natural pattern rename)
      _ = _ := (Diagram.vars_map_comp ports rename
        (actualEmbedding pattern targetWires)).symm
  have patternMap :
      (pattern.boundaryWire.map
          fun wire => patternEmbedding pattern sourceWires wire).map
            (fun wire => rename.appendRight (locals pattern) wire) =
        pattern.boundaryWire.map
          (fun wire => patternEmbedding pattern targetWires wire) := by
    calc
      _ = pattern.boundaryWire.map (fun wire =>
          rename.appendRight (locals pattern)
            (patternEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp pattern.boundaryWire
          (patternEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = _ := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming pattern.external
              (targetWires ++ locals pattern) =>
            pattern.boundaryWire.map fun wire => map wire)
          (patternEmbedding_natural pattern rename)
  rw [instantiate_eq_presentation, instantiate_eq_presentation]
  simp only [Region.renameWires, items, ItemSeq.renameWires_append,
    ItemSeq.renameWires_comp,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
  rw [bodyEmbedding_natural, actualMap, patternMap]

/-- Every actual port of an instantiation has a root-level equality
incidence. -/
private theorem instantiate_port_incidence_mem_nil
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val := by
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append]
  have selected := equalityItems_left_mem_nil
    (ports.map fun wire => actualEmbedding pattern targetWires wire)
    (pattern.boundaryWire.map
      fun wire => patternEmbedding pattern targetWires wire)
    position (pattern.body.items.renameWires
      (bodyEmbedding pattern targetWires)).length
  have selectedIndex :
      ((ports.map fun wire => actualEmbedding pattern targetWires wire).get
        position).index.val = (ports.get position).index.val := by
    rw [Vars.get_map]
    simp [actualEmbedding, equalityEmbedding, WireRenaming.comp,
      Region.conjoinRightWire, Region.adjoinMaterialWire, locals]
  rw [selectedIndex] at selected
  exact List.mem_append_right _ (by
    simpa only [Nat.zero_add] using selected)

/-- Every actual port of an instantiation has an equality incidence. -/
private theorem instantiate_port_incidence_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val ≠ [] :=
  List.ne_nil_of_mem (instantiate_port_incidence_mem_nil pattern ports position)

private theorem Vars.countIndex_map_zero_of_lower
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (floor wireIndex : Nat)
    (lower : ∀ {signature} (wire : Var source signature),
      floor ≤ (rename wire).index.val)
    (below : wireIndex < floor) :
    (variables.map fun wire => rename wire).countIndex wireIndex = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex]
      have different : (rename head).index.val ≠ wireIndex := by
        intro equality
        have := lower head
        omega
      simp only [different, if_false, Nat.zero_add]
      exact induction

private theorem Vars.countIndex_map_actual
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires signatures)
    (wireIndex : Nat) :
    (ports.map fun wire => actualEmbedding pattern targetWires wire).countIndex
        wireIndex = ports.countIndex wireIndex := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, actualEmbedding_index_val,
        induction]

private theorem instantiate_incidencePaths_length
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val).length =
      ports.countIndex wire.index.val := by
  have bodyEmpty :
      (pattern.body.items.renameWires
        (bodyEmbedding pattern targetWires)).incidencePaths
          wire.index.val 0 = [] := by
    apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
    · have bound := wire.index.isLt
      simp only [List.length_append]
      omega
    · intro bodySignature bodyWire equality
      have lower := bodyEmbedding_index_lower
        (targetWires := targetWires) pattern bodyWire
      have bound := wire.index.isLt
      omega
  have rightZero :
      (pattern.boundaryWire.map
        fun boundaryWire => patternEmbedding pattern targetWires
          boundaryWire).countIndex wire.index.val = 0 := by
    apply Vars.countIndex_map_zero_of_lower pattern.boundaryWire
      (patternEmbedding pattern targetWires) targetWires.length
        wire.index.val
    · exact patternEmbedding_index_lower
        (targetWires := targetWires) pattern
    · exact wire.index.isLt
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append,
    List.length_append,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_incidencePaths_length,
    bodyEmpty,
    List.length_nil, Nat.zero_add, Vars.countIndex_map_actual, rightZero,
    Nat.add_zero]

private theorem instantiate_incidence_nonempty_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val ≠ [] ↔
      0 < ports.countIndex wire.index.val := by
  rw [← List.length_pos_iff, instantiate_incidencePaths_length]

/-- Replace an arbitrary valid pattern boundary by the ordered identity
boundary over its argument context. Its body is the exact existing-syntax
instantiation of the original pattern on those formal variables. -/
def identityBoundary (pattern : OpenDiagram arguments) :
    OpenDiagram arguments where
  external := arguments
  boundaryWire := formalPorts arguments
  boundarySurjective := formalPorts_surjective
  body := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  canonical :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
      pattern (formalPorts arguments)
  externalTwoEnded := by
    intro signature wire
    have boundaryPositive :
        0 < (formalPorts arguments).countIndex wire.index.val := by
      obtain ⟨position, maps⟩ := formalPorts_surjective wire.index
      have positive := (formalPorts arguments).countIndex_get_positive position
      rw [maps] at positive
      exact positive
    have bodyPositive : 0 <
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)).incidencePaths
            wire.index.val).length := by
      have nonempty := instantiate_port_incidence_nonempty pattern
        (formalPorts arguments) wire.index
      rw [formalPorts_get_index] at nonempty
      exact List.length_pos_iff.mpr nonempty
    omega

private def formalSubstitution : {arguments : List Sig} →
    Vars targetWires arguments → WireRenaming arguments targetWires
  | [], .nil => ⟨fun wire => nomatch wire⟩
  | _ :: _, .cons head tail => ⟨fun wire =>
      match wire with
      | .here => head
      | .there rest => formalSubstitution tail rest⟩

@[simp] private theorem formalSubstitution_here
    (head : Var targetWires signature)
    (tail : Vars targetWires arguments) :
    formalSubstitution (.cons head tail) (.here : Var (signature :: arguments)
      signature) = head := rfl

private theorem formalPorts_map_substitution
    (ports : Vars targetWires arguments) :
    (formalPorts arguments).map
      (fun wire => formalSubstitution ports wire) = ports := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [formalPorts, Erasure.Exposure.identityBoundary, Vars.map,
        formalSubstitution_here]
      congr 1
      rw [Diagram.vars_map_comp
        (Erasure.Exposure.identityBoundary _) ⟨fun wire => .there wire⟩
          (formalSubstitution (.cons head tail))]
      change (formalPorts _).map
        (fun wire => formalSubstitution tail wire) = tail
      exact induction

private theorem formalPorts_eq_exposure :
    formalPorts arguments = Erasure.Exposure.identityBoundary arguments := by
  rfl

private theorem supportPins_eq_nil
    (material : Region materialWires)
    (variables : Vars materialWires signatures)
    (supported : ∀ position : Fin signatures.length,
      material.incidencePaths (variables.get position).index.val ≠ []) :
    Erasure.Exposure.supportPins material signatures variables = .nil := by
  induction variables with
  | nil => rfl
  | @cons signature rest head tail induction =>
      have headSupported : material.incidencePaths head.index.val ≠ [] := by
        simpa only [Vars.get] using supported 0
      have tailSupported : ∀ position : Fin rest.length,
          material.incidencePaths (tail.get position).index.val ≠ [] := by
        intro position
        simpa only [Vars.get] using supported position.succ
      simp only [Erasure.Exposure.supportPins, headSupported, ↓reduceIte]
      exact induction tailSupported

private theorem normalized_supportPins_eq_nil
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportPins
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments))
      arguments (Erasure.Exposure.identityBoundary arguments) = .nil := by
  apply supportPins_eq_nil
  intro position
  simpa only [← formalPorts_eq_exposure] using
    instantiate_port_incidence_nonempty pattern
      (formalPorts arguments) position

private theorem supportBody_eq_of_supportPins_nil
    (material : Region materialWires)
    (empty : Erasure.Exposure.supportPins material materialWires
      (Erasure.Exposure.identityBoundary materialWires) = .nil) :
    Erasure.Exposure.supportBody material = material := by
  unfold Erasure.Exposure.supportBody
  rw [empty]
  cases material with
  | mk locals materialItems =>
      change Region.mk locals (materialItems.append .nil) =
        Region.mk locals materialItems
      rw [ItemSeq.append_nil]

private theorem OpenDiagram.eq_of_data
    (left right : OpenDiagram boundary)
    (externalEq : left.external = right.external)
    (boundaryEq : HEq left.boundaryWire right.boundaryWire)
    (bodyEq : HEq left.body right.body) : left = right := by
  cases left with
  | mk leftExternal leftBoundary leftSurjective leftBody leftCanonical
      leftTwoEnded =>
    cases right with
    | mk rightExternal rightBoundary rightSurjective rightBody rightCanonical
        rightTwoEnded =>
      simp only at externalEq boundaryEq bodyEq
      cases externalEq
      cases boundaryEq
      cases bodyEq
      rfl

private theorem normalized_supportBody_eq
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportBody
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)) =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments) := by
  apply supportBody_eq_of_supportPins_nil
  exact normalized_supportPins_eq_nil pattern

private theorem supportPattern_eq_identityBoundary
    (pattern : OpenDiagram arguments)
    (materialCanonical :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)).Canonical) :
    Erasure.Exposure.supportPattern
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)) materialCanonical =
      identityBoundary pattern := by
  apply OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq (normalized_supportBody_eq pattern)

private def exposureDescriptionWithHost
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Rule.Erasure.Description outer where
  materialWires := arguments
  hostLocals := hostLocals
  hostItems := hostItems
  material := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  wireMap := formalSubstitution ports

private theorem exposureDescriptionWithHost_source
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    (exposureDescriptionWithHost pattern hostLocals hostItems ports).source =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports) := by
  simp only [Rule.Erasure.Description.source,
    exposureDescriptionWithHost, Region.spliceAt]
  rw [instantiate_renameWires, formalPorts_map_substitution]

private theorem exposureDescriptionWithHost_applicationPorts
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Erasure.Exposure.applicationPorts
      (exposureDescriptionWithHost pattern hostLocals hostItems ports) =
      ports := by
  simp only [Erasure.Exposure.applicationPorts,
    exposureDescriptionWithHost]
  rw [← formalPorts_eq_exposure, formalPorts_map_substitution]

private theorem exposureDescriptionWithHost_exposedRegion
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments)
    (materialCanonical :
      (exposureDescriptionWithHost pattern hostLocals hostItems ports).material.Canonical) :
    Erasure.Exposure.exposedRegion
        (exposureDescriptionWithHost pattern hostLocals hostItems ports)
        materialCanonical =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (identityBoundary pattern) ports) := by
  simp only [Erasure.Exposure.exposedRegion]
  change Region.adjoinAt hostLocals hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern (formalPorts arguments)) materialCanonical)
        (Erasure.Exposure.applicationPorts
          (exposureDescriptionWithHost pattern hostLocals hostItems ports))) =
    _
  rw [supportPattern_eq_identityBoundary pattern materialCanonical,
    exposureDescriptionWithHost_applicationPorts]

private theorem Vars.exists_get_index_of_countIndex_pos
    (variables : Vars context signatures) (wireIndex : Nat)
    (positive : 0 < variables.countIndex wireIndex) :
    ∃ position : Fin signatures.length,
      (variables.get position).index.val = wireIndex := by
  induction variables with
  | nil => simp [Vars.countIndex] at positive
  | @cons signature rest head tail induction =>
      by_cases headEq : head.index.val = wireIndex
      · exact ⟨0, headEq⟩
      · have tailPositive : 0 < tail.countIndex wireIndex := by
          simpa [Vars.countIndex, headEq] using positive
        obtain ⟨position, positionEq⟩ := induction tailPositive
        exact ⟨position.succ, by
          simpa only [Vars.get] using positionEq⟩

private theorem instantiate_incidence_mem_nil_of_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature)
    (nonempty :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).incidencePaths wire.index.val ≠ []) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val := by
  have positive := (instantiate_incidence_nonempty_iff pattern ports wire).mp
    nonempty
  obtain ⟨position, positionEq⟩ :=
    Vars.exists_get_index_of_countIndex_pos ports wire.index.val positive
  have rootIncidence := instantiate_port_incidence_mem_nil pattern ports position
  rw [positionEq] at rootIncidence
  exact rootIncidence

private theorem instantiate_rootedTwo_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    RegionPath.RootedTwo
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val) ↔
      2 ≤ ports.countIndex wire.index.val := by
  constructor
  · intro rooted
    have lengthBound := rooted.1
    rw [instantiate_incidencePaths_length] at lengthBound
    exact lengthBound
  · intro countBound
    have nonempty :
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val ≠ [] :=
      (instantiate_incidence_nonempty_iff pattern ports wire).mpr (by omega)
    constructor
    · rw [instantiate_incidencePaths_length]
      exact countBound
    · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _
        (instantiate_incidence_mem_nil_of_nonempty pattern ports wire nonempty)

mutual
  private def normalizedRegion
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .mk childSites =>
        let childOutput := normalizedItems pattern _ childSites
        ⟨Region.adjoinAt _ .nil childOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            childOutput.2⟩
  termination_by structural sites

  private def normalizedItems
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .nil _ =>
        ⟨Region.blank common,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil⟩
    | .cons itemSites tailSites =>
        let itemOutput := normalizedItem pattern _ itemSites
        let tailOutput := normalizedItems pattern _ tailSites
        ⟨itemOutput.1.conjoin tailOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemOutput.2 tailOutput.2⟩
  termination_by structural sites

  private def normalizedItem
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .atom head ports =>
        ⟨Region.singleton (.atom head ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports⟩
    | .selectedAtom ports _ =>
        ⟨_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            ports⟩
    | .identity signature arity ports =>
        ⟨Region.singleton (.identity signature arity ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports⟩
    | .cut childSites =>
        let childOutput := normalizedRegion pattern _ childSites
        ⟨Region.singleton (.cut childOutput.1),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childOutput.2⟩
  termination_by structural sites
end

mutual
  /-- Whether the exact site annotation contains any selected application. -/
  private def regionHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) : Bool :=
    match sites with
    | .mk childSites => itemsHaveSelection childSites
  termination_by structural sites

  private def itemsHaveSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) : Bool :=
    match sites with
    | .nil _ => false
    | .cons itemSites tailSites =>
        itemHasSelection itemSites || itemsHaveSelection tailSites
  termination_by structural sites

  private def itemHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) : Bool :=
    match sites with
    | .atom _ _ => false
    | .selectedAtom _ _ => true
    | .identity _ _ _ => false
    | .cut childSites => regionHasSelection childSites
  termination_by structural sites
end

mutual
  private theorem normalizedRegion_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (none : regionHasSelection sites = false) :
      (normalizedRegion pattern evidence sites).1 = result :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        change Region.adjoinAt locals .nil
            (normalizedItems pattern childEvidence childSites).1 =
          Region.adjoinAt locals .nil childResult
        rw [normalizedItems_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [regionHasSelection] using none)]
  termination_by structural sites

  private theorem normalizedItems_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (none : itemsHaveSelection sites = false) :
      (normalizedItems pattern evidence sites).1 = result :=
    match sites with
    | .nil _ => rfl
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        have itemNone : itemHasSelection itemSites = false := by
          cases selected : itemHasSelection itemSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.true_or,
              Bool.true_eq_false]
        have tailNone : itemsHaveSelection tailSites = false := by
          cases selected : itemsHaveSelection tailSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.or_true,
              Bool.true_eq_false]
        change
          (normalizedItem pattern itemEvidence itemSites).1.conjoin
              (normalizedItems pattern tailEvidence tailSites).1 =
            itemResult.conjoin tailResult
        rw [normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
          itemNone]
        rw [normalizedItems_eq_of_noSelection pattern tailEvidence tailSites
          tailNone]
  termination_by structural sites

  private theorem normalizedItem_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (none : itemHasSelection sites = false) :
      (normalizedItem pattern evidence sites).1 = result :=
    match sites with
    | .atom _ _ => rfl
    | .selectedAtom _ _ => by
        simp only [itemHasSelection, Bool.true_eq_false] at none
    | .identity _ _ _ => rfl
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        change Region.singleton
            (.cut (normalizedRegion pattern childEvidence childSites).1) =
          Region.singleton (.cut childResult)
        rw [normalizedRegion_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [itemHasSelection] using none)]
  termination_by structural sites
end

mutual
  private theorem normalizedRegion_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      ScopePreservation result (normalizedRegion pattern evidence sites).1 :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        let childOutput := normalizedItems pattern childEvidence childSites
        let childPreservation :=
          normalizedItems_scope pattern childEvidence childSites
        change ScopePreservation
          (Region.adjoinAt locals .nil childResult)
          (Region.adjoinAt locals .nil childOutput.1)
        constructor
        · intro sourceCanonical
          have sourceChildCanonical : childResult.Canonical :=
            Region.Canonical.material_of_adjoinAt locals .nil childResult
              sourceCanonical
          have targetChildCanonical : childOutput.1.Canonical :=
            childPreservation.canonical sourceChildCanonical
          apply Region.Canonical.adjoinAt_of_material_roots locals .nil
            childOutput.1 True.intro targetChildCanonical
          intro localIndex
          let localWire := Var.appendRight common (Var.ofIndex localIndex)
          have sourceRoot : RegionPath.RootedTwo
              (childResult.incidencePaths localWire.index.val) := by
            simpa [localWire] using
              Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
                childResult sourceCanonical localIndex
          have targetRoot := childPreservation.rootedTwo localWire sourceRoot
          simpa [localWire] using targetRoot
        · intro signature wire
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths, targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.incidenceNonempty childWire
        · intro signature wire sourceRoot
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths] at sourceRoot
          rw [targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.rootedTwo childWire (by
              simpa only [childWire, Var.index_appendLeft] using sourceRoot)
  termination_by structural sites

  private theorem normalizedItems_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      ScopePreservation result (normalizedItems pattern evidence sites).1 :=
    match sites with
    | .nil _ => by
        change ScopePreservation (Region.blank common) (Region.blank common)
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        let itemOutput := normalizedItem pattern itemEvidence itemSites
        let tailOutput := normalizedItems pattern tailEvidence tailSites
        let itemPreservation := normalizedItem_scope pattern itemEvidence
          itemSites
        let tailPreservation := normalizedItems_scope pattern tailEvidence
          tailSites
        change ScopePreservation (itemResult.conjoin tailResult)
          (itemOutput.1.conjoin tailOutput.1)
        have combined := Region.conjoin_preserves_scope itemResult tailResult
          itemOutput.1 tailOutput.1 itemPreservation.canonical
            tailPreservation.canonical itemPreservation.incidenceNonempty
              tailPreservation.incidenceNonempty itemPreservation.rootedTwo
                tailPreservation.rootedTwo
        exact {
          canonical := combined.1
          incidenceNonempty := fun wire => (combined.2 wire).1
          rootedTwo := fun wire => (combined.2 wire).2
        }
  termination_by structural sites

  private theorem normalizedItem_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      ScopePreservation result (normalizedItem pattern evidence sites).1 :=
    match sites with
    | .atom head ports => by
        change ScopePreservation (Region.singleton (.atom head ports))
          (Region.singleton (.atom head ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | .selectedAtom ports _ => by
        change ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports)
        constructor
        · intro _
          exact
            _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
              (identityBoundary pattern) ports
        · intro signature wire
          rw [instantiate_incidence_nonempty_iff,
            instantiate_incidence_nonempty_iff]
        · intro signature wire sourceRoot
          rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
          exact sourceRoot
    | .identity signature arity ports => by
        change ScopePreservation
          (Region.singleton (.identity signature arity ports))
          (Region.singleton (.identity signature arity ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        let childOutput := normalizedRegion pattern childEvidence childSites
        let childPreservation := normalizedRegion_scope pattern childEvidence
          childSites
        change ScopePreservation (Region.singleton (.cut childResult))
          (Region.singleton (.cut childOutput.1))
        constructor
        · intro sourceCanonical
          apply (Region.singleton_cut_canonical_iff childOutput.1).mpr
          exact childPreservation.canonical
            ((Region.singleton_cut_canonical_iff childResult).mp
              sourceCanonical)
        · intro signature wire
          rw [Region.incidencePaths_singleton_cut,
            Region.incidencePaths_singleton_cut]
          constructor
          · intro sourceNonempty
            have childSourceNonempty :
                childResult.incidencePaths wire.index.val ≠ [] := by
              intro sourceEmpty
              exact sourceNonempty
                ((List.map_eq_nil_iff).mpr sourceEmpty)
            have childTargetNonempty :=
              (childPreservation.incidenceNonempty wire).mp
                childSourceNonempty
            intro targetEmpty
            exact childTargetNonempty
              ((List.map_eq_nil_iff).mp targetEmpty)
          · intro targetNonempty
            have childTargetNonempty :
                childOutput.1.incidencePaths wire.index.val ≠ [] := by
              intro targetEmpty
              exact targetNonempty
                ((List.map_eq_nil_iff).mpr targetEmpty)
            have childSourceNonempty :=
              (childPreservation.incidenceNonempty wire).mpr
                childTargetNonempty
            intro sourceEmpty
            exact childSourceNonempty
              ((List.map_eq_nil_iff).mp sourceEmpty)
        · intro signature wire sourceRoot
          have sameEmpty :
              childResult.incidencePaths wire.index.val = [] ↔
                childOutput.1.incidencePaths wire.index.val = [] := by
            constructor
            · intro sourceEmpty
              by_cases targetEmpty :
                  childOutput.1.incidencePaths wire.index.val = []
              · exact targetEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mpr
                    targetEmpty) sourceEmpty)
            · intro targetEmpty
              by_cases sourceEmpty :
                  childResult.incidencePaths wire.index.val = []
              · exact sourceEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mp
                    sourceEmpty) targetEmpty)
          rw [Region.incidencePaths_singleton_cut] at sourceRoot ⊢
          have replaced := RegionPath.rootedTwo_replace []
            (childResult.incidencePaths wire.index.val)
            (childOutput.1.incidencePaths wire.index.val) [] 0 sameEmpty
          simpa only [List.nil_append, List.append_nil] using
            replaced.mp (by simpa using sourceRoot)
  termination_by structural sites
end

/-- Normalize every selected application in one exact authoritative item
sequence and preserve the canonical, externally two-ended scope of its actual
occurrence. The normalized endpoint and its instantiation evidence are
generated solely from the supplied evidence-indexed sites. -/
theorem normalizeItemsScope
    {arguments common sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ normalized : Region common,
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        (occurrence.context.fill normalized).Canonical ∧
        OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill normalized) := by
  let output := normalizedItems pattern evidence sites
  let preservation := normalizedItems_scope pattern evidence sites
  have resultCanonical : result.Canonical :=
    occurrence.context.holeCanonical result occurrence.sourceCanonical
  have normalizedCanonical : output.1.Canonical :=
    preservation.canonical resultCanonical
  have replacement := occurrence.context.replaceCanonical result output.1
    occurrence.sourceCanonical normalizedCanonical
      preservation.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill result) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have normalizedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill output.1) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill output.1) replacement.2
  exact ⟨output.1, output.2, replacement.1, normalizedExternalTwoEnded⟩

private def appendHostWire (outer hostLocals : List Sig) :
    WireRenaming outer (outer ++ hostLocals) :=
  ⟨fun wire => wire.appendLeft hostLocals⟩

private theorem conjoin_eq_adjoinRename
    (host material : Region outer) :
    host.conjoin material =
      Region.adjoinAt host.locals host.items
        (material.renameWires (appendHostWire outer host.locals)) := by
  cases host with
  | mk hostLocals hostItems =>
      cases material with
      | mk materialLocals materialItems =>
          have materialMap : WireRenaming.comp
              (Region.adjoinMaterialWire outer hostLocals materialLocals)
              ((appendHostWire outer hostLocals).appendRight materialLocals) =
            Region.conjoinRightWire outer hostLocals materialLocals := by
            apply WireRenaming.ext
            intro signature wire
            apply Var.appendCases (left := outer)
              (right := materialLocals)
              (motive := fun wire =>
                WireRenaming.comp
                    (Region.adjoinMaterialWire outer hostLocals materialLocals)
                    ((appendHostWire outer hostLocals).appendRight
                      materialLocals) wire =
                  Region.conjoinRightWire outer hostLocals materialLocals
                    wire)
            · intro inheritedSignature inherited
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
            · intro localSignature localWire
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
          simp only [Region.conjoin, Region.adjoinAt, Region.renameWires,
            Region.locals, Region.items, ItemSeq.renameWires_comp,
            Region.adjoinHostWire]
          rw [materialMap]

private noncomputable def instantiateRenameIso
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).renameWires rename)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire)) := by
  rw [instantiate_renameWires]
  exact RegionIso.refl _

private theorem canonical_conjoin
    {outer : List Sig} {first second : Region outer}
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical) :
    (first.conjoin second).Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          rw [conjoin_eq_adjoinRename]
          exact Region.Canonical.adjoinAt firstLocals firstItems
            ((Region.mk secondLocals secondItems).renameWires
              (appendHostWire _ firstLocals)) firstCanonical
            ((Region.Canonical.renameWires_iff
              (Region.mk secondLocals secondItems)
              (appendHostWire _ firstLocals)).mpr secondCanonical)

private theorem canonical_right_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : second.Canonical := by
  rw [conjoin_eq_adjoinRename] at canonical
  have renamed := Region.Canonical.material_of_adjoinAt first.locals
    first.items (second.renameWires (appendHostWire _ first.locals)) canonical
  exact (Region.Canonical.renameWires_iff second
    (appendHostWire _ first.locals)).mp renamed

private theorem canonical_left_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : first.Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          simp only [Region.conjoin, Region.Canonical] at canonical ⊢
          constructor
          · intro localIndex
            let hostWire := Var.appendRight outer (Var.ofIndex localIndex)
            let combinedIndex : Fin (firstLocals ++ secondLocals).length :=
              ⟨localIndex.val, by
                simp only [List.length_append]
                exact Nat.lt_add_right _ localIndex.isLt⟩
            have combinedRoot := canonical.1 combinedIndex
            have combinedWireIndex :
                outer.length + combinedIndex.val = hostWire.index.val := by
              simp [combinedIndex, hostWire]
            rw [combinedWireIndex, ItemSeq.incidencePaths_append]
              at combinedRoot
            have hostMap :
                Region.conjoinLeftWire outer firstLocals secondLocals =
                  Region.adjoinHostWire outer firstLocals secondLocals := rfl
            rw [hostMap,
              ItemSeq.incidencePaths_renameWires_adjoinHost
              firstItems hostWire 0] at combinedRoot
            have secondEmpty :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.conjoinLeftWire outer firstLocals
                          secondLocals)).length) = [] := by
              apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
              · have hostBound := localIndex.isLt
                simp [hostWire, List.length_append]
                omega
              · intro signature wire
                apply Var.appendCases (left := outer)
                  (right := secondLocals)
                  (motive := fun wire =>
                    (Region.conjoinRightWire outer firstLocals secondLocals
                      wire).index.val ≠ hostWire.index.val)
                · intro inheritedSignature inherited
                  have bound := inherited.index.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
                · intro localSignature localWire
                  have hostBound := localIndex.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
            have secondEmpty' :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.adjoinHostWire outer firstLocals
                          secondLocals)).length) = [] := by
              simpa only [← hostMap] using secondEmpty
            rw [secondEmpty', List.append_nil] at combinedRoot
            simpa [hostWire, combinedIndex] using combinedRoot
          · have children :=
              (ItemSeq.childrenCanonical_append _ _).mp canonical.2 |>.1
            exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
              firstItems).mp children
/-- Refine an actual occurrence through one further exact recursive context.
The composed context is the only occurrence path; `fill_comp` identifies its
source with the caller's actual filled endpoint. -/
private noncomputable def Occurrence.nest
    {boundary middle holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    {inner : DiagramContext middle holeWires}
    (occurrence : Occurrence (inner.fill before) source) :
    Occurrence before source where
  interface := occurrence.interface
  context := occurrence.context.comp inner
  sourceCanonical := by
    simpa only [DiagramContext.fill_comp] using occurrence.sourceCanonical
  sourceExternalTwoEnded := by
    intro signature wire
    simpa only [DiagramContext.fill_comp] using
      occurrence.sourceExternalTwoEnded wire
  host_iso := by
    simpa only [DiagramContext.fill_comp] using occurrence.host_iso

/-- Bidirectional nonempty reachability between exact occurrence endpoints.
This stronger internal form permits endpoint presentation transport while
the public equality phase remains optional when no selected site exists. -/
private def StrictEquates
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (after : Region holeWires)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)) : Prop :=
  let target := occurrence.interface.withBody
    (occurrence.context.fill after) targetCanonical targetExternalTwoEnded
  Relation.TransGen Step source target ∧
    Relation.TransGen Step target source

private theorem StrictEquates.toEquates
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (strict : StrictEquates occurrence after targetCanonical
      targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail steps step induction => exact .tail induction step
  exact ⟨optional strict.1, optional strict.2⟩

/-- A nonempty symmetric loop at an exact occurrence. The two Vacuity steps
insert and immediately remove one structurally fixed point, so presentation
transport never relies on a zero-length derivation. -/
private theorem StrictEquates.refl
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source) :
    StrictEquates occurrence before occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded := by
  have regionEta :
      Vacuity.Point.plain before.locals before.items = before := by
    cases before
    rfl
  let pointOccurrence : Occurrence
      (Vacuity.Point.plain before.locals before.items) source := by
    rw [regionEta]
    exact occurrence
  have pointValidity :=
    Vacuity.Point.introduceValidity pointOccurrence Sig.iota
  let pointEndpoint := pointOccurrence.interface.withBody
    (pointOccurrence.context.fill
      (Vacuity.Point.present before.locals before.items Sig.iota))
    pointValidity.1 pointValidity.2
  have introduction : Vacuity source pointEndpoint := by
    exact ⟨holeWires,
      Vacuity.Point.plain before.locals before.items,
      Vacuity.Point.present before.locals before.items Sig.iota,
      pointOccurrence, pointValidity.1, pointValidity.2,
      OpenDiagramIso.refl _,
      atPolarity_symmetric_of pointOccurrence.context.polarity
        (.mk (.point before.locals before.items Sig.iota))⟩
  let exact := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have exactIntroduction : Vacuity exact pointEndpoint := by
    exact Vacuity.iso occurrence.host_iso introduction
      (OpenDiagramIso.refl pointEndpoint)
  exact ⟨(Relation.TransGen.single (Step.vacuity introduction)).tail
      (Step.vacuity exactIntroduction.symm),
    (Relation.TransGen.single (Step.vacuity exactIntroduction)).tail
      (Step.vacuity introduction.symm)⟩

/-- Transport the exact target presentation of a nonempty symmetric phase. -/
private theorem StrictEquates.targetIso
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (strict : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (targetIso : OpenDiagramIso
      (occurrence.interface.withBody (occurrence.context.fill middle)
        middleCanonical middleExternalTwoEnded)
      (occurrence.interface.withBody (occurrence.context.fill after)
        targetCanonical targetExternalTwoEnded)) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨transGen_iso (OpenDiagramIso.refl source) strict.1 targetIso,
    transGen_iso targetIso strict.2 (OpenDiagramIso.refl source)⟩

/-- Consecutive nonempty symmetric phases compose at their exact midpoint. -/
private theorem StrictEquates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (first : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : StrictEquates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩

/-- Consecutive bidirectional phases at the same actual occurrence compose. -/
private theorem Equates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (first : Equates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : Equates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩


private noncomputable def presentationOccurrence
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (afterCanonical : after.Canonical)
    (sameNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ [])
    (presentation : RegionIso (WireEquiv.refl holeWires) before after) :
    Occurrence after source := by
  have replacement := occurrence.context.replaceCanonical before after
    occurrence.sourceCanonical afterCanonical sameNonempty
  let beforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after) :=
    beforeEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill after) replacement.2
  exact {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := replacement.1
    sourceExternalTwoEnded := afterExternalTwoEnded
    host_iso := occurrence.host_iso.trans
      (OpenDiagram.withBody_iso occurrence.sourceCanonical replacement.1
        occurrence.sourceExternalTwoEnded afterExternalTwoEnded
        (DiagramContext.fillIso occurrence.context presentation))
  }

private theorem pinStep
    {boundary holeWires locals : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (Vacuity.Pin.plain locals items) source)
    (signature : Sig) (wire : Var (holeWires ++ locals) signature) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Vacuity.Pin.present locals items signature wire)).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present locals items signature wire)),
        Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Vacuity.Pin.present locals items signature wire))
              targetCanonical targetExternalTwoEnded) ∧
          Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Vacuity.Pin.present locals items signature wire))
              targetCanonical targetExternalTwoEnded)
            source := by
  have validity := Vacuity.Pin.introduceValidity occurrence signature wire
  let step : Vacuity source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Vacuity.Pin.present locals items signature wire))
        validity.1 validity.2) := ⟨holeWires, Vacuity.Pin.plain locals items,
    Vacuity.Pin.present locals items signature wire, occurrence,
    validity.1, validity.2, OpenDiagramIso.refl _,
    atPolarity_symmetric_of occurrence.context.polarity
      (.mk (.pin locals items signature wire))⟩
  exact ⟨validity.1, validity.2,
    Step.vacuity step, Step.vacuity step.symm⟩

/-- One unary identity for every wire in a typed source context. -/
private def allPins (source : List Sig)
    (rename : WireRenaming source target) : ItemSeq target :=
  ItemSeq.pinWires source rename (fun _ => true)

/-- Add one pin for every selected source wire at an exact occurrence. -/
private theorem pinAllExact
    {boundary holeWires locals pinWires : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (items : ItemSeq (holeWires ++ locals))
    (rename : WireRenaming pinWires (holeWires ++ locals))
    (sourceCanonical :
      (context.fill (.mk locals items)).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals items))) :
    ∃ targetCanonical :
        (context.fill
          (.mk locals (items.append (allPins pinWires rename)))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire
          (context.fill
            (.mk locals (items.append (allPins pinWires rename)))),
        Equates
          (exactOccurrence interface context (.mk locals items)
            sourceCanonical sourceExternalTwoEnded)
          (.mk locals (items.append (allPins pinWires rename)))
          targetCanonical targetExternalTwoEnded := by
  induction pinWires generalizing items with
  | nil =>
      refine ⟨by simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
          sourceCanonical,
        by
          intro wireSignature wire
          simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
            sourceExternalTwoEnded wire,
        ?_⟩
      simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
        (show Equates
          (exactOccurrence interface context (.mk locals items)
            sourceCanonical sourceExternalTwoEnded)
          (.mk locals items) sourceCanonical sourceExternalTwoEnded from
          ⟨.refl, .refl⟩)
  | cons signature tail induction =>
      let tailRename : WireRenaming tail (holeWires ++ locals) :=
        ⟨fun wire => rename (.there wire)⟩
      let pin := Item.identity signature 1 (fun _ => rename .here)
      let occurrence := exactOccurrence interface context (.mk locals items)
        sourceCanonical sourceExternalTwoEnded
      obtain ⟨firstCanonical, firstExternalTwoEnded, firstSteps⟩ :=
        pinStep occurrence signature (rename .here)
      let firstItems := items.append (.cons pin .nil)
      have firstCanonical' :
          (context.fill (.mk locals firstItems)).Canonical := by
        simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
          Vacuity.Pin.plain] using firstCanonical
      have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire (context.fill (.mk locals firstItems)) := by
        intro wireSignature wire
        simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
          Vacuity.Pin.plain] using firstExternalTwoEnded wire
      obtain ⟨targetCanonical, targetExternalTwoEnded, rest⟩ :=
        induction firstItems tailRename firstCanonical'
          firstExternalTwoEnded'
      refine ⟨?_, ?_, ?_⟩
      · simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using targetCanonical
      · intro wireSignature wire
        simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using targetExternalTwoEnded wire
      · have firstEquates : Equates occurrence
            (.mk locals firstItems) firstCanonical' firstExternalTwoEnded' := by
          exact ⟨.tail .refl (by
              simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
                Vacuity.Pin.plain] using firstSteps.1),
            .tail .refl (by
              simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
                Vacuity.Pin.plain] using firstSteps.2)⟩
        have combined := Equates.trans firstEquates rest
        simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using combined

/-- A nonempty all-wire pin batch has a genuine Vacuity step in each
direction, even when the supplied occurrence uses a nontrivial source
presentation. -/
private theorem pinAllNonempty
    {boundary holeWires locals : List Sig}
    {signature : Sig} {tail : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (Vacuity.Pin.plain locals items) source)
    (rename : WireRenaming (signature :: tail) (holeWires ++ locals)) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals
            (items.append (allPins (signature :: tail) rename)))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals
              (items.append (allPins (signature :: tail) rename)))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals
                  (items.append (allPins (signature :: tail) rename))))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals
                  (items.append (allPins (signature :: tail) rename))))
              targetCanonical targetExternalTwoEnded)
            source := by
  let tailRename : WireRenaming tail (holeWires ++ locals) :=
    ⟨fun wire => rename (.there wire)⟩
  let pin := Item.identity signature 1 (fun _ => rename .here)
  obtain ⟨firstCanonical, firstExternalTwoEnded, firstSteps⟩ :=
    pinStep occurrence signature (rename .here)
  let firstItems := items.append (.cons pin .nil)
  have firstCanonical' :
      (occurrence.context.fill (.mk locals firstItems)).Canonical := by
    simpa only [pin, firstItems, Vacuity.Pin.present,
      Vacuity.Pin.plain] using firstCanonical
  have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (.mk locals firstItems)) := by
    intro wireSignature wire
    simpa only [pin, firstItems, Vacuity.Pin.present,
      Vacuity.Pin.plain] using firstExternalTwoEnded wire
  obtain ⟨targetCanonical, targetExternalTwoEnded, rest⟩ :=
    pinAllExact occurrence.interface occurrence.context firstItems tailRename
      firstCanonical' firstExternalTwoEnded'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using targetCanonical
  · intro wireSignature wire
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using targetExternalTwoEnded wire
  · have first : Step source
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pin, firstItems, Vacuity.Pin.present,
        Vacuity.Pin.plain] using firstSteps.1
    have combined := (Relation.TransGen.single first).reflTransGen rest.1
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using combined
  · have first : Step
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') source := by
      simpa only [pin, firstItems, Vacuity.Pin.present,
        Vacuity.Pin.plain] using firstSteps.2
    have combined := rest.2.transGen (Relation.TransGen.single first)
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using combined

/-- Two complete pin batches provide two root incidences for every selected
wire and remain a nonempty symmetric Vacuity derivation. -/
private theorem pinAllTwiceNonempty
    {boundary holeWires locals : List Sig}
    {signature : Sig} {tail : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (.mk locals items) source)
    (rename : WireRenaming (signature :: tail) (holeWires ++ locals)) :
    let pins := allPins (signature :: tail) rename
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals ((items.append pins).append pins))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded)
            source := by
  dsimp only
  obtain ⟨firstCanonical, firstExternalTwoEnded, first⟩ :=
    pinAllNonempty occurrence rename
  let pins := allPins (signature :: tail) rename
  let firstItems := items.append pins
  have firstCanonical' :
      (occurrence.context.fill (.mk locals firstItems)).Canonical := by
    simpa only [pins, firstItems] using firstCanonical
  have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (.mk locals firstItems)) := by
    intro wireSignature wire
    simpa only [pins, firstItems] using firstExternalTwoEnded wire
  obtain ⟨targetCanonical, targetExternalTwoEnded, second⟩ :=
    pinAllExact occurrence.interface occurrence.context firstItems rename
      firstCanonical' firstExternalTwoEnded'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pins, firstItems] using targetCanonical
  · intro wireSignature wire
    simpa only [pins, firstItems] using targetExternalTwoEnded wire
  · have first' : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pins, firstItems] using first.1
    exact first'.reflTransGen (by
      simpa only [pins, firstItems] using second.1)
  · have first' : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') source := by
      simpa only [pins, firstItems] using first.2
    have secondReverse : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins)))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pins, firstItems] using second.2
    exact secondReverse.transGen first'

private theorem pinAllTwiceOfNonempty
    {boundary holeWires locals pinWires : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (.mk locals items) source)
    (rename : WireRenaming pinWires (holeWires ++ locals))
    (nonempty : pinWires ≠ []) :
    let pins := allPins pinWires rename
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals ((items.append pins).append pins))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded)
            source := by
  cases pinWires with
  | nil => exact False.elim (nonempty rfl)
  | cons signature tail => exact pinAllTwiceNonempty occurrence rename

private theorem allPins_renameWires
    (source : List Sig) (rename : WireRenaming source middle)
    (next : WireRenaming middle target) :
    (allPins source rename).renameWires next =
      allPins source (WireRenaming.comp next rename) := by
  induction source with
  | nil => rfl
  | cons signature tail induction =>
      simp only [allPins, ItemSeq.pinWires, if_true,
        ItemSeq.renameWires, Item.renameWires]
      exact congrArg (ItemSeq.cons
        (.identity signature 1
          (fun _ => next (rename (.here : Var (signature :: tail)
            signature)))))
        (induction ⟨fun wire => rename (.there wire)⟩)

private theorem allPins_mem_nil
    (source : List Sig) (rename : WireRenaming source target)
    (wire : Var source signature) (itemIndex : Nat) :
    [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val itemIndex := by
  exact ItemSeq.pinWires_mem_nil source rename (fun _ => true) wire
    itemIndex rfl

/-- Two complete pin batches root every selected wire at the current region. -/
private theorem allPins_twice_rooted
    (source : List Sig) (rename : WireRenaming source target)
    (wire : Var source signature) (itemIndex : Nat) :
    RegionPath.RootedTwo
      (((allPins source rename).append (allPins source rename)).incidencePaths
        (rename wire).index.val itemIndex) := by
  rw [ItemSeq.incidencePaths_append]
  have firstMem : [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val itemIndex :=
    allPins_mem_nil source rename wire itemIndex
  have secondMem : [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val
        (itemIndex + (allPins source rename).length) :=
    allPins_mem_nil source rename wire
      (itemIndex + (allPins source rename).length)
  constructor
  · have firstPositive := List.length_pos_iff.mpr
      (List.ne_nil_of_mem firstMem)
    have secondPositive := List.length_pos_iff.mpr
      (List.ne_nil_of_mem secondMem)
    simp only [List.length_append]
    omega
  · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _
      (List.mem_append.mpr (Or.inl firstMem))

private theorem allPins_twice_childrenCanonical
    (source : List Sig) (rename : WireRenaming source target) :
    ((allPins source rename).append
      (allPins source rename)).ChildrenCanonical := by
  exact (ItemSeq.childrenCanonical_append _ _).mpr
    ⟨ItemSeq.pinWires_childrenCanonical source rename (fun _ => true),
      ItemSeq.pinWires_childrenCanonical source rename (fun _ => true)⟩
private def appendAdjoinedPins
    (hostLocals : List Sig) (hostItems pins : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) : Region outer :=
  match material with
  | .mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      .mk (hostLocals ++ materialLocals)
        (((hostItems.renameWires hostRename).append
          (materialItems.renameWires materialRename)).append
            (pins.renameWires hostRename))

/-- Moving a pin block from after adjoined material into the host item block
is a presentation isomorphism and changes no rewrite authority. -/
private noncomputable def adjoinPinsIso
    (hostLocals : List Sig) (hostItems pins : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) :
    RegionIso (WireEquiv.refl outer)
      (appendAdjoinedPins hostLocals hostItems pins material)
      (Region.adjoinAt hostLocals (hostItems.append pins) material) := by
  cases material with
  | mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      let host := hostItems.renameWires hostRename
      let material := materialItems.renameWires materialRename
      let pinItems := pins.renameWires hostRename
      let reordered : ItemSeqIso
          (WireEquiv.refl (outer ++ (hostLocals ++ materialLocals)))
          ((host.append material).append pinItems)
          ((host.append pinItems).append material) := by
        let moved := ItemSeqIso.append (ItemSeqIso.refl host)
          (ItemSeqIso.swapAppend material pinItems)
        simpa only [ItemSeq.append_assoc] using moved
      refine .mk (WireEquiv.refl (hostLocals ++ materialLocals)) ?_
      simpa only [Region.adjoinAt, Region.locals, Region.items,
        ItemSeq.renameWires_append, hostRename, materialRename, host,
        material, pinItems] using
        reordered.castAmbient
          (WireEquiv.append_refl outer
            (hostLocals ++ materialLocals)).symm

private theorem ItemSeq.incidencePaths_append_nonempty_iff
    (first second : ItemSeq wires) (wireIndex itemIndex : Nat) :
    (first.append second).incidencePaths wireIndex itemIndex ≠ [] ↔
      first.incidencePaths wireIndex 0 ≠ [] ∨
        second.incidencePaths wireIndex 0 ≠ [] := by
  constructor
  · intro joinedNonempty
    by_cases firstEmpty : first.incidencePaths wireIndex 0 = []
    · apply Or.inr
      intro secondEmpty
      apply joinedNonempty
      rw [ItemSeq.incidencePaths_append]
      rw [(ItemSeq.incidencePaths_eq_nil_iff_itemIndex first wireIndex
        itemIndex 0).mpr firstEmpty]
      rw [(ItemSeq.incidencePaths_eq_nil_iff_itemIndex second wireIndex
        (itemIndex + first.length) 0).mpr secondEmpty]
      rfl
    · exact Or.inl firstEmpty
  · intro nonempty
    intro joinedEmpty
    rw [ItemSeq.incidencePaths_append] at joinedEmpty
    have parts := List.append_eq_nil_iff.mp joinedEmpty
    rcases nonempty with firstNonempty | secondNonempty
    · exact firstNonempty
        ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex first wireIndex
          itemIndex 0).mp parts.1)
    · exact secondNonempty
        ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex second wireIndex
          (itemIndex + first.length) 0).mp parts.2)

private theorem ItemSeq.incidencePaths_rotate_nonempty_iff
    (host material pins : ItemSeq wires) (wireIndex itemIndex : Nat) :
    ((host.append material).append pins).incidencePaths
        wireIndex itemIndex ≠ [] ↔
      ((host.append pins).append material).incidencePaths
        wireIndex itemIndex ≠ [] := by
  simp only [ItemSeq.incidencePaths_append_nonempty_iff]
  constructor
  · rintro ((hostNonempty | materialNonempty) | pinsNonempty)
    · exact Or.inl (Or.inl hostNonempty)
    · exact Or.inr materialNonempty
    · exact Or.inl (Or.inr pinsNonempty)
  · rintro ((hostNonempty | pinsNonempty) | materialNonempty)
    · exact Or.inl (Or.inl hostNonempty)
    · exact Or.inr pinsNonempty
    · exact Or.inl (Or.inr materialNonempty)

private def contextPins (outer hostLocals : List Sig) :
    ItemSeq (outer ++ hostLocals) :=
  let pins := allPins (outer ++ hostLocals) WireRenaming.id
  pins.append pins

private theorem contextPins_incidence_nonempty
    (outer hostLocals : List Sig)
    (wire : Var (outer ++ hostLocals) signature) (itemIndex : Nat) :
    (contextPins outer hostLocals).incidencePaths
      wire.index.val itemIndex ≠ [] := by
  let pins := allPins (outer ++ hostLocals) WireRenaming.id
  have member : [] ∈ pins.incidencePaths wire.index.val itemIndex := by
    simpa only [WireRenaming.id] using
      allPins_mem_nil (outer ++ hostLocals) WireRenaming.id wire itemIndex
  rw [show contextPins outer hostLocals = pins.append pins by rfl,
    ItemSeq.incidencePaths_append]
  exact List.append_ne_nil_of_left_ne_nil (List.ne_nil_of_mem member) _

private theorem pinnedHostCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (sourceCanonical :
      (Region.adjoinAt hostLocals hostItems material).Canonical) :
    (Region.mk hostLocals
      (hostItems.append (contextPins outer hostLocals))).Canonical := by
  cases material with
  | mk materialLocals materialItems =>
      have hostRenamedChildren :
          (hostItems.renameWires
            (Region.adjoinHostWire outer hostLocals
              materialLocals)).ChildrenCanonical := by
        have sourceChildren := sourceCanonical.2
        simp only at sourceChildren
        exact (ItemSeq.childrenCanonical_append _ _).mp
          sourceChildren |>.1
      have hostChildren : hostItems.ChildrenCanonical :=
        (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
          hostItems).mp hostRenamedChildren
      constructor
      · intro localIndex
        let localWire := Var.appendRight outer (Var.ofIndex localIndex)
        have pinRoot := allPins_twice_rooted
          (outer ++ hostLocals) WireRenaming.id localWire
          hostItems.length
        rw [ItemSeq.incidencePaths_append]
        apply RegionPath.RootedTwo.of_sublist
          (List.sublist_append_right _ _)
        simpa [contextPins, localWire, WireRenaming.id] using pinRoot
      · exact (ItemSeq.childrenCanonical_append _ _).mpr
          ⟨hostChildren,
            allPins_twice_childrenCanonical
              (outer ++ hostLocals) WireRenaming.id⟩
/-- Add the structural double-pin block around arbitrary adjoined material,
transporting the nonempty Vacuity derivation through the exact item
permutation that places those pins in the host block. -/
private theorem adjoinPinsEquatesNonempty
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems material) source)
    (nonempty : outer ++ hostLocals ≠ []) :
    let target := Region.adjoinAt hostLocals
      (hostItems.append (contextPins outer hostLocals)) material
    ∃ targetCanonical : (occurrence.context.fill target).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill target),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill target)
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill target)
              targetCanonical targetExternalTwoEnded)
            source := by
  dsimp only
  cases material with
  | mk materialLocals materialItems =>
      let hostRename :=
        Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      let host := hostItems.renameWires hostRename
      let material := materialItems.renameWires materialRename
      let pin := allPins (outer ++ hostLocals) hostRename
      let base := host.append material
      let directOccurrence : Occurrence
          (.mk (hostLocals ++ materialLocals) base) source := by
        simpa only [Region.adjoinAt, hostRename, materialRename, host,
          material, base] using occurrence
      obtain ⟨rawCanonical, rawExternalTwoEnded, rawSteps⟩ :=
        pinAllTwiceOfNonempty directOccurrence hostRename nonempty
      let raw := Region.mk (hostLocals ++ materialLocals)
        ((base.append pin).append pin)
      have rawCanonical' : (occurrence.context.fill raw).Canonical := by
        simpa only [directOccurrence, pin, base, raw] using rawCanonical
      have rawExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill raw) := by
        intro wireSignature wire
        simpa only [directOccurrence, pin, base, raw] using
          rawExternalTwoEnded wire
      have compId : WireRenaming.comp hostRename WireRenaming.id =
          hostRename := by
        apply WireRenaming.ext
        intro wireSignature wire
        rfl
      have pinsRename :
          (contextPins outer hostLocals).renameWires hostRename =
            pin.append pin := by
        simp only [contextPins, ItemSeq.renameWires_append,
          allPins_renameWires, compId, pin]
      have rawEq : raw = appendAdjoinedPins hostLocals hostItems
          (contextPins outer hostLocals)
          (.mk materialLocals materialItems) := by
        simp only [raw, appendAdjoinedPins, hostRename, materialRename,
          host, material, base, pinsRename, ItemSeq.append_assoc]
      let target := Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals))
        (.mk materialLocals materialItems)
      let presentation : RegionIso (WireEquiv.refl outer) raw target := by
        rw [rawEq]
        exact adjoinPinsIso hostLocals hostItems
          (contextPins outer hostLocals)
          (.mk materialLocals materialItems)
      have sourceLocalCanonical :
          (Region.adjoinAt hostLocals hostItems
            (.mk materialLocals materialItems)).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have materialCanonical :
          (Region.mk materialLocals materialItems).Canonical :=
        Region.Canonical.material_of_adjoinAt hostLocals hostItems _
          sourceLocalCanonical
      have targetLocalCanonical : target.Canonical := by
        exact Region.Canonical.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals))
          (.mk materialLocals materialItems)
          (pinnedHostCanonical hostLocals hostItems
            (.mk materialLocals materialItems) sourceLocalCanonical)
          materialCanonical
      have sameNonempty : ∀ {wireSignature}
          (wire : Var outer wireSignature),
          raw.incidencePaths wire.index.val ≠ [] ↔
            target.incidencePaths wire.index.val ≠ [] := by
        intro wireSignature wire
        simpa only [raw, target, Region.adjoinAt, Region.incidencePaths,
          hostRename, materialRename, host, material, base, pinsRename,
          ItemSeq.renameWires_append, ItemSeq.append_assoc] using
          ItemSeq.incidencePaths_rotate_nonempty_iff host material
            (pin.append pin) wire.index.val 0
      have replacement := occurrence.context.replaceCanonical raw target
        rawCanonical' targetLocalCanonical sameNonempty
      let targetCanonical := replacement.1
      let rawEndpoint := occurrence.interface.withBody
        (occurrence.context.fill raw) rawCanonical' rawExternalTwoEnded'
      have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill target) :=
        rawEndpoint.externalTwoEnded_of_nonempty_iff
          (occurrence.context.fill target) replacement.2
      let targetEndpoint := occurrence.interface.withBody
        (occurrence.context.fill target) targetCanonical
          targetExternalTwoEnded
      let endpointIso : OpenDiagramIso rawEndpoint targetEndpoint :=
        OpenDiagram.withBody_iso rawCanonical' targetCanonical
          rawExternalTwoEnded' targetExternalTwoEnded
          (DiagramContext.fillIso occurrence.context presentation)
      have rawForward : Relation.TransGen Step source rawEndpoint := by
        simpa only [directOccurrence, pin, base, raw, rawEndpoint] using
          rawSteps.1
      have rawReverse : Relation.TransGen Step rawEndpoint source := by
        simpa only [directOccurrence, pin, base, raw, rawEndpoint] using
          rawSteps.2
      refine ⟨targetCanonical, targetExternalTwoEnded, ?_, ?_⟩
      · exact transGen_iso (OpenDiagramIso.refl source) rawForward endpointIso
      · exact transGen_iso endpointIso rawReverse
          (OpenDiagramIso.refl source)

private theorem pinnedHost_incidence_nonempty
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (wire : Var outer signature) :
    (Region.mk hostLocals
      (hostItems.append
        (contextPins outer hostLocals))).incidencePaths
          wire.index.val ≠ [] := by
  let embedded := wire.appendLeft hostLocals
  have pinsNonempty := contextPins_incidence_nonempty
    outer hostLocals embedded hostItems.length
  simp only [Region.incidencePaths, ItemSeq.incidencePaths_append,
    Nat.zero_add]
  exact List.append_ne_nil_of_right_ne_nil _ (by
    simpa only [embedded, Var.index_appendLeft] using pinsNonempty)

/-- Change only the adjoined material presentation beneath a host whose
existing syntax is canonical and incident at every inherited wire. -/
private noncomputable def supportedAdjoinOccurrence
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (afterCanonical : after.Canonical)
    (presentation : RegionIso (WireEquiv.refl (outer ++ hostLocals))
      before after) :
    Occurrence (Region.adjoinAt hostLocals hostItems after) source := by
  have targetLocalCanonical :
      (Region.adjoinAt hostLocals hostItems after).Canonical :=
    Region.Canonical.adjoinAt hostLocals hostItems after hostCanonical
      afterCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems before).incidencePaths
            wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have hostPositive : 0 <
        ((Region.mk hostLocals hostItems).incidencePaths
          wire.index.val).length :=
      List.length_pos_iff.mpr (hostNonempty wire)
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems before wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems after wire
    have beforeNonempty :
        (Region.adjoinAt hostLocals hostItems before).incidencePaths
          wire.index.val ≠ [] :=
      List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive beforeSublist.length_le)
    have afterNonempty :
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
          wire.index.val ≠ [] :=
      List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive afterSublist.length_le)
    exact ⟨fun _ => afterNonempty, fun _ => beforeNonempty⟩
  exact presentationOccurrence occurrence targetLocalCanonical sameNonempty
    (RegionIso.adjoinAt hostLocals hostItems presentation)

private theorem supportedAdjoinValidity
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (afterCanonical : after.Canonical) :
    (occurrence.context.fill
      (Region.adjoinAt hostLocals hostItems after)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems after)) := by
  have targetLocalCanonical :
      (Region.adjoinAt hostLocals hostItems after).Canonical :=
    Region.Canonical.adjoinAt hostLocals hostItems after hostCanonical
      afterCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems before).incidencePaths
            wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have hostPositive := List.length_pos_iff.mpr (hostNonempty wire)
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems before wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems after wire
    exact ⟨fun _ => List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive afterSublist.length_le),
      fun _ => List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive beforeSublist.length_le)⟩
  have replacement := occurrence.context.replaceCanonical _ _
    occurrence.sourceCanonical targetLocalCanonical sameNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Region.adjoinAt hostLocals hostItems before))
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  exact ⟨replacement.1,
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2⟩

private theorem extendHostCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (leading : Region (outer ++ hostLocals))
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (leadingCanonical : leading.Canonical) :
    (Region.mk (hostLocals ++ leading.locals)
      (Region.extendHostItems hostLocals hostItems leading)).Canonical := by
  cases leading with
  | mk leadingLocals leadingItems =>
      simpa only [Region.adjoinAt, Region.extendHostItems, Region.locals,
        Region.items] using
        Region.Canonical.adjoinAt hostLocals hostItems
          (Region.mk leadingLocals leadingItems) hostCanonical
          leadingCanonical

private theorem extendHost_incidence_nonempty
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (leading : Region (outer ++ hostLocals))
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    {signature} (wire : Var outer signature) :
    (Region.mk (hostLocals ++ leading.locals)
      (Region.extendHostItems hostLocals hostItems leading)).incidencePaths
        wire.index.val ≠ [] := by
  cases leading with
  | mk leadingLocals leadingItems =>
      have sublist := Region.incidencePaths_adjoinAt_host_sublist
        hostLocals hostItems (Region.mk leadingLocals leadingItems) wire
      have positive := List.length_pos_iff.mpr (hostNonempty wire)
      have targetPositive := Nat.lt_of_lt_of_le positive sublist.length_le
      simpa only [Region.adjoinAt, Region.extendHostItems, Region.locals,
        Region.items] using
        (List.length_pos_iff.mp targetPositive)

private noncomputable def flattenAdjoinOccurrence
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (first second : Region (outer ++ hostLocals))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems (first.conjoin second)) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical) :
    Occurrence
      (Region.adjoinAt (hostLocals ++ first.locals)
        (Region.extendHostItems hostLocals hostItems first)
        (second.renameWires
          (Region.adjoinHostWire outer hostLocals first.locals))) source := by
  let nextHostItems := Region.extendHostItems hostLocals hostItems first
  have nextHostCanonical :
      (Region.mk (hostLocals ++ first.locals) nextHostItems).Canonical :=
    extendHostCanonical hostLocals hostItems first hostCanonical firstCanonical
  have renamedSecondCanonical :
      (second.renameWires
        (Region.adjoinHostWire outer hostLocals first.locals)).Canonical :=
    (Region.Canonical.renameWires_iff second
      (Region.adjoinHostWire outer hostLocals first.locals)).mpr
        secondCanonical
  have targetLocalCanonical :
      (Region.adjoinAt (hostLocals ++ first.locals) nextHostItems
        (second.renameWires
          (Region.adjoinHostWire outer hostLocals first.locals))).Canonical :=
    Region.Canonical.adjoinAt (hostLocals ++ first.locals) nextHostItems _
      nextHostCanonical renamedSecondCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems
          (first.conjoin second)).incidencePaths wire.index.val ≠ [] ↔
        (Region.adjoinAt (hostLocals ++ first.locals) nextHostItems
          (second.renameWires
            (Region.adjoinHostWire outer hostLocals first.locals))).incidencePaths
              wire.index.val ≠ [] := by
    intro signature wire
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems (first.conjoin second) wire
    have beforePositive := Nat.lt_of_lt_of_le
      (List.length_pos_iff.mpr (hostNonempty wire)) beforeSublist.length_le
    have nextHostNonempty := extendHost_incidence_nonempty hostLocals
      hostItems first hostNonempty wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      (hostLocals ++ first.locals) nextHostItems
      (second.renameWires
        (Region.adjoinHostWire outer hostLocals first.locals)) wire
    have afterPositive := Nat.lt_of_lt_of_le
      (List.length_pos_iff.mpr nextHostNonempty) afterSublist.length_le
    exact ⟨fun _ => List.length_pos_iff.mp afterPositive,
      fun _ => List.length_pos_iff.mp beforePositive⟩
  exact presentationOccurrence occurrence targetLocalCanonical sameNonempty
    (RegionIso.adjoinAtConjoinLeft hostLocals hostItems first second)

private theorem identityBoundaryMaterial_scope
    (pattern : OpenDiagram arguments)
    (ports : Vars wires arguments) :
    ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (identityBoundary pattern) ports) := by
  constructor
  · intro _
    exact
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (identityBoundary pattern) ports
  · intro signature wire
    rw [instantiate_incidence_nonempty_iff,
      instantiate_incidence_nonempty_iff]
  · intro signature wire sourceRoot
    rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
    exact sourceRoot

/-- One selected instantiation in its exact inferred retained host is
bidirectionally equivalent to the same application through the ordered
identity boundary. The normalized combined endpoint and both validity proofs
are constructed internally. -/
theorem equatesIdentityBoundary
    {boundary outer arguments : List Sig}
    (pattern : OpenDiagram arguments)
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (ports : Vars (outer ++ hostLocals) arguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports)) source) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                (identityBoundary pattern) ports))),
        Equates occurrence
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))
          targetCanonical targetExternalTwoEnded := by
  let sourceMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports
  let targetMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports
  let sourceRegion := Region.adjoinAt hostLocals hostItems sourceMaterial
  let targetRegion := Region.adjoinAt hostLocals hostItems targetMaterial
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have regionScope : ScopePreservation sourceRegion targetRegion := by
    exact adjoinAt_preserves_scope hostLocals hostItems sourceMaterial
      targetMaterial (identityBoundaryMaterial_scope pattern ports)
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let targetCanonical := replacement.1
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  let targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2
  refine ⟨targetCanonical, targetExternalTwoEnded, ?_⟩
  by_cases nonempty : outer ++ hostLocals ≠ []
  · obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
      sourceMaterial (by simpa only [sourceMaterial] using occurrence)
        nonempty
    let pinnedItems := hostItems.append (contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context pinnedSource
        pinnedSourceCanonical pinnedSourceExternalTwoEnded
    let description := exposureDescriptionWithHost pattern hostLocals
      pinnedItems ports
    have sourceEq : description.source = pinnedSource := by
      simpa only [description, pinnedSource] using
        exposureDescriptionWithHost_source pattern hostLocals pinnedItems ports
    let exposureOccurrence : Occurrence description.source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := {
      interface := pinnedSourceOccurrence.interface
      context := pinnedSourceOccurrence.context
      sourceCanonical := by
        rw [sourceEq]
        exact pinnedSourceOccurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro signature wire
        rw [sourceEq]
        exact pinnedSourceOccurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq] using pinnedSourceOccurrence.host_iso
    }
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
      simpa only [description, exposureDescriptionWithHost,
        Rule.Erasure.Description.target, pinnedItems] using canonical
    have erasedNonempty : ∀ {signature} (wire : Var outer signature),
        description.target.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      simpa only [description, exposureDescriptionWithHost,
        Rule.Erasure.Description.target, pinnedItems] using
        pinnedHost_incidence_nonempty hostLocals hostItems wire
    have pinnedSourceNonempty : ∀ {signature}
        (wire : Var outer signature),
        pinnedSource.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      have hostPositive := List.length_pos_iff.mpr (erasedNonempty wire)
      have sublist := Region.incidencePaths_adjoinAt_host_sublist
        hostLocals pinnedItems sourceMaterial wire
      exact List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive sublist.length_le)
    have erasedSameNonempty : ∀ {signature} (wire : Var outer signature),
        pinnedSource.incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact ⟨fun _ => erasedNonempty wire,
        fun _ => pinnedSourceNonempty wire⟩
    have erasedReplacement := occurrence.context.replaceCanonical
      pinnedSource description.target pinnedSourceCanonical
        erasedLocalCanonical erasedSameNonempty
    let pinnedSourceEndpoint := occurrence.interface.withBody
      (occurrence.context.fill pinnedSource) pinnedSourceCanonical
        pinnedSourceExternalTwoEnded
    have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill description.target) :=
      pinnedSourceEndpoint.externalTwoEnded_of_nonempty_iff _
        erasedReplacement.2
    obtain ⟨materialCanonical, exposedCanonical,
        exposedExternalTwoEnded, exposedEquates⟩ :=
      Erasure.Exposure.equates description exposureOccurrence
        erasedReplacement.1 erasedExternalTwoEnded
    have exposedEq :
        Erasure.Exposure.exposedRegion description materialCanonical =
          Region.adjoinAt hostLocals pinnedItems targetMaterial := by
      simpa only [description, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern hostLocals
          pinnedItems ports materialCanonical
    let targetOccurrence : Occurrence targetRegion
        (occurrence.interface.withBody
          (occurrence.context.fill targetRegion) targetCanonical
            targetExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context targetRegion
        targetCanonical targetExternalTwoEnded
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        targetPins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
      targetMaterial (by simpa only [targetRegion, targetMaterial] using
        targetOccurrence) nonempty
    have forwardExposure : Relation.ReflTransGen Step
        pinnedSourceEndpoint
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetCanonical pinnedTargetExternalTwoEnded) := by
      simpa only [exposureOccurrence, pinnedSourceOccurrence,
        exactOccurrence, sourceEq, exposedEq, pinnedSourceEndpoint] using
        exposedEquates.1
    have reverseExposure : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetCanonical pinnedTargetExternalTwoEnded)
        pinnedSourceEndpoint := by
      simpa only [exposureOccurrence, pinnedSourceOccurrence,
        exactOccurrence, sourceEq, exposedEq, pinnedSourceEndpoint] using
        exposedEquates.2
    have forwardPins : Relation.TransGen Step source pinnedSourceEndpoint := by
      simpa only [pinnedSourceEndpoint, pinnedSource, pinnedItems,
        sourceMaterial] using sourcePins.1
    have reversePins : Relation.TransGen Step pinnedSourceEndpoint source := by
      simpa only [pinnedSourceEndpoint, pinnedSource, pinnedItems,
        sourceMaterial] using sourcePins.2
    have unpinForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetCanonical pinnedTargetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill targetRegion) targetCanonical
            targetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, targetRegion,
        pinnedItems, targetMaterial] using targetPins.2
    have unpinReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill targetRegion) targetCanonical
            targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetCanonical pinnedTargetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, targetRegion,
        pinnedItems, targetMaterial] using targetPins.1
    refine ⟨?_, ?_⟩
    · have core := forwardPins.reflTransGen forwardExposure
      have strictForward := core.trans unpinForward
      exact (show StrictEquates occurrence targetRegion targetCanonical
        targetExternalTwoEnded from
          ⟨strictForward,
            (unpinReverse.reflTransGen reverseExposure).trans reversePins⟩).toEquates.1
    · have core := unpinReverse.reflTransGen reverseExposure
      have strictReverse := core.trans reversePins
      exact (show StrictEquates occurrence targetRegion targetCanonical
        targetExternalTwoEnded from
          ⟨(forwardPins.reflTransGen forwardExposure).trans unpinForward,
            strictReverse⟩).toEquates.2
  · have empty : outer ++ hostLocals = [] :=
      Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    let description := exposureDescriptionWithHost pattern [] hostItems ports
    have sourceEq : description.source = sourceRegion := by
      simpa only [description, sourceRegion, sourceMaterial] using
        exposureDescriptionWithHost_source pattern [] hostItems ports
    let exposureOccurrence : Occurrence description.source source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := by
        rw [sourceEq]
        exact occurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro signature wire
        rw [sourceEq]
        exact occurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq, sourceRegion, sourceMaterial] using
          occurrence.host_iso
    }
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := pinnedHostCanonical ([] : List Sig) hostItems
        sourceMaterial sourceLocalCanonical
      simpa only [description, exposureDescriptionWithHost,
        Rule.Erasure.Description.target, contextPins, allPins,
        List.nil_append, ItemSeq.pinWires, ItemSeq.nil_append,
        ItemSeq.append_nil] using canonical
    have erasedSameNonempty : ∀ {signature} (wire : Var [] signature),
        sourceRegion.incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact Fin.elim0 wire.index
    have erasedReplacement := occurrence.context.replaceCanonical
      sourceRegion description.target occurrence.sourceCanonical
        erasedLocalCanonical erasedSameNonempty
    have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill description.target) :=
      sourceEndpoint.externalTwoEnded_of_nonempty_iff _
        erasedReplacement.2
    obtain ⟨materialCanonical, exposedCanonical,
        exposedExternalTwoEnded, exposedEquates⟩ :=
      Erasure.Exposure.equates description exposureOccurrence
        erasedReplacement.1 erasedExternalTwoEnded
    have exposedEq :
        Erasure.Exposure.exposedRegion description materialCanonical =
          targetRegion := by
      simpa only [description, targetRegion, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern [] hostItems ports
          materialCanonical
    simpa only [Equates, exposureOccurrence, sourceEq, exposedEq,
      sourceRegion, sourceMaterial, targetRegion, targetMaterial] using
      exposedEquates

private theorem strictEquates_of_equates
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (equivalent : Equates occurrence after targetCanonical
      targetExternalTwoEnded) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  have loop := StrictEquates.refl occurrence
  have sourceLoop : Relation.TransGen Step source source :=
    loop.1.trans loop.2
  exact ⟨sourceLoop.reflTransGen equivalent.1,
    equivalent.2.transGen sourceLoop⟩

mutual
  private noncomputable def normalizedRegionStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected sourceRegion result)
      (sites : RegionSites operation data evidence)
      (hasSelection : regionHasSelection sites = true) :
      ∀ (outer : List Sig) (rename : WireRenaming common outer)
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence (result.renameWires rename) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1)).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1))),
        StrictEquates occurrence
          (Region.renameWires rename (normalizedRegion pattern evidence sites).1)
          targetCanonical (fun wire => targetExternalTwoEnded wire) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        intro outer rename boundary source occurrence targetCanonical
          targetExternalTwoEnded
        let childRename := rename.appendRight locals
        let childHostItems : ItemSeq (outer ++ locals) := .nil
        change Occurrence
          ((Region.adjoinAt locals .nil childResult).renameWires rename) source
          at occurrence
        have sourceEq := Region.renameWires_adjoinAt_nil childResult rename
        have childSourceCanonical :
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)).Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            ((Region.adjoinAt locals .nil childResult).renameWires rename).incidencePaths
                  wire.index.val ≠ [] ↔
              (Region.adjoinAt locals childHostItems
                (childResult.renameWires childRename)).incidencePaths
                  wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let childOccurrence : Occurrence
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)) source :=
          presentationOccurrence occurrence childSourceCanonical sourceNonempty
            (by
              simpa only [childHostItems, childRename] using
                RegionIso.renameWiresAdjoinAtNil childResult rename)
        let normalizedChild :=
          (normalizedItems pattern childEvidence childSites).1
        let targetBefore :=
          (Region.adjoinAt locals (.nil : ItemSeq (common ++ locals))
            normalizedChild).renameWires rename
        let targetAfter := Region.adjoinAt locals childHostItems
          (normalizedChild.renameWires childRename)
        have targetEq : targetBefore = targetAfter := by
          simpa only [targetBefore, targetAfter, childHostItems, childRename] using
            Region.renameWires_adjoinAt_nil normalizedChild rename
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))).Canonical := by
          exact targetReplacement.1
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childSelection : itemsHaveSelection childSites = true := by
          simpa only [regionHasSelection] using hasSelection
        have folded := normalizedItemsStrict pattern
          childEvidence childSites childSelection locals childRename childHostItems
          childOccurrence childTargetCanonical childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          simpa only [targetAfter, targetBefore, childHostItems, childRename] using
            (RegionIso.renameWiresAdjoinAtNil normalizedChild rename).symm
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill targetAfter)
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso childTargetCanonical targetCanonical
            childTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso folded finalIso
        simpa only [normalizedRegion, normalizedChild, targetBefore, targetAfter,
          childHostItems, childRename, childOccurrence] using presented
  termination_by 5 * sizeOf sites

  private noncomputable def normalizedItemsStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          (result.renameWires rename)) source)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename (normalizedItems pattern evidence sites).1))
        targetCanonical (fun wire => targetExternalTwoEnded wire) := by
    let sourceMaterial := result.renameWires rename
    let targetMaterial :=
      (Region.renameWires rename (normalizedItems pattern evidence sites).1)
    by_cases nonempty : outer ++ hostLocals ≠ []
    · exact (by
    obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems sourceMaterial occurrence nonempty
    let pinnedItems := hostItems.append
      (contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context pinnedSource
        pinnedSourceCanonical pinnedSourceExternalTwoEnded
    have sourceLocalCanonical :
        (Region.adjoinAt hostLocals hostItems sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have pinnedHostCanonical :
        (Region.mk hostLocals pinnedItems).Canonical := by
      exact pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
    have pinnedHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk hostLocals pinnedItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact pinnedHost_incidence_nonempty hostLocals hostItems wire
    have targetLocalCanonical :
        (Region.adjoinAt hostLocals hostItems targetMaterial).Canonical :=
      occurrence.context.holeCanonical _ targetCanonical
    have targetMaterialCanonical : targetMaterial.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals hostItems _
        targetLocalCanonical
    have pinnedTargetValidity := supportedAdjoinValidity hostLocals
      pinnedItems pinnedSourceOccurrence pinnedHostCanonical
      pinnedHostNonempty targetMaterialCanonical
    have folded := normalizedItemsSupportedStrict pattern evidence
      sites hasSelection outer hostLocals rename pinnedItems pinnedSourceOccurrence
      pinnedHostCanonical pinnedHostNonempty pinnedTargetValidity.1
      pinnedTargetValidity.2
    let targetOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems targetMaterial)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context _
        targetCanonical targetExternalTwoEnded
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        targetPins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems targetMaterial targetOccurrence nonempty
    have forwardPins : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.1
    have reversePins : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) source := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.2
    have middleForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.1
    have middleReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.2
    have unpinForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.2
    have unpinReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.1
    exact ⟨(forwardPins.trans middleForward).trans unpinForward,
      (unpinReverse.trans middleReverse).trans reversePins⟩)
    · have empty : outer ++ hostLocals = [] :=
        Classical.not_not.mp nonempty
      have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
      have localsEmpty : hostLocals = [] :=
        (List.append_eq_nil_iff.mp empty).2
      subst outer
      subst hostLocals
      have sourceLocalCanonical :
          (Region.adjoinAt [] hostItems sourceMaterial).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have hostCanonical : (Region.mk [] hostItems).Canonical := by
        have canonical := pinnedHostCanonical ([] : List Sig) hostItems
          sourceMaterial sourceLocalCanonical
        simpa only [contextPins, allPins, List.nil_append,
          ItemSeq.pinWires, ItemSeq.nil_append, ItemSeq.append_nil] using
          canonical
      have hostNonempty : ∀ {signature} (wire : Var [] signature),
          (Region.mk [] hostItems).incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        exact Fin.elim0 wire.index
      have folded := normalizedItemsSupportedStrict pattern evidence sites
        hasSelection [] [] rename hostItems occurrence hostCanonical
          hostNonempty targetCanonical targetExternalTwoEnded
      simpa only [sourceMaterial, targetMaterial] using folded
  termination_by 5 * sizeOf sites + 4

  private noncomputable def normalizedItemsSupportedStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (_hostCanonical : (Region.mk hostLocals hostItems).Canonical)
        (_hostNonempty : ∀ {signature} (wire : Var outer signature),
          (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItems pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .nil _ => by
        simp only [itemsHaveSelection, Bool.false_eq_true] at hasSelection
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          hostCanonical hostNonempty targetCanonical targetExternalTwoEnded
        let itemBefore := itemResult.renameWires rename
        let tailBefore := tailResult.renameWires rename
        let itemAfter :=
          (Region.renameWires rename (normalizedItem pattern itemEvidence itemSites).1)
        let tailAfter :=
          (Region.renameWires rename (normalizedItems pattern tailEvidence tailSites).1)
        change Occurrence
          (Region.adjoinAt hostLocals hostItems
            ((itemResult.conjoin tailResult).renameWires rename)) source
          at occurrence
        have sourceBeforeCanonical :
            ((itemResult.conjoin tailResult).renameWires rename).Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
        have sourceMaterialCanonical :
            (itemBefore.conjoin tailBefore).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact sourceBeforeCanonical
        let sourceOccurrence : Occurrence
            (Region.adjoinAt hostLocals hostItems
              (itemBefore.conjoin tailBefore)) source :=
          supportedAdjoinOccurrence hostLocals hostItems occurrence hostCanonical
            hostNonempty sourceMaterialCanonical (by
              simpa only [itemBefore, tailBefore] using
                RegionIso.renameWiresConjoin itemResult tailResult rename)
        have itemBeforeCanonical :=
          canonical_left_of_conjoin sourceMaterialCanonical
        have tailBeforeCanonical :=
          canonical_right_of_conjoin sourceMaterialCanonical
        let normalizedHead := (normalizedItem pattern itemEvidence itemSites).1
        let normalizedTail := (normalizedItems pattern tailEvidence tailSites).1
        let targetBefore :=
          (normalizedHead.conjoin normalizedTail).renameWires rename
        change (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical
          at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetBefore))
          at targetExternalTwoEnded
        have presentedTargetCanonical :
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            sourceOccurrence.interface.boundaryWire
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        have targetBeforeCanonical : targetBefore.Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ targetCanonical)
        have targetMaterialCanonical :
            (itemAfter.conjoin tailAfter).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact targetBeforeCanonical
        have itemAfterCanonical :=
          canonical_left_of_conjoin targetMaterialCanonical
        have tailAfterCanonical :=
          canonical_right_of_conjoin targetMaterialCanonical
        by_cases itemSelected : itemHasSelection itemSites = true
        · by_cases tailSelected : itemsHaveSelection tailSites = true
          · exact (by
        have itemPhaseValidity := supportedAdjoinValidity hostLocals hostItems
          sourceOccurrence hostCanonical hostNonempty
          (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
        have itemPhase := normalizedItemWithTailStrict pattern
          itemEvidence itemSites itemSelected hostLocals rename hostItems tailBefore
          sourceOccurrence hostCanonical hostNonempty itemBeforeCanonical
          tailBeforeCanonical itemAfterCanonical itemPhaseValidity.1
          itemPhaseValidity.2
        let afterItem := Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tailBefore)
        let afterItemOccurrence : Occurrence afterItem
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          exactOccurrence sourceOccurrence.interface sourceOccurrence.context afterItem
            itemPhaseValidity.1 itemPhaseValidity.2
        let flattened := flattenAdjoinOccurrence hostLocals hostItems
          itemAfter tailBefore afterItemOccurrence hostCanonical hostNonempty
          itemAfterCanonical tailBeforeCanonical
        let nextHostItems := Region.extendHostItems hostLocals hostItems
          itemAfter
        let hostWire :=
          Region.adjoinHostWire outer hostLocals itemAfter.locals
        let nextRename := WireRenaming.comp
          hostWire rename
        have nextHostCanonical := extendHostCanonical hostLocals hostItems
          itemAfter hostCanonical itemAfterCanonical
        have nextHostNonempty : ∀ {signature}
            (wire : Var outer signature),
            (Region.mk (hostLocals ++ itemAfter.locals) nextHostItems).incidencePaths
              wire.index.val ≠ [] := by
          intro signature wire
          exact extendHost_incidence_nonempty hostLocals hostItems itemAfter
            hostNonempty wire
        have tailResultCanonical : tailResult.Canonical :=
          (Region.Canonical.renameWires_iff tailResult rename).mp
            tailBeforeCanonical
        have alignedTailCanonical :
            (tailResult.renameWires nextRename).Canonical :=
          (Region.Canonical.renameWires_iff tailResult nextRename).mpr
            tailResultCanonical
        let alignedFlattened : Occurrence
            (Region.adjoinAt (hostLocals ++ itemAfter.locals) nextHostItems
              (tailResult.renameWires nextRename))
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          supportedAdjoinOccurrence (hostLocals ++ itemAfter.locals)
            nextHostItems flattened nextHostCanonical nextHostNonempty
            alignedTailCanonical (by
              simpa only [tailBefore, hostWire, nextRename] using
                RegionIso.renameWiresComp tailResult rename hostWire)
        have normalizedTailCanonical : normalizedTail.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail rename).mp
            tailAfterCanonical
        let flatTargetMaterial := normalizedTail.renameWires nextRename
        have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
            normalizedTailCanonical
        have tailTargetValidity := supportedAdjoinValidity
          (hostLocals ++ itemAfter.locals) nextHostItems alignedFlattened
          nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
        have tailPhase := normalizedItemsSupportedStrict pattern
          tailEvidence tailSites tailSelected outer
          (hostLocals ++ itemAfter.locals) nextRename
          nextHostItems alignedFlattened nextHostCanonical nextHostNonempty
          tailTargetValidity.1 tailTargetValidity.2
        let flatTarget := Region.adjoinAt
          (hostLocals ++ itemAfter.locals) nextHostItems
          flatTargetMaterial
        let flatTargetEndpoint := alignedFlattened.interface.withBody
          (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
            tailTargetValidity.2
        have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
            (Region.adjoinAt hostLocals hostItems targetBefore) := by
          exact (RegionIso.adjoinAt (hostLocals ++ itemAfter.locals)
            nextHostItems (by
            simpa only [flatTargetMaterial, tailAfter, normalizedTail,
              nextRename, hostWire] using
                (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
            ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemAfter
              tailAfter).symm.trans
              (RegionIso.adjoinAt hostLocals hostItems (by
                simpa only [itemAfter, tailAfter, normalizedHead,
                  normalizedTail, targetBefore] using
                  (RegionIso.renameWiresConjoin normalizedHead normalizedTail rename).symm)))
        have finalIso : OpenDiagramIso flatTargetEndpoint
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems
                  targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso tailTargetValidity.1
            presentedTargetCanonical tailTargetValidity.2
            presentedTargetExternalTwoEnded
            (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
        have tailPhase' : StrictEquates alignedFlattened
            (Region.adjoinAt hostLocals hostItems targetBefore)
            presentedTargetCanonical presentedTargetExternalTwoEnded :=
          StrictEquates.targetIso tailPhase finalIso
        have itemPhase' : StrictEquates sourceOccurrence afterItem
            itemPhaseValidity.1 itemPhaseValidity.2 := by
          simpa only [afterItem, itemBefore, tailBefore, itemAfter,
            sourceOccurrence] using itemPhase
        have combined := StrictEquates.trans
          (targetExternalTwoEnded := presentedTargetExternalTwoEnded)
          itemPhase' tailPhase'
        have outputIso : OpenDiagramIso
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl _)
        have exactCombined : StrictEquates occurrence
            (Region.adjoinAt hostLocals hostItems targetBefore)
            targetCanonical targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) combined.1 outputIso,
            transGen_iso outputIso combined.2 (OpenDiagramIso.refl source)⟩
        simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
          sourceOccurrence, afterItem, afterItemOccurrence, flattened,
          alignedFlattened, nextHostItems, hostWire, nextRename,
          flatTargetMaterial, flatTarget, flatTargetEndpoint,
          normalizedHead, normalizedTail, targetBefore, normalizedItems]
          using exactCombined)
          · have tailNone : itemsHaveSelection tailSites = false := by
              cases selected : itemsHaveSelection tailSites with
              | false => rfl
              | true => exact False.elim (tailSelected selected)
            have normalizedTailEq : normalizedTail = tailResult := by
              simpa only [normalizedTail] using
                normalizedItems_eq_of_noSelection pattern tailEvidence
                  tailSites tailNone
            have tailAfterEq : tailAfter = tailBefore := by
              change Region.renameWires rename normalizedTail =
                Region.renameWires rename tailResult
              rw [normalizedTailEq]
            have itemPhaseValidity := supportedAdjoinValidity hostLocals
              hostItems sourceOccurrence hostCanonical hostNonempty
              (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
            have itemPhase := normalizedItemWithTailStrict pattern
              itemEvidence itemSites itemSelected hostLocals rename hostItems
              tailBefore sourceOccurrence hostCanonical hostNonempty
              itemBeforeCanonical tailBeforeCanonical itemAfterCanonical
              itemPhaseValidity.1 itemPhaseValidity.2
            let afterItem := Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tailBefore)
            have itemPhase' : StrictEquates sourceOccurrence afterItem
                itemPhaseValidity.1 itemPhaseValidity.2 := by
              simpa only [afterItem, itemBefore, tailBefore, itemAfter,
                sourceOccurrence] using itemPhase
            have materialIso : RegionIso
                (WireEquiv.refl (outer ++ hostLocals))
                (itemAfter.conjoin tailBefore) targetBefore := by
              rw [← tailAfterEq]
              simpa only [itemAfter, tailAfter, normalizedHead,
                normalizedTail, targetBefore] using
                (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                  rename).symm
            have finalBodyIso : RegionIso (WireEquiv.refl outer) afterItem
                (Region.adjoinAt hostLocals hostItems targetBefore) := by
              exact RegionIso.adjoinAt hostLocals hostItems materialIso
            have finalIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill afterItem)
                  itemPhaseValidity.1 itemPhaseValidity.2)
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded) :=
              OpenDiagram.withBody_iso itemPhaseValidity.1
                presentedTargetCanonical itemPhaseValidity.2
                presentedTargetExternalTwoEnded
                (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
            have presented := StrictEquates.targetIso itemPhase' finalIso
            have outputIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded)
                (occurrence.interface.withBody
                  (occurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  targetCanonical targetExternalTwoEnded) :=
              OpenDiagram.withBody_iso presentedTargetCanonical
                targetCanonical presentedTargetExternalTwoEnded
                targetExternalTwoEnded (RegionIso.refl _)
            have exactPresented : StrictEquates occurrence
                (Region.adjoinAt hostLocals hostItems targetBefore)
                targetCanonical targetExternalTwoEnded :=
              ⟨transGen_iso (OpenDiagramIso.refl source) presented.1
                  outputIso,
                transGen_iso outputIso presented.2
                  (OpenDiagramIso.refl source)⟩
            simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
              sourceOccurrence, afterItem, normalizedHead, normalizedTail,
              targetBefore, normalizedItems] using exactPresented
        · have itemNone : itemHasSelection itemSites = false := by
            cases selected : itemHasSelection itemSites with
            | false => rfl
            | true => exact False.elim (itemSelected selected)
          have tailSelected : itemsHaveSelection tailSites = true := by
            cases selected : itemsHaveSelection tailSites with
            | true => rfl
            | false =>
                simp only [itemsHaveSelection, itemNone, selected,
                  Bool.false_or, Bool.false_eq_true] at hasSelection
          have normalizedHeadEq : normalizedHead = itemResult := by
            simpa only [normalizedHead] using
              normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
                itemNone
          have itemAfterEq : itemAfter = itemBefore := by
            change Region.renameWires rename normalizedHead =
              Region.renameWires rename itemResult
            rw [normalizedHeadEq]
          let flattened := flattenAdjoinOccurrence hostLocals hostItems
            itemBefore tailBefore sourceOccurrence hostCanonical hostNonempty
            itemBeforeCanonical tailBeforeCanonical
          let nextHostItems := Region.extendHostItems hostLocals hostItems
            itemBefore
          let hostWire :=
            Region.adjoinHostWire outer hostLocals itemBefore.locals
          let nextRename := WireRenaming.comp hostWire rename
          have nextHostCanonical := extendHostCanonical hostLocals hostItems
            itemBefore hostCanonical itemBeforeCanonical
          have nextHostNonempty : ∀ {signature}
              (wire : Var outer signature),
              (Region.mk (hostLocals ++ itemBefore.locals)
                nextHostItems).incidencePaths wire.index.val ≠ [] := by
            intro signature wire
            exact extendHost_incidence_nonempty hostLocals hostItems itemBefore
              hostNonempty wire
          have tailResultCanonical : tailResult.Canonical :=
            (Region.Canonical.renameWires_iff tailResult rename).mp
              tailBeforeCanonical
          have alignedTailCanonical :
              (tailResult.renameWires nextRename).Canonical :=
            (Region.Canonical.renameWires_iff tailResult nextRename).mpr
              tailResultCanonical
          let alignedFlattened : Occurrence
              (Region.adjoinAt (hostLocals ++ itemBefore.locals)
                nextHostItems (tailResult.renameWires nextRename)) source :=
            supportedAdjoinOccurrence (hostLocals ++ itemBefore.locals)
              nextHostItems flattened nextHostCanonical nextHostNonempty
              alignedTailCanonical (by
                simpa only [tailBefore, hostWire, nextRename] using
                  RegionIso.renameWiresComp tailResult rename hostWire)
          have normalizedTailCanonical : normalizedTail.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail rename).mp
              tailAfterCanonical
          let flatTargetMaterial := normalizedTail.renameWires nextRename
          have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
              normalizedTailCanonical
          have tailTargetValidity := supportedAdjoinValidity
            (hostLocals ++ itemBefore.locals) nextHostItems alignedFlattened
            nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
          have tailPhase := normalizedItemsSupportedStrict pattern
            tailEvidence tailSites tailSelected outer
            (hostLocals ++ itemBefore.locals) nextRename nextHostItems
            alignedFlattened nextHostCanonical nextHostNonempty
            tailTargetValidity.1 tailTargetValidity.2
          let flatTarget := Region.adjoinAt
            (hostLocals ++ itemBefore.locals) nextHostItems flatTargetMaterial
          let flatTargetEndpoint := alignedFlattened.interface.withBody
            (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
              tailTargetValidity.2
          have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
              (Region.adjoinAt hostLocals hostItems targetBefore) := by
            exact (RegionIso.adjoinAt (hostLocals ++ itemBefore.locals)
              nextHostItems (by
                simpa only [flatTargetMaterial, tailAfter, normalizedTail,
                  nextRename, hostWire] using
                    (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
              ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemBefore
                tailAfter).symm.trans
                (RegionIso.adjoinAt hostLocals hostItems (by
                  rw [← itemAfterEq]
                  simpa only [itemAfter, tailAfter, normalizedHead,
                    normalizedTail, targetBefore] using
                    (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                      rename).symm)))
          have finalIso : OpenDiagramIso flatTargetEndpoint
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical
                  presentedTargetExternalTwoEnded) :=
            OpenDiagram.withBody_iso tailTargetValidity.1
              presentedTargetCanonical tailTargetValidity.2
              presentedTargetExternalTwoEnded
              (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
          have tailPhase' : StrictEquates alignedFlattened
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded :=
            StrictEquates.targetIso tailPhase finalIso
          have presented : StrictEquates sourceOccurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded := by
            simpa only [sourceOccurrence, flattened, alignedFlattened,
              supportedAdjoinOccurrence] using tailPhase'
          have outputIso : OpenDiagramIso
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical presentedTargetExternalTwoEnded)
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                targetCanonical targetExternalTwoEnded) :=
            OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
              presentedTargetExternalTwoEnded targetExternalTwoEnded
              (RegionIso.refl _)
          have exactPresented : StrictEquates occurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              targetCanonical targetExternalTwoEnded :=
            ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
              transGen_iso outputIso presented.2
                (OpenDiagramIso.refl source)⟩
          simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
            sourceOccurrence, flattened, alignedFlattened, nextHostItems,
            hostWire, nextRename, flatTargetMaterial, flatTarget,
            flatTargetEndpoint, normalizedHead, normalizedTail, targetBefore,
            normalizedItems] using exactPresented
  termination_by 5 * sizeOf sites + 3

  private noncomputable def normalizedItemWithTailStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      (tail : Region (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          ((result.renameWires rename).conjoin tail)) source)
      (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
      (hostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
      (itemBeforeCanonical : (result.renameWires rename).Canonical)
      (tailCanonical : tail.Canonical)
      (itemAfterCanonical :
        (Region.renameWires rename
          (normalizedItem pattern evidence sites).1).Canonical)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin
                tail))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin tail)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          ((Region.renameWires rename
            (normalizedItem pattern evidence sites).1).conjoin tail))
        targetCanonical targetExternalTwoEnded := by
    let itemBefore := result.renameWires rename
    let itemAfter :=
      (Region.renameWires rename (normalizedItem pattern evidence sites).1)
    have swappedCanonical : (tail.conjoin itemBefore).Canonical :=
      canonical_conjoin tailCanonical itemBeforeCanonical
    let swapped := supportedAdjoinOccurrence hostLocals hostItems occurrence
      hostCanonical hostNonempty swappedCanonical
      (RegionIso.conjoinComm itemBefore tail)
    let flattened := flattenAdjoinOccurrence hostLocals hostItems tail
      itemBefore swapped hostCanonical hostNonempty tailCanonical
      itemBeforeCanonical
    let nextHostItems := Region.extendHostItems hostLocals hostItems tail
    let hostWire := Region.adjoinHostWire outer hostLocals tail.locals
    let nextRename := WireRenaming.comp
      hostWire rename
    have nextHostCanonical := extendHostCanonical hostLocals hostItems tail
      hostCanonical tailCanonical
    have nextHostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk (hostLocals ++ tail.locals) nextHostItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact extendHost_incidence_nonempty hostLocals hostItems tail
        hostNonempty wire
    have resultCanonical : result.Canonical :=
      (Region.Canonical.renameWires_iff result rename).mp itemBeforeCanonical
    have alignedSourceCanonical : (result.renameWires nextRename).Canonical :=
      (Region.Canonical.renameWires_iff result nextRename).mpr resultCanonical
    let alignedFlattened : Occurrence
        (Region.adjoinAt (hostLocals ++ tail.locals) nextHostItems
          (result.renameWires nextRename)) source :=
      supportedAdjoinOccurrence (hostLocals ++ tail.locals) nextHostItems
        flattened nextHostCanonical nextHostNonempty alignedSourceCanonical (by
          simpa only [itemBefore, hostWire, nextRename] using
            RegionIso.renameWiresComp result rename hostWire)
    let normalized := (normalizedItem pattern evidence sites).1
    have normalizedCanonical : normalized.Canonical :=
      (Region.Canonical.renameWires_iff normalized rename).mp
        itemAfterCanonical
    let flatTargetMaterial := normalized.renameWires nextRename
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (Region.Canonical.renameWires_iff normalized nextRename).mpr
        normalizedCanonical
    have flatTargetValidity := supportedAdjoinValidity
      (hostLocals ++ tail.locals) nextHostItems alignedFlattened
      nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
    have core := normalizedItemStrict pattern evidence sites hasSelection
      outer (hostLocals ++ tail.locals) nextRename nextHostItems alignedFlattened
      flatTargetValidity.1 flatTargetValidity.2
    let flatTarget := Region.adjoinAt (hostLocals ++ tail.locals)
      nextHostItems flatTargetMaterial
    let flatEndpoint := alignedFlattened.interface.withBody
      (alignedFlattened.context.fill flatTarget) flatTargetValidity.1
        flatTargetValidity.2
    have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
        (Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tail)) := by
      exact (RegionIso.adjoinAt (hostLocals ++ tail.locals) nextHostItems (by
        simpa only [flatTargetMaterial, itemAfter, normalized, nextRename,
          hostWire] using
            (RegionIso.renameWiresComp normalized rename hostWire).symm)).trans
        ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems tail
          itemAfter).symm.trans
          (RegionIso.adjoinAt hostLocals hostItems
            (RegionIso.conjoinComm tail itemAfter)))
    have presentedTargetCanonical :
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))).Canonical := by
      exact targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        alignedFlattened.interface.boundaryWire
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))) := by
      intro signature wire
      exact targetExternalTwoEnded wire
    have finalIso : OpenDiagramIso flatEndpoint
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tail))) presentedTargetCanonical
          presentedTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso flatTargetValidity.1 presentedTargetCanonical
        flatTargetValidity.2 presentedTargetExternalTwoEnded
        (DiagramContext.fillIso alignedFlattened.context finalBodyIso)
    have presented : StrictEquates alignedFlattened
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        presentedTargetCanonical presentedTargetExternalTwoEnded :=
      StrictEquates.targetIso core finalIso
    have outputIso : OpenDiagramIso
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded (RegionIso.refl _)
    have exactPresented : StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        targetCanonical targetExternalTwoEnded :=
      ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
        transGen_iso outputIso presented.2 (OpenDiagramIso.refl source)⟩
    simpa only [itemBefore, itemAfter, swapped, flattened, alignedFlattened,
      nextHostItems, hostWire, nextRename, normalized, flatTargetMaterial,
      flatTarget, flatEndpoint] using exactPresented
  termination_by 5 * sizeOf sites + 2

  private noncomputable def normalizedItemStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItem pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .atom head ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | .selectedAtom ports _ => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let mappedPorts := ports.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedPorts
        let sourceHostBefore := Region.adjoinAt hostLocals hostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals hostItems sourceAfter
        change Occurrence sourceHostBefore source at occurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedPorts, instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty
            (RegionIso.adjoinAt hostLocals hostItems
              (instantiateRenameIso pattern ports rename))
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports).renameWires rename)
        let targetAfter := Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) mappedPorts)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, mappedPorts,
            instantiate_renameWires]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        obtain ⟨ownedTargetCanonical, ownedTargetExternalTwoEnded,
            equivalent⟩ :=
          equatesIdentityBoundary pattern mappedPorts presentedOccurrence
        have strict := strictEquates_of_equates presentedOccurrence equivalent
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore :=
          RegionIso.adjoinAt hostLocals hostItems
            (instantiateRenameIso (identityBoundary pattern) ports rename).symm
        have finalIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              ownedTargetCanonical ownedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso ownedTargetCanonical targetCanonical
            ownedTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso strict finalIso
        simpa only [normalizedItem, targetBefore, sourceHostBefore,
          sourceBefore] using presented
    | .identity signature arity ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let appendNil : WireRenaming common (common ++ []) :=
          ⟨fun wire => wire.appendLeft []⟩
        let materialRename := Region.adjoinMaterialWire outer hostLocals []
        let childRename := WireRenaming.comp materialRename
          (WireRenaming.comp (rename.appendRight []) appendNil)
        let retained := hostItems.renameWires
          (Region.adjoinHostWire outer hostLocals [])
        let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
          .cut (hostLocals ++ []) retained .nil .hole
        have childRename_eq (region : Region common) :
            Region.renameWires materialRename
                (Region.renameWires (rename.appendRight [])
                  (Region.renameWires appendNil region)) =
              Region.renameWires childRename region := by
          rw [Region.renameWires_comp, Region.renameWires_comp]
          apply congrArg (fun map => Region.renameWires map region)
          apply WireRenaming.ext
          intro signature wire
          rfl
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childResult)).renameWires rename)
        let sourceAfter := inner.fill (childResult.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourceEq : sourceBefore = sourceAfter := by
          simp only [inner, retained, childRename, materialRename, appendNil,
            sourceBefore, sourceAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have sourceAfterCanonical : sourceAfter.Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let outerOccurrence : Occurrence sourceAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty (by
              rw [← sourceEq]
              exact RegionIso.refl _)
        let childOccurrence := Occurrence.nest outerOccurrence
        let normalizedChild :=
          (normalizedRegion pattern childEvidence childSites).1
        let targetBefore := Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename
            (normalizedItem pattern evidence (.cut childSites)).1)
        let targetAfter := inner.fill
          (Region.renameWires childRename normalizedChild)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [normalizedItem, inner, retained, childRename,
            materialRename, appendNil, normalizedChild, targetBefore,
            targetAfter, DiagramContext.fill, Region.renameWires,
            Region.singleton, Region.ofItems, Region.adjoinAt,
            ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have outerTargetCanonical :
            (outerOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have outerTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            outerOccurrence.interface.boundaryWire
            (outerOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)).Canonical := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerTargetCanonical
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)) := by
          intro signature wire
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              outerTargetExternalTwoEnded wire
        have childSelection : regionHasSelection childSites = true := by
          simpa only [itemHasSelection] using hasSelection
        have child := normalizedRegionStrict pattern childEvidence
          childSites childSelection (outer ++ (hostLocals ++ [])) childRename
          childOccurrence
          childTargetCanonical
          childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          rw [← targetEq]
          exact RegionIso.refl _
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              outerTargetCanonical outerTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso outerTargetCanonical targetCanonical
            outerTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (Region.renameWires childRename normalizedChild))
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        have exactChild : StrictEquates occurrence targetBefore targetCanonical
            targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) child.1 finalIso,
            transGen_iso finalIso child.2 (OpenDiagramIso.refl source)⟩
        simpa only [targetBefore, normalizedItem, sourceBefore] using exactChild
  termination_by 5 * sizeOf sites + 1
end

/-- Normalize every selected application in one exact authoritative item
sequence and connect the actual occurrence bidirectionally to the generated
identity-boundary instantiation. -/
theorem normalizeItemsEquates
    {arguments outer hostLocals sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ hostLocals) sourceWires
      targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ hostLocals)}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals .nil result) host) :
    ∃ normalized : Region (outer ++ hostLocals),
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        ∃ targetCanonical :
            (occurrence.context.fill
              (Region.adjoinAt hostLocals .nil normalized)).Canonical,
          ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized)),
            let reconstructed := occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized))
              targetCanonical targetExternalTwoEnded
            let target := if itemsHaveSelection sites = false then host
              else reconstructed
            OpenDiagram.Isomorphic target reconstructed ∧
              Relation.ReflTransGen Step host target ∧
                Relation.ReflTransGen Step target host := by
  let output := normalizedItems pattern evidence sites
  by_cases noSelection : itemsHaveSelection sites = false
  · have outputEq : output.1 = result := by
      simpa only [output] using
        normalizedItems_eq_of_noSelection pattern evidence sites noSelection
    have targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)).Canonical := by
      rw [outputEq]
      exact occurrence.sourceCanonical
    have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)) := by
      intro signature wire
      rw [outputEq]
      exact occurrence.sourceExternalTwoEnded wire
    have targetIsomorphic : OpenDiagram.Isomorphic host
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals .nil output.1))
          targetCanonical targetExternalTwoEnded) := by
      exact ⟨by simpa only [outputEq] using occurrence.host_iso⟩
    refine ⟨output.1, output.2, targetCanonical,
      targetExternalTwoEnded, ?_⟩
    dsimp only
    rw [if_pos noSelection]
    exact ⟨targetIsomorphic,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · exact (by
  let sourceRegion := Region.adjoinAt hostLocals .nil result
  let targetRegion := Region.adjoinAt hostLocals .nil output.1
  let materialScope := normalizedItems_scope pattern evidence sites
  let regionScope := adjoinAt_preserves_scope hostLocals
    (.nil : ItemSeq (outer ++ hostLocals)) result output.1 materialScope
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill targetRegion) replacement.2
  have targetCanonical : (occurrence.context.fill targetRegion).Canonical :=
    replacement.1
  have hasSelection : itemsHaveSelection sites = true := by
    cases selected : itemsHaveSelection sites with
    | false => exact False.elim (noSelection selected)
    | true => rfl
  let identity : WireRenaming (outer ++ hostLocals)
      (outer ++ hostLocals) := WireRenaming.id
  let presentedOccurrence : Occurrence
      (Region.adjoinAt hostLocals .nil (result.renameWires identity)) host := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := by
      simpa only [identity, Region.renameWires_id] using occurrence.sourceCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [identity, Region.renameWires_id] using
        occurrence.sourceExternalTwoEnded wire
    host_iso := by
      simpa only [identity, Region.renameWires_id] using occurrence.host_iso
  }
  have folded := normalizedItemsStrict (outer := outer) pattern evidence sites
    hasSelection hostLocals identity (.nil : ItemSeq (outer ++ hostLocals))
      presentedOccurrence (by
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetCanonical) (by
        intro signature wire
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetExternalTwoEnded wire)
  have exactStrict : StrictEquates occurrence targetRegion targetCanonical
      targetExternalTwoEnded := by
    simpa only [presentedOccurrence, targetRegion, identity,
      Region.renameWires_id] using folded
  have equivalent := exactStrict.toEquates
  refine ⟨output.1, output.2, targetCanonical,
    targetExternalTwoEnded, ?_⟩
  dsimp only
  rw [if_neg noSelection]
  exact ⟨OpenDiagram.Isomorphic.refl _, equivalent.1, equivalent.2⟩)

end EqualityNormalization

/-- A proof-irrelevant traversal operation used only to recover the exact
selected-site layout from authoritative instantiation evidence. Its unit datum
cannot select a transform endpoint. -/
private def normalizationOperation (arguments : List Sig) :
    Transform.Operation arguments where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun _ _ _ => PUnit
  site := fun {_ _ targetWires} _ _ _ _ => Region.blank targetWires
  pin := fun {_ _ targetWires} _ _ => Region.blank targetWires

/-- The fixed traversal frame retains the exact source-side instantiation
indices and uses the identity target context only as an inert site annotation
index. -/
private def normalizationFrame (outer before after arguments : List Sig) :
    Transform.Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ after)) where
  sourceKeep := _root_.VisualProof.Rule.Comprehension.retain outer before after
    arguments
  targetKeep := WireRenaming.id
  selected := _root_.VisualProof.Rule.Comprehension.selected outer before after
    arguments

mutual
  /-- Unit site annotations exist for every exact authoritative region
  result. The existential stays in `Prop`, so no Instantiation proof is
  eliminated into caller-selectable data. -/
  private theorem normalizationRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | mk itemsEvidence =>
        obtain ⟨sites⟩ := normalizationItemsSites_nonempty
          (frame := frame.append _) itemsEvidence
        exact ⟨.mk sites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item-sequence
  result. -/
  private theorem normalizationItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := normalizationItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := normalizationItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item result. -/
  private theorem normalizationItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨ItemSites.atom (pattern := pattern) (frame := frame) head ports⟩
    | selectedAtom ports =>
        exact ⟨ItemSites.selectedAtom (pattern := pattern) (frame := frame)
          ports PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨sites⟩ := normalizationRegionSites_nonempty childEvidence
        exact ⟨.cut sites⟩
  termination_by sizeOf source
end

/-- A fixed unit-data site traversal selected internally from exact
Instantiation evidence. -/
private noncomputable def normalizationSites
    {arguments common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result) :
    ItemsSites (normalizationOperation arguments) PUnit.unit evidence :=
  Classical.choice (normalizationItemsSites_nonempty evidence)

/-- Exact singleton-atom decomposition at an existing pattern item. The
boundary/equality phases may choose the formal position only by proving that
the atom's argument list is precisely the remaining boundary. -/
structure FormalShape
    {patternWires atomArguments : List Sig}
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) where
  before : List Sig
  after : List Sig
  formal : Var patternWires (.rel (before ++ after))
  retained : Vars patternWires (before ++ after)
  head_eq : HEq head formal
  ports_eq : HEq ports retained
  boundaryWire : Vars patternWires
    (before ++ .rel (before ++ after) :: after)
  boundary_eq : boundaryWire =
    Argument.Projection.Vars.insertAt before formal retained
  boundarySurjective : ∀ wire : Fin patternWires.length,
    ∃ position : Fin
      (before ++ .rel (before ++ after) :: after).length,
      (boundaryWire.get position).index = wire
  canonical : (Region.singleton (.atom head ports)).Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire
    (Region.singleton (.atom head ports))

/-- The exact open singleton atom selected by a formal leaf decomposition. -/
def FormalShape.pattern
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    (shape : FormalShape head ports) :
    OpenDiagram
      (shape.before ++ .rel (shape.before ++ shape.after) :: shape.after) := {
  external := patternWires
  boundaryWire := shape.boundaryWire
  boundarySurjective := shape.boundarySurjective
  body := Region.singleton (.atom head ports)
  canonical := shape.canonical
  externalTwoEnded := shape.externalTwoEnded
}

/-- Caller-owned exact all-sites evidence for one singleton formal pattern.
The final primitive is intentionally absent: `compile` below fixes it to
`itemsFormal`. -/
structure FormalPhase
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    (shape : FormalShape head ports) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq
    (outer ++ (localBefore ++
      .rel (shape.before ++
        .rel (shape.before ++ shape.after) :: shape.after) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      shape.pattern
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after).sourceKeep
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after).selected
      source result
  sites : ItemsSites (Leaf.Formal.operation shape.before shape.after)
    PUnit.unit evidence
  request : Telescope.Request
    (Region.adjoinAt (localBefore ++ localAfter) .nil result)
    (.mk
      (localBefore ++
        .rel (shape.before ++
          .rel (shape.before ++ shape.after) :: shape.after) :: localAfter)
      source)
  prepare : ∀ output : ExactEdit
    (Transform.ItemsEdit (Leaf.Formal.operation shape.before shape.after)
      (Leaf.Formal.rootFrame outer localBefore localAfter shape.before
        shape.after)
      PUnit.unit source)
    (fun edit => edit.run),
    request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        output.endpoint)

/-- The singleton-atom branch fixes the final phase to FormalApplication. -/
private theorem FormalPhase.compile
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {shape : FormalShape head ports}
    (phase : FormalPhase shape) : phase.request.Result := by
  exact itemsFormal phase.evidence phase.sites phase.request phase.prepare

/-- Exact singleton-identity decomposition at an existing pattern item. -/
structure IdentityShape
    {patternWires : List Sig}
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var patternWires signature) where
  boundaryWire : Vars patternWires (List.replicate arity signature)
  boundary_eq : boundaryWire = Leaf.Identity.Vars.fromFn ports
  boundarySurjective : ∀ wire : Fin patternWires.length,
    ∃ position : Fin (List.replicate arity signature).length,
      (boundaryWire.get position).index = wire
  canonical :
    (Region.singleton (.identity signature arity ports)).Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire
    (Region.singleton (.identity signature arity ports))

/-- The exact open singleton identity selected by an identity leaf
decomposition. -/
def IdentityShape.pattern
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    (shape : IdentityShape signature arity ports) :
    OpenDiagram (List.replicate arity signature) := {
  external := patternWires
  boundaryWire := shape.boundaryWire
  boundarySurjective := shape.boundarySurjective
  body := Region.singleton (.identity signature arity ports)
  canonical := shape.canonical
  externalTwoEnded := shape.externalTwoEnded
}

/-- Caller-owned exact all-sites evidence for one singleton identity pattern.
The final primitive is intentionally absent: `compile` below fixes it to
`itemsIdentity`. -/
structure IdentityPhase
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    (shape : IdentityShape signature arity ports) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq
    (outer ++ (localBefore ++
      .rel (List.replicate arity signature) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      shape.pattern
      (Leaf.Identity.rootFrame outer localBefore localAfter signature
        arity).sourceKeep
      (Leaf.Identity.rootFrame outer localBefore localAfter signature
        arity).selected
      source result
  sites : ItemsSites (Leaf.Identity.operation signature arity)
    PUnit.unit evidence
  request : Telescope.Request
    (Region.adjoinAt (localBefore ++ localAfter) .nil result)
    (.mk
      (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
      source)
  prepare : ∀ output : ExactEdit
    (Transform.ItemsEdit (Leaf.Identity.operation signature arity)
      (Leaf.Identity.rootFrame outer localBefore localAfter signature arity)
      PUnit.unit source)
    (fun edit => edit.run),
    request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        output.endpoint)

/-- The singleton-identity branch fixes the final phase to IdentityLeaf. -/
private theorem IdentityPhase.compile
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    {shape : IdentityShape signature arity ports}
    (phase : IdentityPhase shape) : phase.request.Result := by
  exact itemsIdentity phase.evidence phase.sites phase.request phase.prepare

/-- One exact strict compiler goal. Its public fields preserve the actual
region indices of the request, so a structural plan cannot exchange a child
result for one about different endpoints. -/
structure Goal where
  holeWires : List Sig
  instantiated : Region holeWires
  pending : Region holeWires
  request : Telescope.Request instantiated pending

/-- Package an existing exact request without changing any endpoint. -/
def Goal.ofRequest
    {holeWires : List Sig}
    {instantiated pending : Region holeWires}
    (request : Telescope.Request instantiated pending) : Goal := {
  holeWires := holeWires
  instantiated := instantiated
  pending := pending
  request := request
}

/-- The strict result belonging to an exact packaged request. -/
def Goal.Result (goal : Goal) : Prop :=
  goal.request.Result

/-- The exact goal stored by the established blank phase. -/
def nilGoal {wires : List Sig} (phase : Compiler.NilPhase wires) : Goal :=
  .ofRequest phase.request

/-- The exact goal stored by a singleton formal phase. -/
def FormalPhase.goal
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {shape : FormalShape head ports}
    (phase : FormalPhase shape) : Goal :=
  .ofRequest phase.request

/-- The exact goal stored by a singleton identity phase. -/
def IdentityPhase.goal
    {patternWires : List Sig}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var patternWires signature}
    {shape : IdentityShape signature arity ports}
    (phase : IdentityPhase shape) : Goal :=
  .ofRequest phase.request

/-- The exact goal for a constructor-preparation segment. Its pending and
final endpoints are definitionally the supplied prepared region and its
continuation is reflexive, so it contains no caller-selected derivation. -/
noncomputable def Goal.exact
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (polarityEq : context.polarity = polarity)
    (instantiated prepared : Region holeWires)
    (instantiatedCanonical : (context.fill instantiated).Canonical)
    (instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill instantiated))
    (preparedCanonical : (context.fill prepared).Canonical)
    (preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill prepared)) : Goal :=
  .ofRequest {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity instantiated prepared))
      (match polarity with
      | .positive => instantiatedCanonical
      | .negative => preparedCanonical)
      (match polarity with
      | .positive => instantiatedExternalTwoEnded
      | .negative => preparedExternalTwoEnded)
    endpoint := prepared
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity instantiated prepared)
      (match polarity with
      | .positive => instantiatedCanonical
      | .negative => preparedCanonical)
      (match polarity with
      | .positive => instantiatedExternalTwoEnded
      | .negative => preparedExternalTwoEnded)
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := preparedCanonical
    pendingExternalTwoEnded := preparedExternalTwoEnded
    endpointCanonical := preparedCanonical
    endpointExternalTwoEnded := preparedExternalTwoEnded
    continuation := Telescope.refl polarity interface context
      preparedCanonical preparedExternalTwoEnded polarityEq
  }

/-- Consume the strict result of an exact goal as its optional telescope
segment. -/
theorem Goal.exactResult
    {boundary holeWires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external holeWires}
    {polarityEq : context.polarity = polarity}
    {instantiated prepared : Region holeWires}
    {instantiatedCanonical : (context.fill instantiated).Canonical}
    {instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill instantiated)}
    {preparedCanonical : (context.fill prepared).Canonical}
    {preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill prepared)}
    (result : (Goal.exact polarity interface context polarityEq instantiated
      prepared instantiatedCanonical instantiatedExternalTwoEnded
      preparedCanonical preparedExternalTwoEnded).Result) :
    Telescope polarity interface context instantiated prepared
      instantiatedCanonical instantiatedExternalTwoEnded preparedCanonical
      preparedExternalTwoEnded := by
  exact Telescope.Compiles.toTelescope polarity interface context
    instantiatedCanonical instantiatedExternalTwoEnded preparedCanonical
    preparedExternalTwoEnded polarityEq result

/-- The exact child goal for the current request's preparation segment. -/
noncomputable abbrev Goal.preparation
    (target : Goal)
    (prepared : Region target.holeWires)
    (preparedCanonical :
      (target.request.occurrence.context.fill prepared).Canonical)
    (preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      target.request.occurrence.interface.boundaryWire
      (target.request.occurrence.context.fill prepared)) : Goal :=
  Goal.exact target.request.polarity target.request.occurrence.interface
    target.request.occurrence.context target.request.continuation.1
    target.instantiated prepared target.request.instantiatedCanonical
    target.request.instantiatedExternalTwoEnded preparedCanonical
    preparedExternalTwoEnded

/-- Consume the strict result of the current request's exact preparation
goal. -/
theorem Goal.preparationResult
    {target : Goal}
    {prepared : Region target.holeWires}
    {preparedCanonical :
      (target.request.occurrence.context.fill prepared).Canonical}
    {preparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      target.request.occurrence.interface.boundaryWire
      (target.request.occurrence.context.fill prepared)}
    (result : (Goal.preparation target prepared preparedCanonical
      preparedExternalTwoEnded).Result) :
    Telescope target.request.polarity target.request.occurrence.interface
      target.request.occurrence.context target.instantiated prepared
      target.request.instantiatedCanonical
      target.request.instantiatedExternalTwoEnded preparedCanonical
      preparedExternalTwoEnded := by
  exact Goal.exactResult result

/-- Exact consecutive preparation segments compose in logical order for both
occurrence polarities. -/
private theorem telescopeTrans
    {boundary holeWires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external holeWires}
    {first middle last : Region holeWires}
    {firstCanonical : (context.fill first).Canonical}
    {firstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill first)}
    {middleCanonical : (context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill middle)}
    {lastCanonical : (context.fill last).Canonical}
    {lastExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill last)}
    (head : Telescope polarity interface context first middle
      firstCanonical firstExternalTwoEnded middleCanonical
      middleExternalTwoEnded)
    (tail : Telescope polarity interface context middle last
      middleCanonical middleExternalTwoEnded lastCanonical
      lastExternalTwoEnded) :
    Telescope polarity interface context first last firstCanonical
      firstExternalTwoEnded lastCanonical lastExternalTwoEnded := by
  cases polarity with
  | positive => exact ⟨head.1, head.2.trans tail.2⟩
  | negative => exact ⟨head.1, tail.2.trans head.2⟩

/-- Exact outer-boundary inputs for one comprehension application. The
authoritative instantiation evidence fixes the retained locals, source syntax,
and original instantiated endpoint. -/
structure NormalizationTarget (pattern : OpenDiagram arguments) where
  outer : List Sig
  before : List Sig
  after : List Sig
  source : ItemSeq
    (outer ++ (before ++ .rel arguments :: after))
  result : Region (outer ++ (before ++ after))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
      (normalizationFrame outer before after arguments).sourceKeep
      (normalizationFrame outer before after arguments).selected source result
  request : Telescope.Request
    (Region.adjoinAt (before ++ after) .nil result)
    (.mk (before ++ .rel arguments :: after) source)

namespace NormalizationTarget

variable {arguments : List Sig} {pattern : OpenDiagram arguments}

abbrev goal (target : NormalizationTarget pattern) : Goal :=
  Goal.ofRequest target.request

private noncomputable def sites (target : NormalizationTarget pattern) :
    ItemsSites (normalizationOperation arguments) PUnit.unit target.evidence :=
  normalizationSites target.evidence

private noncomputable def originalEndpoint
    (target : NormalizationTarget pattern) :
    OpenDiagram target.request.boundary :=
  target.request.occurrence.interface.withBody
    (target.request.occurrence.context.fill
      (Region.adjoinAt (target.before ++ target.after) .nil target.result))
    target.request.instantiatedCanonical
    target.request.instantiatedExternalTwoEnded

private noncomputable def normalizationOccurrence
    (target : NormalizationTarget pattern) :
    Occurrence
      (Region.adjoinAt (target.before ++ target.after) .nil target.result)
      target.originalEndpoint :=
  exactOccurrence target.request.occurrence.interface
    target.request.occurrence.context
    (Region.adjoinAt (target.before ++ target.after) .nil target.result)
    target.request.instantiatedCanonical
    target.request.instantiatedExternalTwoEnded

/-- Compiler-owned output of the fixed normalization theorem. The relational
target is conditional only so the no-selection case remains literally
reflexive; `isomorphism` fixes its presentation relative to the reconstructed
normalized endpoint. -/
private structure Output (target : NormalizationTarget pattern) where
  normalized : Region (target.outer ++ (target.before ++ target.after))
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (EqualityNormalization.identityBoundary pattern)
      (normalizationFrame target.outer target.before target.after
        arguments).sourceKeep
      (normalizationFrame target.outer target.before target.after
        arguments).selected target.source normalized
  canonical :
    (target.request.occurrence.context.fill
      (Region.adjoinAt (target.before ++ target.after) .nil normalized)).Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded
    target.request.occurrence.interface.boundaryWire
    (target.request.occurrence.context.fill
      (Region.adjoinAt (target.before ++ target.after) .nil normalized))
  isomorphism : OpenDiagramIso
    (if EqualityNormalization.itemsHaveSelection target.sites = false then
      target.originalEndpoint
    else
      target.request.occurrence.interface.withBody
        (target.request.occurrence.context.fill
          (Region.adjoinAt (target.before ++ target.after) .nil normalized))
        canonical externalTwoEnded)
    (target.request.occurrence.interface.withBody
      (target.request.occurrence.context.fill
        (Region.adjoinAt (target.before ++ target.after) .nil normalized))
      canonical externalTwoEnded)
  forward : Relation.ReflTransGen Step target.originalEndpoint
    (if EqualityNormalization.itemsHaveSelection target.sites = false then
      target.originalEndpoint
    else
      target.request.occurrence.interface.withBody
        (target.request.occurrence.context.fill
          (Region.adjoinAt (target.before ++ target.after) .nil normalized))
        canonical externalTwoEnded)
  reverse : Relation.ReflTransGen Step
    (if EqualityNormalization.itemsHaveSelection target.sites = false then
      target.originalEndpoint
    else
      target.request.occurrence.interface.withBody
        (target.request.occurrence.context.fill
          (Region.adjoinAt (target.before ++ target.after) .nil normalized))
        canonical externalTwoEnded)
    target.originalEndpoint

private theorem output_nonempty (target : NormalizationTarget pattern) :
    Nonempty target.Output := by
  obtain ⟨normalized, evidence, canonical, externalTwoEnded,
      isomorphic, forward, reverse⟩ :=
    EqualityNormalization.normalizeItemsEquates pattern target.evidence
      target.sites target.normalizationOccurrence
  obtain ⟨isomorphism⟩ := isomorphic
  exact ⟨{
    normalized := normalized
    evidence := evidence
    canonical := canonical
    externalTwoEnded := externalTwoEnded
    isomorphism := isomorphism
    forward := forward
    reverse := reverse
  }⟩

private noncomputable def output (target : NormalizationTarget pattern) :
    target.Output :=
  Classical.choice target.output_nonempty

noncomputable def normalized (target : NormalizationTarget pattern) :
    Region (target.outer ++ (target.before ++ target.after)) :=
  target.output.normalized

theorem normalizedEvidence (target : NormalizationTarget pattern) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (EqualityNormalization.identityBoundary pattern)
      (normalizationFrame target.outer target.before target.after
        arguments).sourceKeep
      (normalizationFrame target.outer target.before target.after
        arguments).selected target.source target.normalized :=
  target.output.evidence

private noncomputable def normalizedInstantiated
    (target : NormalizationTarget pattern) :
    Region target.outer :=
  Region.adjoinAt (target.before ++ target.after) .nil
    target.normalized

private noncomputable def normalizedEndpoint
    (target : NormalizationTarget pattern) :
    OpenDiagram target.request.boundary :=
  target.request.occurrence.interface.withBody
    (target.request.occurrence.context.fill target.normalizedInstantiated)
    target.output.canonical target.output.externalTwoEnded

private theorem polaritySourceCanonicalAt
    {outer holeWires : List Sig}
    (polarity : Polarity)
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (beforeCanonical : (context.fill before).Canonical)
    (afterCanonical : (context.fill after).Canonical) :
    (context.fill (polaritySource polarity before after)).Canonical := by
  cases polarity
  · exact beforeCanonical
  · exact afterCanonical

private theorem polaritySourceExternalTwoEndedAt
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (before after : Region holeWires)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)) :
    OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (polaritySource polarity before after)) := by
  cases polarity
  · exact beforeExternalTwoEnded
  · exact afterExternalTwoEnded

private theorem normalizedSourceCanonical
    (target : NormalizationTarget pattern) :
    (target.request.occurrence.context.fill
      (polaritySource target.request.polarity target.normalizedInstantiated
        target.request.endpoint)).Canonical := by
  exact polaritySourceCanonicalAt target.request.polarity
    target.request.occurrence.context target.normalizedInstantiated
    target.request.endpoint target.output.canonical
    target.request.endpointCanonical

private theorem normalizedSourceExternalTwoEnded
    (target : NormalizationTarget pattern) :
    OpenDiagram.ExternalTwoEnded
      target.request.occurrence.interface.boundaryWire
      (target.request.occurrence.context.fill
        (polaritySource target.request.polarity target.normalizedInstantiated
          target.request.endpoint)) := by
  exact polaritySourceExternalTwoEndedAt target.request.polarity
    target.request.occurrence.interface target.request.occurrence.context
    target.normalizedInstantiated target.request.endpoint
    target.output.externalTwoEnded target.request.endpointExternalTwoEnded

/-- The structural child's exact request replaces only the instantiated
endpoint and its generated validity. Pending syntax, final endpoint, context,
polarity, and continuation remain the actual parent request. -/
noncomputable def normalizedRequest (target : NormalizationTarget pattern) :
    Telescope.Request target.normalizedInstantiated target.goal.pending := {
  boundary := target.request.boundary
  source := target.request.occurrence.interface.withBody
    (target.request.occurrence.context.fill
      (polaritySource target.request.polarity target.normalizedInstantiated
        target.request.endpoint))
    target.normalizedSourceCanonical target.normalizedSourceExternalTwoEnded
  endpoint := target.request.endpoint
  polarity := target.request.polarity
  occurrence := exactOccurrence target.request.occurrence.interface
    target.request.occurrence.context
    (polaritySource target.request.polarity target.normalizedInstantiated
      target.request.endpoint)
    target.normalizedSourceCanonical target.normalizedSourceExternalTwoEnded
  instantiatedCanonical := target.output.canonical
  instantiatedExternalTwoEnded := target.output.externalTwoEnded
  pendingCanonical := target.request.pendingCanonical
  pendingExternalTwoEnded := target.request.pendingExternalTwoEnded
  endpointCanonical := target.request.endpointCanonical
  endpointExternalTwoEnded := target.request.endpointExternalTwoEnded
  continuation := target.request.continuation
}

noncomputable abbrev normalizedGoal (target : NormalizationTarget pattern) : Goal :=
  Goal.ofRequest target.normalizedRequest

private noncomputable def phaseTarget (target : NormalizationTarget pattern) :
    OpenDiagram target.request.boundary :=
  if EqualityNormalization.itemsHaveSelection target.sites = false then
    target.originalEndpoint
  else
    target.normalizedEndpoint

private theorem compile (target : NormalizationTarget pattern)
    (core : target.normalizedGoal.Result) : target.goal.Result := by
  cases polarityEq : target.request.polarity with
  | positive =>
      have coreSteps : Relation.TransGen Step target.normalizedEndpoint
          (target.request.occurrence.interface.withBody
            (target.request.occurrence.context.fill target.request.endpoint)
            target.request.endpointCanonical
            target.request.endpointExternalTwoEnded) := by
        simpa only [normalizedGoal, Goal.Result, Goal.ofRequest,
          Telescope.Request.Result, Telescope.Compiles, normalizedRequest,
          polarityEq, polaritySource, polarityTarget, exactOccurrence,
          normalizedEndpoint] using core
      have phaseIso : OpenDiagramIso target.phaseTarget
          target.normalizedEndpoint := by
        simpa only [phaseTarget, normalizedEndpoint] using
          target.output.isomorphism
      have forward : Relation.ReflTransGen Step target.originalEndpoint
          target.phaseTarget := by
        simpa only [phaseTarget, normalizedEndpoint] using target.output.forward
      have exact : Relation.TransGen Step target.originalEndpoint
          (target.request.occurrence.interface.withBody
            (target.request.occurrence.context.fill target.request.endpoint)
            target.request.endpointCanonical
            target.request.endpointExternalTwoEnded) :=
        forward.transGen
          (transGen_iso phaseIso.symm coreSteps (OpenDiagramIso.refl _))
      have sourceIso : OpenDiagramIso target.originalEndpoint
          target.request.source := by
        simpa only [originalEndpoint, polarityEq, polaritySource] using
          target.request.occurrence.host_iso.symm
      have presented :=
        transGen_iso sourceIso exact (OpenDiagramIso.refl _)
      simpa only [goal, Goal.Result, Goal.ofRequest, Telescope.Request.Result,
        Telescope.Compiles, polarityEq, polarityTarget] using presented
  | negative =>
      have coreSteps : Relation.TransGen Step
          (target.request.occurrence.interface.withBody
            (target.request.occurrence.context.fill target.request.endpoint)
            target.request.endpointCanonical
            target.request.endpointExternalTwoEnded)
          target.normalizedEndpoint := by
        simpa only [normalizedGoal, Goal.Result, Goal.ofRequest,
          Telescope.Request.Result, Telescope.Compiles, normalizedRequest,
          polarityEq, polaritySource, polarityTarget, exactOccurrence,
          normalizedEndpoint] using core
      have phaseIso : OpenDiagramIso target.phaseTarget
          target.normalizedEndpoint := by
        simpa only [phaseTarget, normalizedEndpoint] using
          target.output.isomorphism
      have reverse : Relation.ReflTransGen Step target.phaseTarget
          target.originalEndpoint := by
        simpa only [phaseTarget, normalizedEndpoint] using target.output.reverse
      have exact : Relation.TransGen Step
          (target.request.occurrence.interface.withBody
            (target.request.occurrence.context.fill target.request.endpoint)
            target.request.endpointCanonical
            target.request.endpointExternalTwoEnded)
          target.originalEndpoint :=
        (transGen_iso (OpenDiagramIso.refl _) coreSteps phaseIso.symm)
          |>.reflTransGen reverse
      have sourceIso : OpenDiagramIso
          (target.request.occurrence.interface.withBody
            (target.request.occurrence.context.fill target.request.endpoint)
            target.request.endpointCanonical
            target.request.endpointExternalTwoEnded)
          target.request.source := by
        simpa only [polarityEq, polaritySource] using
          target.request.occurrence.host_iso.symm
      have presented :=
        transGen_iso sourceIso exact (OpenDiagramIso.refl _)
      simpa only [goal, Goal.Result, Goal.ofRequest, Telescope.Request.Result,
        Telescope.Compiles, polarityEq, polarityTarget, originalEndpoint] using
          presented

end NormalizationTarget

/-- Evidence for one primitive at a fixed local-rule family. It contains the
exact staged and raw endpoints, validity, presentation isomorphisms, and
preparation, but deliberately contains neither a `Step` injection nor a
compiled result. -/
private structure PrimitivePhase (localRule : LocalRule) (goal : Goal) where
  staged : Region goal.holeWires
  rawPrepared : Region goal.holeWires
  rawPending : Region goal.holeWires
  preparation : goal.request.Preparation rawPrepared
  rawPendingCanonical :
    (goal.request.occurrence.context.fill rawPending).Canonical
  rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPending)
  pendingIso : RegionIso (WireEquiv.refl goal.holeWires)
    goal.pending rawPending
  localStep : localRule rawPrepared rawPending
  stagedIso : RegionIso (WireEquiv.refl goal.holeWires)
    staged rawPrepared

/-- Internal conversion of fixed-family phase evidence to the mandatory
primitive core. Public structural plans below never receive this injection. -/
private def dischargePrimitive
    {localRule : LocalRule}
    {goal : Goal}
    (inject : ∀ {stepBoundary : List Sig}
      {stepSource stepTarget : OpenDiagram stepBoundary},
      Contextual localRule stepSource stepTarget →
        Step stepSource stepTarget)
    (phase : PrimitivePhase localRule goal) :
    goal.request.Discharge phase.staged := by
  let branch : goal.request.Branch phase.preparation.prepared := {
    rawPrepared := phase.rawPrepared
    rawPending := phase.rawPending
    localRule := localRule
    inject := inject
    preparedCanonical := phase.preparation.preparedCanonical
    preparedExternalTwoEnded :=
      phase.preparation.preparedExternalTwoEnded
    rawPreparedCanonical := phase.preparation.rawPreparedCanonical
    rawPreparedExternalTwoEnded :=
      phase.preparation.rawPreparedExternalTwoEnded
    rawPendingCanonical := phase.rawPendingCanonical
    rawPendingExternalTwoEnded := phase.rawPendingExternalTwoEnded
    preparedIso := phase.preparation.preparedIso
    pendingIso := phase.pendingIso
    localStep := phase.localStep
    preparation := phase.preparation.telescope
  }
  exact Telescope.Request.Discharge.primitive branch phase.stagedIso

/-- The fixed endpoint data for one exact primitive. The preparation
telescope is deliberately absent; structural recursion must supply it from
the preceding child result. -/
private structure PrimitiveTarget (localRule : LocalRule) (goal : Goal) where
  rawPrepared : Region goal.holeWires
  rawPending : Region goal.holeWires
  rawPreparedCanonical :
    (goal.request.occurrence.context.fill rawPrepared).Canonical
  rawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPrepared)
  rawPendingCanonical :
    (goal.request.occurrence.context.fill rawPending).Canonical
  rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    goal.request.occurrence.interface.boundaryWire
    (goal.request.occurrence.context.fill rawPending)
  pendingIso : RegionIso (WireEquiv.refl goal.holeWires)
    goal.pending rawPending
  localStep : localRule rawPrepared rawPending

/-- Install the child-produced telescope into an exact primitive target. -/
private noncomputable def PrimitiveTarget.phase
    {localRule : LocalRule} {goal : Goal}
    (target : PrimitiveTarget localRule goal)
    (staged : Region goal.holeWires)
    (preparation : goal.request.Preparation target.rawPrepared)
    (stagedIso : RegionIso (WireEquiv.refl goal.holeWires)
      staged target.rawPrepared) : PrimitivePhase localRule goal := {
  staged := staged
  rawPrepared := target.rawPrepared
  rawPending := target.rawPending
  preparation := preparation
  rawPendingCanonical := target.rawPendingCanonical
  rawPendingExternalTwoEnded := target.rawPendingExternalTwoEnded
  pendingIso := target.pendingIso
  localStep := target.localStep
  stagedIso := stagedIso
}

/-- Exact open-pattern data indexed by the existing region syntax. -/
structure PatternShape
    {patternWires : List Sig}
    (body : Region patternWires)
    (arguments : List Sig) where
  boundaryWire : Vars patternWires arguments
  boundarySurjective : ∀ wire : Fin patternWires.length,
    ∃ position : Fin arguments.length,
      (boundaryWire.get position).index = wire
  canonical : body.Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire body

/-- The only open diagram associated with an exact syntax-indexed shape. -/
def PatternShape.pattern
    {patternWires arguments : List Sig}
    {body : Region patternWires}
    (shape : PatternShape body arguments) : OpenDiagram arguments := {
  external := patternWires
  boundaryWire := shape.boundaryWire
  boundarySurjective := shape.boundarySurjective
  body := body
  canonical := shape.canonical
  externalTwoEnded := shape.externalTwoEnded
}

/-- The authoritative all-sites inputs for one structural primitive. It
contains no edit: the constrained compiler fold is the sole producer of that
edit and of its exact staged endpoint. -/
structure ItemsAuthority
    {arguments outer resultLocals stagedLocals sourceWires : List Sig}
    (pattern : OpenDiagram arguments)
    (operation : Transform.Operation arguments)
    (frame : Transform.Frame arguments (outer ++ resultLocals)
      sourceWires (outer ++ stagedLocals))
    (data : operation.Data frame)
    (source : ItemSeq sourceWires)
    (result : Region (outer ++ resultLocals))
    (pending : Region outer) where
  evidence :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
      frame.sourceKeep frame.selected source result
  sites : ItemsSites operation data evidence
  request : Telescope.Request
    (Region.adjoinAt resultLocals .nil result) pending
  stagedCanonical : ∀ output : ExactEdit
      (Transform.ItemsEdit operation frame data source)
      (fun edit => edit.run),
    (request.occurrence.context.fill
      (Region.adjoinAt stagedLocals .nil output.endpoint)).Canonical
  stagedExternalTwoEnded : ∀ output : ExactEdit
      (Transform.ItemsEdit operation frame data source)
      (fun edit => edit.run),
    OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (Region.adjoinAt stagedLocals .nil output.endpoint))

namespace ItemsAuthority

abbrev Output
    {arguments outer resultLocals stagedLocals sourceWires : List Sig}
    {pattern : OpenDiagram arguments}
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ resultLocals)
      sourceWires (outer ++ stagedLocals)}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ resultLocals)}
    {pending : Region outer}
    (_authority : ItemsAuthority pattern operation frame data source result
      pending) :=
  ExactEdit (Transform.ItemsEdit operation frame data source)
    (fun edit => edit.run)

def staged
    {arguments outer resultLocals stagedLocals sourceWires : List Sig}
    {pattern : OpenDiagram arguments}
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ resultLocals)
      sourceWires (outer ++ stagedLocals)}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ resultLocals)}
    {pending : Region outer}
    (authority : ItemsAuthority pattern operation frame data source result
      pending)
    (output : authority.Output) : Region outer :=
  Region.adjoinAt stagedLocals .nil output.endpoint

abbrev goal
    {arguments outer resultLocals stagedLocals sourceWires : List Sig}
    {pattern : OpenDiagram arguments}
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ resultLocals)
      sourceWires (outer ++ stagedLocals)}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ resultLocals)}
    {pending : Region outer}
    (authority : ItemsAuthority pattern operation frame data source result
      pending) : Goal :=
  Goal.ofRequest authority.request

end ItemsAuthority

/-- Build the fixed primitive discharge after recursive compilation has
supplied only the telescope ending at the authoritative edit endpoint. -/
private noncomputable def dischargeAtAuthoritativeEdit
    {localRule : LocalRule}
    {goal : Goal}
    (inject : ∀ {stepBoundary : List Sig}
      {stepSource stepTarget : OpenDiagram stepBoundary},
      Contextual localRule stepSource stepTarget → Step stepSource stepTarget)
    {staged rawPrepared rawPending : Region goal.holeWires}
    (stagedCanonical :
      (goal.request.occurrence.context.fill staged).Canonical)
    (stagedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      goal.request.occurrence.interface.boundaryWire
      (goal.request.occurrence.context.fill staged))
    (telescope : Telescope goal.request.polarity
      goal.request.occurrence.interface goal.request.occurrence.context
      goal.instantiated staged goal.request.instantiatedCanonical
      goal.request.instantiatedExternalTwoEnded stagedCanonical
      stagedExternalTwoEnded)
    (stagedEq : staged = rawPrepared)
    (rawPendingCanonical :
      (goal.request.occurrence.context.fill rawPending).Canonical)
    (rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      goal.request.occurrence.interface.boundaryWire
      (goal.request.occurrence.context.fill rawPending))
    (pendingIso : RegionIso (WireEquiv.refl goal.holeWires)
      goal.pending rawPending)
    (localStep : localRule rawPrepared rawPending) :
    goal.request.Discharge staged := by
  let supplied : goal.request.Preparation staged := {
    prepared := staged
    preparedCanonical := stagedCanonical
    preparedExternalTwoEnded := stagedExternalTwoEnded
    rawPreparedCanonical := stagedCanonical
    rawPreparedExternalTwoEnded := stagedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := telescope
  }
  let preparation : goal.request.Preparation rawPrepared := stagedEq ▸ supplied
  let primitive : PrimitiveTarget localRule goal := {
    rawPrepared := rawPrepared
    rawPending := rawPending
    rawPreparedCanonical := by
      rw [← stagedEq]
      exact stagedCanonical
    rawPreparedExternalTwoEnded := by
      rw [← stagedEq]
      exact stagedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    pendingIso := pendingIso
    localStep := localStep
  }
  exact dischargePrimitive inject
    (primitive.phase staged preparation (by
      rw [stagedEq]
      exact RegionIso.refl _))

/-- Exact authoritative CutShape inputs at an existing cut constructor. -/
structure CutTarget
    {patternWires arguments : List Sig}
    (body : Region patternWires)
    (shape : PatternShape (Region.singleton (.cut body)) arguments) where
  outer : List Sig
  before : List Sig
  after : List Sig
  source : ItemSeq
    (outer ++ (before ++ .rel arguments :: after))
  result : Region (outer ++ (before ++ after))
  authority : ItemsAuthority shape.pattern
    (Content.Cut.operation arguments)
    (Content.Cut.rootFrame outer before after arguments)
    (Content.Cut.targetHead outer before after arguments)
    source result (.mk (before ++ .rel arguments :: after) source)

namespace CutTarget

variable {patternWires arguments : List Sig}
variable {body : Region patternWires}
variable {shape : PatternShape (Region.singleton (.cut body)) arguments}

abbrev goal (target : CutTarget body shape) : Goal := target.authority.goal
abbrev Output (target : CutTarget body shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : CutTarget body shape) (output : target.Output) :
    Region target.outer := target.authority.staged output

private def description (target : CutTarget body shape) (output : target.Output) :
    Content.Cut.Wrap.Description target.outer := {
  arguments := arguments
  before := target.before
  after := target.after
  items := target.source
  itemsEdit := output.edit
}

private theorem staged_eq_target (target : CutTarget body shape)
    (output : target.Output) :
    target.staged output = (target.description output).target := by
  change Region.adjoinAt
    (target.before ++ .rel arguments :: target.after) .nil output.endpoint =
      Region.adjoinAt
        (target.before ++ .rel arguments :: target.after) .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge (target : CutTarget body shape)
    (output : target.Output)
    (result : (Goal.preparation target.goal (target.staged output)
      (target.authority.stagedCanonical output)
      (target.authority.stagedExternalTwoEnded output)).Result) :
    target.authority.request.Discharge (target.staged output) := by
  let description := target.description output
  exact dischargeAtAuthoritativeEdit
    (goal := target.goal)
    (staged := target.staged output)
    (rawPrepared := description.target)
    (rawPending := description.source)
    (fun step => Step.cutShape step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (Goal.preparationResult result) (target.staged_eq_target output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (Or.inr (.wrap (.mk description)))

end CutTarget

/-- Exact authoritative ParallelShape inputs at one existing conjunction. -/
structure ParallelTarget
    {patternWires arguments : List Sig}
    (head : Item patternWires)
    (tail : ItemSeq patternWires)
    (shape : PatternShape (Region.ofItems (.cons head tail)) arguments) where
  outer : List Sig
  before : List Sig
  after : List Sig
  source : ItemSeq
    (outer ++ (before ++ .rel arguments :: after))
  result : Region (outer ++ (before ++ after))
  authority : ItemsAuthority shape.pattern
    (Content.Parallel.operation arguments)
    (Content.Parallel.rootFrame outer before after arguments)
    (Content.Parallel.firstHead outer before after arguments,
      Content.Parallel.secondHead outer before after arguments)
    source result (.mk (before ++ .rel arguments :: after) source)
  afterHead : authority.Output → Region outer
  afterHeadCanonical : ∀ output : authority.Output,
    (authority.request.occurrence.context.fill (afterHead output)).Canonical
  afterHeadExternalTwoEnded : ∀ output : authority.Output,
    OpenDiagram.ExternalTwoEnded
      authority.request.occurrence.interface.boundaryWire
      (authority.request.occurrence.context.fill (afterHead output))

namespace ParallelTarget

variable {patternWires arguments : List Sig}
variable {head : Item patternWires} {tail : ItemSeq patternWires}
variable {shape : PatternShape (Region.ofItems (.cons head tail)) arguments}

abbrev goal (target : ParallelTarget head tail shape) : Goal :=
  target.authority.goal
abbrev Output (target : ParallelTarget head tail shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : ParallelTarget head tail shape) (output : target.Output) :
    Region target.outer := target.authority.staged output

private def description (target : ParallelTarget head tail shape)
    (output : target.Output) :
    Content.Parallel.Split.Description target.outer := {
  arguments := arguments
  before := target.before
  after := target.after
  items := target.source
  itemsEdit := output.edit
}

private theorem staged_eq_target (target : ParallelTarget head tail shape)
    (output : target.Output) :
    target.staged output = (target.description output).target := by
  change Region.adjoinAt
    (target.before ++ .rel arguments :: .rel arguments :: target.after)
      .nil output.endpoint =
    Region.adjoinAt
      (target.before ++ .rel arguments :: .rel arguments :: target.after)
      .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge
    (target : ParallelTarget head tail shape)
    (output : target.Output)
    (headResult : (Goal.exact target.goal.request.polarity
      target.goal.request.occurrence.interface
      target.goal.request.occurrence.context
      target.goal.request.continuation.1 target.goal.instantiated
      (target.afterHead output) target.goal.request.instantiatedCanonical
      target.goal.request.instantiatedExternalTwoEnded
      (target.afterHeadCanonical output)
      (target.afterHeadExternalTwoEnded output)).Result)
    (tailResult : (Goal.exact target.goal.request.polarity
      target.goal.request.occurrence.interface
      target.goal.request.occurrence.context
      target.goal.request.continuation.1 (target.afterHead output)
      (target.staged output) (target.afterHeadCanonical output)
      (target.afterHeadExternalTwoEnded output)
      (target.authority.stagedCanonical output)
      (target.authority.stagedExternalTwoEnded output)).Result) :
    target.authority.request.Discharge (target.staged output) := by
  let description := target.description output
  exact dischargeAtAuthoritativeEdit
    (goal := target.goal)
    (staged := target.staged output)
    (rawPrepared := description.target)
    (rawPending := description.source)
    (fun step => Step.parallelShape step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (telescopeTrans
      (Goal.exactResult
        (preparedExternalTwoEnded := target.afterHeadExternalTwoEnded output)
        headResult)
      (Goal.exactResult
        (preparedExternalTwoEnded :=
          target.authority.stagedExternalTwoEnded output)
        tailResult))
    (target.staged_eq_target output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (Or.inr (.split (.mk description)))

end ParallelTarget

/-- Exact authoritative Arity inputs for one pattern-local wire. -/
structure ArityTarget
    {patternWires arguments : List Sig}
    (body : Region patternWires)
    (shape : PatternShape body arguments) where
  outer : List Sig
  before : List Sig
  after : List Sig
  added : Sig
  source : ItemSeq
    (outer ++ (before ++ .rel arguments :: after))
  result : Region (outer ++ (before ++ after))
  authority : ItemsAuthority shape.pattern
    (Arity.operation arguments added)
    (Arity.rootFrame outer before after arguments added)
    (Arity.targetHead outer before after arguments added)
    source result (.mk (before ++ .rel arguments :: after) source)

namespace ArityTarget

variable {patternWires arguments : List Sig}
variable {body : Region patternWires}
variable {shape : PatternShape body arguments}

abbrev goal (target : ArityTarget body shape) : Goal := target.authority.goal
abbrev Output (target : ArityTarget body shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : ArityTarget body shape) (output : target.Output) :
    Region target.outer := target.authority.staged output

private def description (target : ArityTarget body shape) (output : target.Output) :
    Arity.Shift.Description target.outer := {
  arguments := arguments
  before := target.before
  after := target.after
  added := target.added
  items := target.source
  itemsEdit := output.edit
}

private theorem staged_eq_target (target : ArityTarget body shape)
    (output : target.Output) :
    target.staged output = (target.description output).target := by
  change Region.adjoinAt
    (target.before ++ .rel (arguments ++ [target.added]) :: target.after)
      .nil output.endpoint =
    Region.adjoinAt
      (target.before ++ .rel (arguments ++ [target.added]) :: target.after)
      .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge (target : ArityTarget body shape)
    (output : target.Output)
    (result : (Goal.preparation target.goal (target.staged output)
      (target.authority.stagedCanonical output)
      (target.authority.stagedExternalTwoEnded output)).Result) :
    target.authority.request.Discharge (target.staged output) := by
  let description := target.description output
  exact dischargeAtAuthoritativeEdit
    (goal := target.goal)
    (staged := target.staged output)
    (rawPrepared := description.target)
    (rawPending := description.source)
    (fun step => Step.arity step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (Goal.preparationResult result) (target.staged_eq_target output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (Or.inr (.shift (.mk description)))

end ArityTarget

mutual
  /-- The sole outer-boundary plan normalizes one exact arbitrary pattern to
  its generated identity-boundary evidence before entering the structural
  compiler. -/
  inductive BoundaryPlan :
      {arguments : List Sig} → OpenDiagram arguments → Goal → Type 1
    | normalize
        {arguments : List Sig} {pattern : OpenDiagram arguments}
        (target : NormalizationTarget pattern)
        (child : NormalizedPlan target target.normalizedEvidence) :
        BoundaryPlan pattern target.goal

  /-- The normalized child is indexed by the compiler-generated exact
  `ItemsResult` as well as its generated goal and identity-boundary syntax. -/
  inductive NormalizedPlan :
      {arguments : List Sig} → {pattern : OpenDiagram arguments} →
      (target : NormalizationTarget pattern) →
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (EqualityNormalization.identityBoundary pattern)
        (normalizationFrame target.outer target.before target.after
          arguments).sourceKeep
        (normalizationFrame target.outer target.before target.after
          arguments).selected target.source target.normalized → Type 1
    | mk
        {arguments : List Sig} {pattern : OpenDiagram arguments}
        {target : NormalizationTarget pattern}
        (structural : RegionPlan
          (EqualityNormalization.identityBoundary pattern).body
          target.normalizedGoal) :
        NormalizedPlan target target.normalizedEvidence

  /-- Type-valued structural compiler evidence indexed by one exact existing
  region. Identity-boundary normalization is owned only by `BoundaryPlan`. -/
  inductive RegionPlan :
      {wires : List Sig} → Region wires → Goal → Type 1
    | mk
        {outer locals : List Sig}
        {items : ItemSeq (outer ++ locals)}
        {goal : Goal}
        (arity : ArityPlan (.mk locals items) goal) :
        RegionPlan (.mk locals items) goal

  /-- Pattern-local arity compilation ends at the exact existing region and
  recurses only at the authoritative shifted endpoint. -/
  inductive ArityPlan :
      {wires : List Sig} → Region wires → Goal → Type 1
    | items
        {outer locals : List Sig}
        {bodyItems : ItemSeq (outer ++ locals)}
        {goal : Goal}
        (plan : ItemsPlan bodyItems goal) :
        ArityPlan (.mk locals bodyItems) goal
    | shift
        {wires arguments : List Sig}
        {body : Region wires}
        {shape : PatternShape body arguments}
        (target : ArityTarget body shape)
        (child : ∀ output : target.Output,
          ArityPlan body (Goal.preparation target.goal
            (target.staged output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        ArityPlan body target.goal

  /-- Item-sequence compilation fixes cons to ParallelShape and indexes both
  recursive children by the exact edit endpoint and shared midpoint. -/
  inductive ItemsPlan :
      {wires : List Sig} → ItemSeq wires → Goal → Type 1
    | nil {wires : List Sig} (phase : Compiler.NilPhase wires) :
        ItemsPlan (.nil : ItemSeq wires) (nilGoal phase)
    | cons
        {wires arguments : List Sig}
        {head : Item wires} {tail : ItemSeq wires}
        {shape : PatternShape (Region.ofItems (.cons head tail)) arguments}
        (target : ParallelTarget head tail shape)
        (headPlan : ∀ output : target.Output,
          ItemPlan head (Goal.exact target.goal.request.polarity
            target.goal.request.occurrence.interface
            target.goal.request.occurrence.context
            target.goal.request.continuation.1 target.goal.instantiated
            (target.afterHead output)
            target.goal.request.instantiatedCanonical
            target.goal.request.instantiatedExternalTwoEnded
            (target.afterHeadCanonical output)
            (target.afterHeadExternalTwoEnded output)))
        (tailPlan : ∀ output : target.Output,
          ItemsPlan tail (Goal.exact target.goal.request.polarity
            target.goal.request.occurrence.interface
            target.goal.request.occurrence.context
            target.goal.request.continuation.1 (target.afterHead output)
            (target.staged output) (target.afterHeadCanonical output)
            (target.afterHeadExternalTwoEnded output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        ItemsPlan (.cons head tail) target.goal

  /-- Item compilation fixes each existing constructor to its production
  primitive family. -/
  inductive ItemPlan : {wires : List Sig} → Item wires → Goal → Type 1
    | atom
        {patternWires atomArguments : List Sig}
        {head : Var patternWires (.rel atomArguments)}
        {ports : Vars patternWires atomArguments}
        (shape : FormalShape head ports)
        (phase : FormalPhase shape) :
        ItemPlan (.atom head ports) phase.goal
    | identity
        {patternWires : List Sig}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var patternWires signature}
        (shape : IdentityShape signature arity ports)
        (phase : IdentityPhase shape) :
        ItemPlan (.identity signature arity ports) phase.goal
    | cut
        {wires arguments : List Sig}
        {body : Region wires}
        {shape : PatternShape (Region.singleton (.cut body)) arguments}
        (target : CutTarget body shape)
        (child : ∀ output : target.Output,
          RegionPlan body (Goal.preparation target.goal
            (target.staged output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        ItemPlan (.cut body) target.goal
end

mutual
  /-- Interpret one exact region plan. -/
  private def regionResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : RegionPlan body goal) : goal.Result :=
    match plan with
    | .mk arity => arityResult arity
  termination_by structural plan

  /-- Interpret the fixed equality-normalization boundary around the child's
  mandatory structural core. -/
  private def boundaryResult
      {arguments : List Sig} {pattern : OpenDiagram arguments} {goal : Goal}
      (plan : BoundaryPlan pattern goal) : goal.Result :=
    match plan with
    | .normalize target (.mk structural) =>
        target.compile (regionResult structural)

  /-- Interpret arity phases through their authoritative all-sites folds. -/
  private def arityResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : ArityPlan body goal) : goal.Result :=
    match plan with
    | .items items => itemsResult items
    | .shift target child =>
        Compiler.items
          (operation := Arity.operation _ target.added)
          (frame := Arity.rootFrame target.outer target.before target.after _
            target.added)
          (Arity.targetHead target.outer target.before target.after _
            target.added)
          target.authority.evidence target.authority.sites
          target.authority.request {
            close := fun output =>
              target.discharge output (arityResult (child output))
          }
  termination_by structural plan

  /-- Interpret item sequences, deriving ParallelShape only after the exact
  all-sites edit is returned. -/
  private def itemsResult
      {wires : List Sig} {bodyItems : ItemSeq wires} {goal : Goal}
      (plan : ItemsPlan bodyItems goal) : goal.Result :=
    match plan with
    | .nil phase => phase.compile
    | .cons target headPlan tailPlan =>
        Compiler.items
          (operation := Content.Parallel.operation _)
          (frame := Content.Parallel.rootFrame target.outer target.before
            target.after _)
          (Content.Parallel.firstHead target.outer target.before target.after _,
            Content.Parallel.secondHead target.outer target.before
              target.after _)
          target.authority.evidence target.authority.sites
          target.authority.request {
            close := fun output => target.discharge output
              (itemResult (headPlan output)) (itemsResult (tailPlan output))
          }
  termination_by structural plan

  /-- Interpret items, deriving CutShape only after the exact all-sites edit
  is returned. -/
  private def itemResult
      {wires : List Sig} {bodyItem : Item wires} {goal : Goal}
      (plan : ItemPlan bodyItem goal) : goal.Result :=
    match plan with
    | .atom _ phase => phase.compile
    | .identity _ phase => phase.compile
    | .cut target child =>
        Compiler.items
          (operation := Content.Cut.operation _)
          (frame := Content.Cut.rootFrame target.outer target.before
            target.after _)
          (Content.Cut.targetHead target.outer target.before target.after _)
          target.authority.evidence target.authority.sites
          target.authority.request {
            close := fun output =>
              target.discharge output (regionResult (child output))
          }
  termination_by structural plan
end

/-- Production entry over one existing open pattern and its exact
syntax-indexed evidence plan. -/
theorem compile
    (pattern : OpenDiagram arguments)
    (plan : BoundaryPlan pattern goal) : goal.Result := by
  exact boundaryResult plan

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
