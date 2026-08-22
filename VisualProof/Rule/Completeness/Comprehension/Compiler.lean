import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Rule.Completeness.Erasure.Exposure
import VisualProof.Diagram.Isomorphism.Algebra
import VisualProof.Diagram.Scope.Isomorphism

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
  apply EqualityNormalization.supportPins_eq_nil
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

private theorem spliceAt_nil
    (material : Region materialWires)
    (rename : WireRenaming materialWires outer) :
    Region.spliceAt (outer := outer) [] .nil material
      ⟨fun wire => (rename wire).appendLeft []⟩ =
      material.renameWires rename := by
  cases material with
  | mk locals materialItems =>
      have materialMap : WireRenaming.comp
          (Region.adjoinMaterialWire outer [] locals)
          ((⟨fun wire => (rename wire).appendLeft []⟩ :
            WireRenaming materialWires (outer ++ [])).appendRight locals) =
          rename.appendRight locals := by
        apply WireRenaming.ext
        intro signature wire
        apply Var.appendCases (left := materialWires) (right := locals)
          (motive := fun wire =>
            WireRenaming.comp
              (Region.adjoinMaterialWire outer [] locals)
              ((⟨fun wire => (rename wire).appendLeft []⟩ :
                WireRenaming materialWires
                  (outer ++ [])).appendRight locals) wire =
                rename.appendRight locals wire)
        · intro inheritedSignature inherited
          simp [WireRenaming.comp, WireRenaming.appendRight,
            Region.adjoinMaterialWire]
        · intro localSignature localWire
          simp [WireRenaming.comp, WireRenaming.appendRight,
            Region.adjoinMaterialWire]
          rfl
      simp only [Region.spliceAt, Region.renameWires, Region.adjoinAt,
        ItemSeq.renameWires, ItemSeq.nil_append, List.nil_append,
        ItemSeq.renameWires_comp]
      exact congrArg
        (fun map => Region.mk locals (materialItems.renameWires map))
        materialMap

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
  /-- Whether the exact site annotation contains any selected application. -/
  private def regionHasSelection
      {common sourceWires targetWires : List Sig}
      {operation : Transform.Operation patternWires}
      {frame : Transform.Frame patternWires common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) : Bool :=
    match sites with
    | .mk childSites => itemsHaveSelection childSites
  termination_by 3 * sizeOf sites

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
  termination_by 3 * sizeOf sites + 2

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
  termination_by 3 * sizeOf sites + 1
end

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
  rw [EqualityNormalization.instantiate_renameWires]
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

@[simp] private theorem presentationOccurrence_interface
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (afterCanonical : after.Canonical)
    (sameNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ [])
    (presentation : RegionIso (WireEquiv.refl holeWires) before after) :
    (presentationOccurrence occurrence afterCanonical sameNonempty
      presentation).interface = occurrence.interface := by
  simp [presentationOccurrence]

@[simp] private theorem presentationOccurrence_context
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (afterCanonical : after.Canonical)
    (sameNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ [])
    (presentation : RegionIso (WireEquiv.refl holeWires) before after) :
    (presentationOccurrence occurrence afterCanonical sameNonempty
      presentation).context = occurrence.context := by
  simp [presentationOccurrence]

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

private theorem pinAllTwiceRegionOfNonempty
    {boundary holeWires pinWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (rename : WireRenaming pinWires (holeWires ++ before.locals))
    (nonempty : pinWires ≠ []) :
    let pins := allPins pinWires rename
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk before.locals
            ((before.items.append pins).append pins))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk before.locals
              ((before.items.append pins).append pins))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk before.locals
                  ((before.items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk before.locals
                  ((before.items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded)
            source := by
  cases before
  exact pinAllTwiceOfNonempty occurrence rename nonempty

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
      have rawEq : raw = Region.appendAdjoinedHostSuffix hostLocals hostItems
          (contextPins outer hostLocals)
          (.mk materialLocals materialItems) := by
        simp only [raw, Region.appendAdjoinedHostSuffix, hostRename,
          materialRename,
          host, material, base, pinsRename, ItemSeq.append_assoc]
      let target := Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals))
        (.mk materialLocals materialItems)
      let presentation : RegionIso (WireEquiv.refl outer) raw target := by
        rw [rawEq]
        exact RegionIso.adjoinAtMoveHostSuffix hostLocals hostItems
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

private theorem identityBoundarySelectedStrict
    (pattern : OpenDiagram arguments)
    {common outer hostLocals : List Sig}
    (ports : Vars common arguments)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).renameWires rename)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports).renameWires rename))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports).renameWires rename)))) :
    StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (identityBoundary pattern) ports).renameWires rename))
      targetCanonical targetExternalTwoEnded := by
  let mappedPorts := ports.map fun wire => rename wire
  let sourceBefore :=
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).renameWires rename
  let sourceAfter :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern mappedPorts
  let sourceHostBefore := Region.adjoinAt hostLocals hostItems sourceBefore
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
    presentationOccurrence occurrence sourceAfterCanonical sourceNonempty
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
  obtain ⟨ownedTargetCanonical, ownedTargetExternalTwoEnded, equivalent⟩ :=
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
  simpa only [targetBefore, sourceHostBefore, sourceBefore] using presented

private structure SelectedLeafCompiler
    {arguments : List Sig} (pattern : OpenDiagram arguments) where
  selectedAt :
    {common target : List Sig} →
    Vars common arguments →
    WireRenaming common target →
    Region target
  selectedNaturality :
    ∀ {common middle target : List Sig}
      (ports : Vars common arguments)
      (rename : WireRenaming common middle)
      (post : WireRenaming middle target),
      RegionIso (WireEquiv.refl target)
        ((selectedAt ports rename).renameWires post)
        (selectedAt ports (WireRenaming.comp post rename))
  selectedStrict :
    ∀ {common outer hostLocals boundary : List Sig}
      (ports : Vars common arguments)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports).renameWires rename)) source)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (selectedAt ports rename))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (selectedAt ports rename)))),
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems (selectedAt ports rename))
        targetCanonical targetExternalTwoEnded

private noncomputable def identitySelectedLeaf
    (pattern : OpenDiagram arguments) : SelectedLeafCompiler pattern := {
  selectedAt := fun ports rename =>
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports).renameWires rename
  selectedNaturality := fun ports rename post =>
    RegionIso.renameWiresComp
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (identityBoundary pattern) ports)
      rename post
  selectedStrict := fun {_common _outer _hostLocals _boundary} ports rename
      hostItems {_source} occurrence targetCanonical targetExternalTwoEnded =>
    identityBoundarySelectedStrict pattern ports rename hostItems
      (occurrence := occurrence) targetCanonical targetExternalTwoEnded
}

namespace EvidenceFold

mutual
  private noncomputable def regionAt
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (rename : WireRenaming common target) : Region target :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites =>
      Region.adjoinAt locals .nil
        (itemsAt leaf childEvidence childSites (rename.appendRight locals))
  termination_by sizeOf sites

  private noncomputable def itemsAt
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (rename : WireRenaming common target) : Region target :=
    match sites with
    | .nil _ => Region.blank target
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item sourceTail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites =>
      (itemAt leaf itemEvidence itemSites rename).conjoin
        (itemsAt leaf tailEvidence tailSites rename)
  termination_by sizeOf sites

  private noncomputable def itemAt
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (rename : WireRenaming common target) : Region target :=
    match sites with
    | .atom head ports =>
      Region.singleton (.atom (rename head)
        (ports.map fun wire => rename wire))
    | .selectedAtom ports _ => leaf.selectedAt ports rename
    | .identity signature arity ports =>
      Region.singleton (.identity signature arity
        (fun position => rename (ports position)))
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites =>
      Region.singleton (.cut
        (regionAt leaf childEvidence childSites rename))
  termination_by sizeOf sites
end

mutual
  private theorem regionAt_eq_of_noSelection
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (none : regionHasSelection sites = false)
      (rename : WireRenaming common target) :
      regionAt leaf evidence sites rename = result.renameWires rename :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold regionAt
      simp_wf
      change Region.adjoinAt locals .nil
          (itemsAt leaf childEvidence childSites (rename.appendRight locals)) =
        (Region.adjoinAt locals .nil childResult).renameWires rename
      rw [Region.renameWires_adjoinAt_nil]
      rw [itemsAt_eq_of_noSelection leaf childEvidence childSites (by
        simpa only [regionHasSelection] using none) (rename.appendRight locals)]
  termination_by sizeOf sites

  private theorem itemsAt_eq_of_noSelection
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (none : itemsHaveSelection sites = false)
      (rename : WireRenaming common target) :
      itemsAt leaf evidence sites rename = result.renameWires rename :=
    match sites with
    | .nil _ => by
      unfold itemsAt
      simp_wf
      rfl
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item sourceTail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold itemsAt
      simp_wf
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
        (itemAt leaf itemEvidence itemSites rename).conjoin
            (itemsAt leaf tailEvidence tailSites rename) =
          (itemResult.conjoin tailResult).renameWires rename
      rw [Region.renameWires_conjoin]
      rw [itemAt_eq_of_noSelection leaf itemEvidence itemSites itemNone rename]
      rw [itemsAt_eq_of_noSelection leaf tailEvidence tailSites tailNone rename]
  termination_by sizeOf sites

  private theorem itemAt_eq_of_noSelection
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (none : itemHasSelection sites = false)
      (rename : WireRenaming common target) :
      itemAt leaf evidence sites rename = result.renameWires rename :=
    match sites with
    | .atom head ports => by
      unfold itemAt
      simp_wf
      rw [Region.singleton_renameWires]
      rfl
    | .selectedAtom _ _ => by
      simp only [itemHasSelection, Bool.true_eq_false] at none
    | .identity signature arity ports => by
      unfold itemAt
      simp_wf
      rw [Region.singleton_renameWires]
      rfl
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold itemAt
      simp_wf
      change Region.singleton (.cut
          (regionAt leaf childEvidence childSites rename)) =
        (Region.singleton (.cut childResult)).renameWires rename
      simp only [Region.singleton_renameWires, Item.renameWires]
      rw [regionAt_eq_of_noSelection leaf childEvidence childSites (by
        simpa only [itemHasSelection] using none) rename]
  termination_by sizeOf sites
end

mutual
  private noncomputable def regionAtNaturality
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (rename : WireRenaming common middle)
      (post : WireRenaming middle target) :
      RegionIso (WireEquiv.refl target)
        ((regionAt leaf evidence sites rename).renameWires post)
        (regionAt leaf evidence sites (WireRenaming.comp post rename)) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold regionAt
      simp_wf
      have maps : WireRenaming.comp (post.appendRight locals)
            (rename.appendRight locals) =
          (WireRenaming.comp post rename).appendRight locals := by
        apply WireRenaming.ext
        intro signature wire
        exact WireRenaming.appendRight_comp_apply rename post locals wire
      let exposed := RegionIso.renameWiresAdjoinAtNil
        (itemsAt leaf childEvidence childSites (rename.appendRight locals)) post
      let child := RegionIso.adjoinAt locals .nil
        (itemsAtNaturality leaf childEvidence childSites
          (rename.appendRight locals) (post.appendRight locals))
      simpa only [maps, WireEquiv.refl_trans] using exposed.trans child

  private noncomputable def itemsAtNaturality
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (rename : WireRenaming common middle)
      (post : WireRenaming middle target) :
      RegionIso (WireEquiv.refl target)
        ((itemsAt leaf evidence sites rename).renameWires post)
        (itemsAt leaf evidence sites (WireRenaming.comp post rename)) :=
    match sites with
    | .nil _ => by
      unfold itemsAt
      simp_wf
      exact RegionIso.refl _
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item sourceTail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold itemsAt
      simp_wf
      let exposed := RegionIso.renameWiresConjoin
        (itemAt leaf itemEvidence itemSites rename)
        (itemsAt leaf tailEvidence tailSites rename) post
      let children := RegionIso.conjoinCongr
        (itemAtNaturality leaf itemEvidence itemSites rename post)
        (itemsAtNaturality leaf tailEvidence tailSites rename post)
      simpa only [WireEquiv.refl_trans] using exposed.trans children

  private noncomputable def itemAtNaturality
      {arguments : List Sig} {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (rename : WireRenaming common middle)
      (post : WireRenaming middle target) :
      RegionIso (WireEquiv.refl target)
        ((itemAt leaf evidence sites rename).renameWires post)
        (itemAt leaf evidence sites (WireRenaming.comp post rename)) :=
    match sites with
    | .atom head ports => by
      unfold itemAt
      simp_wf
      simpa only [Region.singleton_renameWires, Item.renameWires,
        WireRenaming.comp] using
          RegionIso.renameWiresComp
            (Region.singleton (.atom head ports)) rename post
    | .selectedAtom ports _ => by
      unfold itemAt
      simp_wf
      exact leaf.selectedNaturality ports rename post
    | .identity signature arity ports => by
      unfold itemAt
      simp_wf
      simpa only [Region.singleton_renameWires, Item.renameWires,
        WireRenaming.comp] using
          RegionIso.renameWiresComp
            (Region.singleton (.identity signature arity ports)) rename post
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold itemAt
      simp_wf
      simpa only [Region.singleton_renameWires, Item.renameWires] using
        RegionIso.singletonCutCongr
          (regionAtNaturality leaf childEvidence childSites rename post)
end

mutual
  /-- Proof-only evidence that the identity-boundary leaf interpretation is an
  instantiation of the exact endpoint generated by `regionAt`. -/
  private def identityRegionEvidence
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
        (identityBoundary pattern) frame.sourceKeep frame.selected source
          (regionAt (identitySelectedLeaf pattern) evidence sites
            WireRenaming.id) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold regionAt
      simp_wf
      have renameEq : WireRenaming.id.appendRight locals =
          (WireRenaming.id : WireRenaming (common ++ locals)
            (common ++ locals)) := by
        apply WireRenaming.ext
        intro signature wire
        exact WireRenaming.appendRight_id_apply locals wire
      rw [renameEq]
      exact
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
          (identityItemsEvidence pattern childEvidence childSites)
  termination_by sizeOf sites

  /-- Proof-only evidence for the exact item-sequence endpoint. -/
  private def identityItemsEvidence
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (identityBoundary pattern) frame.sourceKeep frame.selected source
          (itemsAt (identitySelectedLeaf pattern) evidence sites
            WireRenaming.id) :=
    match sites with
    | .nil _ => by
      unfold itemsAt
      simp_wf
      exact
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold itemsAt
      simp_wf
      exact
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          (identityItemEvidence pattern itemEvidence itemSites)
          (identityItemsEvidence pattern tailEvidence tailSites)
  termination_by sizeOf sites

  /-- Proof-only evidence for the exact single-item endpoint. -/
  private def identityItemEvidence
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        (identityBoundary pattern) frame.sourceKeep frame.selected source
          (itemAt (identitySelectedLeaf pattern) evidence sites
            WireRenaming.id) :=
    match sites with
    | .atom head ports => by
      unfold itemAt
      simp_wf
      simpa only [WireRenaming.id, Diagram.vars_map_id] using
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
          head ports
    | .selectedAtom ports _ => by
      unfold itemAt identitySelectedLeaf
      simp_wf
      simpa only [Region.renameWires_id] using
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := identityBoundary pattern) ports
    | .identity signature arity ports => by
      unfold itemAt
      simp_wf
      simpa only [WireRenaming.id] using
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          signature arity ports
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold itemAt
      simp_wf
      exact
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
          (identityRegionEvidence pattern childEvidence childSites)
  termination_by sizeOf sites
end

mutual
  /-- Scope preservation for the exact identity-boundary region endpoint. -/
  private theorem identityRegionScope
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (rename : WireRenaming common target) :
      ScopePreservation (result.renameWires rename)
        (regionAt (identitySelectedLeaf pattern) evidence sites rename) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold regionAt
      simp_wf
      rw [Region.renameWires_adjoinAt_nil]
      let childTarget := itemsAt (identitySelectedLeaf pattern) childEvidence
        childSites (rename.appendRight locals)
      let childPreservation := identityItemsScope pattern childEvidence
        childSites (rename.appendRight locals)
      change ScopePreservation
        (Region.adjoinAt locals .nil
          (childResult.renameWires (rename.appendRight locals)))
        (Region.adjoinAt locals .nil childTarget)
      constructor
      · intro sourceCanonical
        have sourceChildCanonical :
            (childResult.renameWires (rename.appendRight locals)).Canonical :=
          Region.Canonical.material_of_adjoinAt locals .nil _ sourceCanonical
        have targetChildCanonical : childTarget.Canonical :=
          childPreservation.canonical sourceChildCanonical
        apply Region.Canonical.adjoinAt_of_material_roots locals .nil
          childTarget True.intro targetChildCanonical
        intro localIndex
        let localWire := Var.appendRight target (Var.ofIndex localIndex)
        have sourceRoot : RegionPath.RootedTwo
            ((childResult.renameWires (rename.appendRight locals)).incidencePaths
              localWire.index.val) := by
          simpa [localWire] using
            Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
              (childResult.renameWires (rename.appendRight locals))
              sourceCanonical localIndex
        simpa [localWire] using
          childPreservation.rootedTwo localWire sourceRoot
      · intro signature wire
        let childWire := wire.appendLeft locals
        have sourcePaths := Region.incidencePaths_adjoinAt_nil
          (childResult.renameWires (rename.appendRight locals)) childWire
        have targetPaths := Region.incidencePaths_adjoinAt_nil childTarget
          childWire
        have childIndex : childWire.index.val = wire.index.val := by
          simp [childWire]
        rw [childIndex] at sourcePaths targetPaths
        rw [sourcePaths, targetPaths]
        simpa only [childWire, Var.index_appendLeft] using
          childPreservation.incidenceNonempty childWire
      · intro signature wire sourceRoot
        let childWire := wire.appendLeft locals
        have sourcePaths := Region.incidencePaths_adjoinAt_nil
          (childResult.renameWires (rename.appendRight locals)) childWire
        have targetPaths := Region.incidencePaths_adjoinAt_nil childTarget
          childWire
        have childIndex : childWire.index.val = wire.index.val := by
          simp [childWire]
        rw [childIndex] at sourcePaths targetPaths
        rw [sourcePaths] at sourceRoot
        rw [targetPaths]
        simpa only [childWire, Var.index_appendLeft] using
          childPreservation.rootedTwo childWire (by
            simpa only [childWire, Var.index_appendLeft] using sourceRoot)
  termination_by sizeOf sites

  /-- Scope preservation for the exact identity-boundary item-sequence
  endpoint. -/
  private theorem identityItemsScope
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (rename : WireRenaming common target) :
      ScopePreservation (result.renameWires rename)
        (itemsAt (identitySelectedLeaf pattern) evidence sites rename) :=
    match sites with
    | .nil _ => by
      unfold itemsAt
      simp_wf
      change ScopePreservation (Region.blank common |>.renameWires rename)
        (Region.blank target)
      simpa only [Region.renameWires] using
        (show ScopePreservation (Region.blank target) (Region.blank target)
          from {
            canonical := fun canonical => canonical
            incidenceNonempty := fun _ => Iff.rfl
            rootedTwo := fun _ rooted => rooted
          })
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold itemsAt
      simp_wf
      rw [Region.renameWires_conjoin]
      let itemTarget := itemAt (identitySelectedLeaf pattern) itemEvidence
        itemSites rename
      let tailTarget := itemsAt (identitySelectedLeaf pattern) tailEvidence
        tailSites rename
      let itemPreservation := identityItemScope pattern itemEvidence
        itemSites rename
      let tailPreservation := identityItemsScope pattern tailEvidence
        tailSites rename
      change ScopePreservation
        ((itemResult.renameWires rename).conjoin
          (tailResult.renameWires rename))
        (itemTarget.conjoin tailTarget)
      have combined := Region.conjoin_preserves_scope
        (itemResult.renameWires rename) (tailResult.renameWires rename)
        itemTarget tailTarget itemPreservation.canonical
          tailPreservation.canonical itemPreservation.incidenceNonempty
            tailPreservation.incidenceNonempty itemPreservation.rootedTwo
              tailPreservation.rootedTwo
      exact {
        canonical := combined.1
        incidenceNonempty := fun wire => (combined.2 wire).1
        rootedTwo := fun wire => (combined.2 wire).2
      }
  termination_by sizeOf sites

  /-- Scope preservation for the exact identity-boundary single-item
  endpoint. -/
  private theorem identityItemScope
      {arguments : List Sig} (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (rename : WireRenaming common target) :
      ScopePreservation (result.renameWires rename)
        (itemAt (identitySelectedLeaf pattern) evidence sites rename) :=
    match sites with
    | .atom head ports => by
      unfold itemAt
      simp_wf
      rw [Region.singleton_renameWires]
      exact {
        canonical := fun canonical => canonical
        incidenceNonempty := fun _ => Iff.rfl
        rootedTwo := fun _ rooted => rooted
      }
    | .selectedAtom ports _ => by
      unfold itemAt identitySelectedLeaf
      simp_wf
      rw [instantiate_renameWires, instantiate_renameWires]
      let mappedPorts := ports.map fun wire => rename wire
      change ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern mappedPorts)
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (identityBoundary pattern) mappedPorts)
      constructor
      · intro _
        exact
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
            (identityBoundary pattern) mappedPorts
      · intro signature wire
        rw [instantiate_incidence_nonempty_iff,
          instantiate_incidence_nonempty_iff]
      · intro signature wire sourceRoot
        rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
        exact sourceRoot
    | .identity signature arity ports => by
      unfold itemAt
      simp_wf
      rw [Region.singleton_renameWires]
      exact {
        canonical := fun canonical => canonical
        incidenceNonempty := fun _ => Iff.rfl
        rootedTwo := fun _ rooted => rooted
      }
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold itemAt
      simp_wf
      rw [Region.singleton_renameWires]
      let childTarget := regionAt (identitySelectedLeaf pattern)
        childEvidence childSites rename
      let childPreservation := identityRegionScope pattern childEvidence
        childSites rename
      change ScopePreservation
        (Region.singleton (.cut (childResult.renameWires rename)))
        (Region.singleton (.cut childTarget))
      constructor
      · intro sourceCanonical
        apply (Region.singleton_cut_canonical_iff childTarget).mpr
        exact childPreservation.canonical
          ((Region.singleton_cut_canonical_iff
            (childResult.renameWires rename)).mp sourceCanonical)
      · intro signature wire
        rw [Region.incidencePaths_singleton_cut,
          Region.incidencePaths_singleton_cut]
        constructor
        · intro sourceNonempty
          have childSourceNonempty :
              (childResult.renameWires rename).incidencePaths
                wire.index.val ≠ [] := by
            intro sourceEmpty
            exact sourceNonempty ((List.map_eq_nil_iff).mpr sourceEmpty)
          have childTargetNonempty :=
            (childPreservation.incidenceNonempty wire).mp childSourceNonempty
          intro targetEmpty
          exact childTargetNonempty ((List.map_eq_nil_iff).mp targetEmpty)
        · intro targetNonempty
          have childTargetNonempty :
              childTarget.incidencePaths wire.index.val ≠ [] := by
            intro targetEmpty
            exact targetNonempty ((List.map_eq_nil_iff).mpr targetEmpty)
          have childSourceNonempty :=
            (childPreservation.incidenceNonempty wire).mpr childTargetNonempty
          intro sourceEmpty
          exact childSourceNonempty ((List.map_eq_nil_iff).mp sourceEmpty)
      · intro signature wire sourceRoot
        rw [Region.incidencePaths_singleton_cut] at sourceRoot ⊢
        have sameEmpty :
            (childResult.renameWires rename).incidencePaths
                  wire.index.val = [] ↔
              childTarget.incidencePaths wire.index.val = [] := by
          constructor
          · intro sourceEmpty
            by_cases targetEmpty : childTarget.incidencePaths
                wire.index.val = []
            · exact targetEmpty
            · exact False.elim
                (((childPreservation.incidenceNonempty wire).mpr targetEmpty)
                  sourceEmpty)
          · intro targetEmpty
            by_cases sourceEmpty :
                (childResult.renameWires rename).incidencePaths
                  wire.index.val = []
            · exact sourceEmpty
            · exact False.elim
                (((childPreservation.incidenceNonempty wire).mp sourceEmpty)
                  targetEmpty)
        have replaced := RegionPath.rootedTwo_replace []
          ((childResult.renameWires rename).incidencePaths wire.index.val)
          (childTarget.incidencePaths wire.index.val) [] 0 sameEmpty
        simpa only [List.nil_append, List.append_nil] using
          replaced.mp (by simpa using sourceRoot)
  termination_by sizeOf sites
end

end EvidenceFold

namespace EvidenceFold

mutual
  private noncomputable def regionStrict
      {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
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
            (regionAt leaf evidence sites rename)).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (regionAt leaf evidence sites rename))),
        StrictEquates occurrence
          (regionAt leaf evidence sites rename)
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
        let childTarget := itemsAt leaf childEvidence childSites childRename
        simp only [regionAt] at targetCanonical targetExternalTwoEnded ⊢
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                childTarget)).Canonical := by
          exact targetCanonical
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                childTarget)) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        have childSelection : itemsHaveSelection childSites = true := by
          simpa only [regionHasSelection] using hasSelection
        have folded := itemsStrict leaf
          childEvidence childSites childSelection locals childRename childHostItems
          childOccurrence childTargetCanonical childTargetExternalTwoEnded
        simpa only [regionAt, childTarget, childHostItems, childRename,
          childOccurrence] using folded
  termination_by 5 * sizeOf sites

  private noncomputable def itemsStrict
      {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
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
            (itemsAt leaf evidence sites rename))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemsAt leaf evidence sites rename)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          (itemsAt leaf evidence sites rename))
        targetCanonical (fun wire => targetExternalTwoEnded wire) := by
    let sourceMaterial := result.renameWires rename
    let targetMaterial := itemsAt leaf evidence sites rename
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
    have folded := itemsSupportedStrict leaf evidence
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
      have folded := itemsSupportedStrict leaf evidence sites
        hasSelection [] [] rename hostItems occurrence hostCanonical
          hostNonempty targetCanonical targetExternalTwoEnded
      simpa only [sourceMaterial, targetMaterial] using folded
  termination_by 5 * sizeOf sites + 4

  private noncomputable def itemsSupportedStrict
      {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
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
              (itemsAt leaf evidence sites rename))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemsAt leaf evidence sites rename)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (itemsAt leaf evidence sites rename))
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
        let itemAfter := itemAt leaf itemEvidence itemSites rename
        let tailAfter := itemsAt leaf tailEvidence tailSites rename
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
        let targetBefore :=
          (itemAt leaf itemEvidence itemSites rename).conjoin
            (itemsAt leaf tailEvidence tailSites rename)
        simp only [itemsAt] at targetCanonical targetExternalTwoEnded ⊢
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
          simpa only [targetBefore, itemAfter, tailAfter, itemsAt] using
            targetBeforeCanonical
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
        have itemPhase := itemWithTailStrict leaf
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
        let nextHostItems := Region.extendHostItems hostLocals hostItems itemAfter
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
        let flatTargetMaterial := itemsAt leaf tailEvidence tailSites nextRename
        have renamedTailCanonical :
            (tailAfter.renameWires hostWire).Canonical :=
          (Region.Canonical.renameWires_iff tailAfter hostWire).mpr
            tailAfterCanonical
        have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
          (RegionIso.canonical_iff
            (itemsAtNaturality leaf tailEvidence tailSites rename hostWire)).mp
              renamedTailCanonical
        have tailTargetValidity := supportedAdjoinValidity
          (hostLocals ++ itemAfter.locals) nextHostItems alignedFlattened
          nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
        have tailPhase := itemsSupportedStrict leaf
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
            simpa only [flatTargetMaterial, tailAfter, nextRename, hostWire]
              using (itemsAtNaturality leaf tailEvidence tailSites rename
                hostWire).symm)).trans
            ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemAfter
              tailAfter).symm.trans
              (RegionIso.adjoinAt hostLocals hostItems (by
                simpa only [itemAfter, tailAfter, targetBefore, itemsAt] using
                  RegionIso.refl (itemAfter.conjoin tailAfter))))
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
          targetBefore, itemsAt]
          using exactCombined)
          · have tailNone : itemsHaveSelection tailSites = false := by
              cases selected : itemsHaveSelection tailSites with
              | false => rfl
              | true => exact False.elim (tailSelected selected)
            have tailAfterEq : tailAfter = tailBefore := by
              simpa only [tailAfter, tailBefore] using
                itemsAt_eq_of_noSelection leaf tailEvidence tailSites
                  tailNone rename
            have itemPhaseValidity := supportedAdjoinValidity hostLocals
              hostItems sourceOccurrence hostCanonical hostNonempty
              (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
            have itemPhase := itemWithTailStrict leaf
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
              simpa only [targetBefore, itemAfter, tailAfter, itemsAt] using
                RegionIso.refl (itemAfter.conjoin tailAfter)
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
              sourceOccurrence, afterItem, targetBefore, itemsAt]
              using exactPresented
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
          have itemAfterEq : itemAfter = itemBefore := by
            simpa only [itemAfter, itemBefore] using
              itemAt_eq_of_noSelection leaf itemEvidence itemSites itemNone
                rename
          let flattened := flattenAdjoinOccurrence hostLocals hostItems
            itemBefore tailBefore sourceOccurrence hostCanonical hostNonempty
            itemBeforeCanonical tailBeforeCanonical
          let nextHostItems := Region.extendHostItems hostLocals hostItems itemBefore
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
          let flatTargetMaterial := itemsAt leaf tailEvidence tailSites nextRename
          have renamedTailCanonical :
              (tailAfter.renameWires hostWire).Canonical :=
            (Region.Canonical.renameWires_iff tailAfter hostWire).mpr
              tailAfterCanonical
          have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
            (RegionIso.canonical_iff
              (itemsAtNaturality leaf tailEvidence tailSites rename hostWire)).mp
                renamedTailCanonical
          have tailTargetValidity := supportedAdjoinValidity
            (hostLocals ++ itemBefore.locals) nextHostItems alignedFlattened
            nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
          have tailPhase := itemsSupportedStrict leaf
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
                simpa only [flatTargetMaterial, tailAfter, nextRename,
                  hostWire] using
                    (itemsAtNaturality leaf tailEvidence tailSites rename
                      hostWire).symm)).trans
              ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemBefore
                tailAfter).symm.trans
                (RegionIso.adjoinAt hostLocals hostItems (by
                  rw [← itemAfterEq]
                  simpa only [itemAfter, tailAfter, targetBefore, itemsAt] using
                    RegionIso.refl (itemAfter.conjoin tailAfter))))
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
            flatTargetEndpoint, targetBefore, itemsAt] using exactPresented
  termination_by 5 * sizeOf sites + 3

  private noncomputable def itemWithTailStrict
      {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
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
        (itemAt leaf evidence sites rename).Canonical)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((itemAt leaf evidence sites rename).conjoin
                tail))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((itemAt leaf evidence sites rename).conjoin tail)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          ((itemAt leaf evidence sites rename).conjoin tail))
        targetCanonical targetExternalTwoEnded := by
    let itemBefore := result.renameWires rename
    let itemAfter := itemAt leaf evidence sites rename
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
    let flatTargetMaterial := itemAt leaf evidence sites nextRename
    have renamedTargetCanonical :
        (itemAfter.renameWires hostWire).Canonical :=
      (Region.Canonical.renameWires_iff itemAfter hostWire).mpr
        itemAfterCanonical
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (RegionIso.canonical_iff
        (itemAtNaturality leaf evidence sites rename hostWire)).mp
          renamedTargetCanonical
    have flatTargetValidity := supportedAdjoinValidity
      (hostLocals ++ tail.locals) nextHostItems alignedFlattened
      nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
    have core := itemStrict leaf evidence sites hasSelection
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
        simpa only [flatTargetMaterial, itemAfter, nextRename, hostWire] using
          (itemAtNaturality leaf evidence sites rename hostWire).symm)).trans
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
      nextHostItems, hostWire, nextRename, flatTargetMaterial,
      flatTarget, flatEndpoint] using exactPresented
  termination_by 5 * sizeOf sites + 2

  private noncomputable def itemStrict
      {pattern : OpenDiagram arguments}
      (leaf : SelectedLeafCompiler pattern)
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
              (itemAt leaf evidence sites rename))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemAt leaf evidence sites rename)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (itemAt leaf evidence sites rename))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .atom head ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | .selectedAtom ports _ => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simp only [itemAt] at targetCanonical targetExternalTwoEnded ⊢
        exact leaf.selectedStrict ports rename hostItems occurrence
          targetCanonical targetExternalTwoEnded
    | .identity signature arity ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let childRename := rename
        let inner : DiagramContext outer (outer ++ hostLocals) :=
          .cut hostLocals hostItems .nil .hole
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childResult)).renameWires rename)
        let sourceAfter := inner.fill (childResult.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourcePresentation : RegionIso (WireEquiv.refl outer)
            sourceBefore sourceAfter := by
          simpa only [sourceBefore, sourceAfter, inner, childRename,
            DiagramContext.fill, Region.singleton_renameWires] using
              RegionIso.adjoinAtSingleton hostLocals hostItems
                (.cut (childResult.renameWires rename))
        have sourceAfterCanonical : sourceAfter.Canonical := by
          exact (RegionIso.canonical_iff sourcePresentation).mp
            (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [← List.length_pos_iff, ← List.length_pos_iff,
            RegionIso.incidencePaths_length_eq sourcePresentation wire]
        let outerOccurrence : Occurrence sourceAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty sourcePresentation
        let childOccurrence := Occurrence.nest outerOccurrence
        let childTarget := regionAt leaf childEvidence childSites childRename
        let targetBefore := Region.adjoinAt hostLocals hostItems
          (Region.singleton (.cut childTarget))
        let targetAfter := inner.fill childTarget
        simp only [itemAt] at targetCanonical targetExternalTwoEnded ⊢
        have targetBeforeCanonical :
            (occurrence.context.fill targetBefore).Canonical := by
          simpa only [targetBefore, childTarget, childRename] using
            targetCanonical
        have targetBeforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetBefore) := by
          intro signature wire
          simpa only [targetBefore, childTarget, childRename] using
            targetExternalTwoEnded wire
        have targetPresentation : RegionIso (WireEquiv.refl outer)
            targetBefore targetAfter := by
          simpa only [targetBefore, targetAfter, inner,
            DiagramContext.fill] using
              RegionIso.adjoinAtSingleton hostLocals hostItems
                (.cut childTarget)
        have targetAfterCanonical : targetAfter.Canonical :=
          (RegionIso.canonical_iff targetPresentation).mp
            (occurrence.context.holeCanonical _ targetBeforeCanonical)
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [← List.length_pos_iff, ← List.length_pos_iff,
            RegionIso.incidencePaths_length_eq targetPresentation wire]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetBeforeCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetBeforeCanonical
            targetBeforeExternalTwoEnded
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
              childTarget).Canonical := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerTargetCanonical
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              childTarget) := by
          intro signature wire
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              outerTargetExternalTwoEnded wire
        have childSelection : regionHasSelection childSites = true := by
          simpa only [itemHasSelection] using hasSelection
        have child := regionStrict leaf childEvidence
          childSites childSelection (outer ++ hostLocals) childRename
          childOccurrence
          childTargetCanonical
          childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := targetPresentation.symm
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              outerTargetCanonical outerTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetBeforeCanonical
                targetBeforeExternalTwoEnded) :=
          OpenDiagram.withBody_iso outerTargetCanonical targetBeforeCanonical
            outerTargetExternalTwoEnded targetBeforeExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                childTarget)
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetBeforeCanonical
                targetBeforeExternalTwoEnded) := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        have exactChild : StrictEquates occurrence targetBefore
            targetBeforeCanonical targetBeforeExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) child.1 finalIso,
            transGen_iso finalIso child.2 (OpenDiagramIso.refl source)⟩
        simpa only [targetBefore, childTarget, childRename, sourceBefore] using
          exactChild
  termination_by 5 * sizeOf sites + 1
end

end EvidenceFold

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
  let identity : WireRenaming (outer ++ hostLocals)
      (outer ++ hostLocals) := WireRenaming.id
  let output := EvidenceFold.itemsAt (identitySelectedLeaf pattern)
    evidence sites identity
  let outputEvidence := EvidenceFold.identityItemsEvidence pattern evidence
    sites
  by_cases noSelection : itemsHaveSelection sites = false
  · have outputEq : output = result := by
      simpa only [output, identity, Region.renameWires_id] using
        EvidenceFold.itemsAt_eq_of_noSelection
          (identitySelectedLeaf pattern) evidence sites noSelection identity
    have targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output)).Canonical := by
      rw [outputEq]
      exact occurrence.sourceCanonical
    have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output)) := by
      intro signature wire
      rw [outputEq]
      exact occurrence.sourceExternalTwoEnded wire
    have targetIsomorphic : OpenDiagram.Isomorphic host
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals .nil output))
          targetCanonical targetExternalTwoEnded) := by
      exact ⟨by simpa only [outputEq] using occurrence.host_iso⟩
    refine ⟨output, outputEvidence, targetCanonical,
      targetExternalTwoEnded, ?_⟩
    dsimp only
    rw [if_pos noSelection]
    exact ⟨targetIsomorphic,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · exact (by
  let sourceRegion := Region.adjoinAt hostLocals .nil result
  let targetRegion := Region.adjoinAt hostLocals .nil output
  let materialScope : ScopePreservation result output := by
    simpa only [output, identity, Region.renameWires_id] using
      EvidenceFold.identityItemsScope pattern evidence sites identity
  let regionScope := adjoinAt_preserves_scope hostLocals
    (.nil : ItemSeq (outer ++ hostLocals)) result output materialScope
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
  have folded := EvidenceFold.itemsStrict (outer := outer)
    (identitySelectedLeaf pattern) evidence sites
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
  refine ⟨output, outputEvidence, targetCanonical,
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
private structure FormalShape
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
private def FormalShape.pattern
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

/-! The structural compiler factors every constructor-local support vector
through the inherited identity vector.  The factor is selected from syntax,
before any site substitution is known, so its naturality law is part of the
typed permutation data rather than a side condition supplied by a caller. -/

/-- A typed argument permutation together with the syntactic naturality law
needed to reuse it at every selected site. -/
private structure TypedPermutation (source target : List Sig) where
  value : ArgumentPermutation.Permutation source target
  map_natural :
    ∀ {before after : List Sig} (variables : Vars before source)
      (rename : WireRenaming before after),
      (value.mapVars variables).map (fun wire => rename wire) =
        value.mapVars (variables.map fun wire => rename wire)

namespace TypedPermutation

/-- Exchange the first two typed positions. -/
private def swapHead (first second : Sig) (rest : List Sig) :
    TypedPermutation (first :: second :: rest) (second :: first :: rest) := {
  value := {
    mapVars := fun
      | .cons firstValue (.cons secondValue restValues) =>
          .cons secondValue (.cons firstValue restValues)
    unmapVars := fun
      | .cons secondValue (.cons firstValue restValues) =>
          .cons firstValue (.cons secondValue restValues)
    mapValues := fun _ values => (values.2.1, values.1, values.2.2)
    unmapValues := fun _ values => (values.2.1, values.1, values.2.2)
    map_unmap_vars := by
      intro context values
      cases values with
      | cons secondValue tail =>
          cases tail with
          | cons firstValue restValues => rfl
    unmap_map_vars := by
      intro context values
      cases values with
      | cons firstValue tail =>
          cases tail with
          | cons secondValue restValues => rfl
    map_unmap_values := by
      intro model values
      cases values with
      | mk secondValue tail =>
          cases tail with
          | mk firstValue restValues => rfl
    unmap_map_values := by
      intro model values
      cases values with
      | mk firstValue tail =>
          cases tail with
          | mk secondValue restValues => rfl
    evaluate_map := by
      intro context model variables env
      cases variables with
      | cons firstValue tail =>
          cases tail with
          | cons secondValue restValues => rfl
    evaluate_unmap := by
      intro context model variables env
      cases variables with
      | cons secondValue tail =>
          cases tail with
          | cons firstValue restValues => rfl
  }
  map_natural := by
    intro before after variables rename
    cases variables with
    | cons firstValue tail =>
        cases tail with
        | cons secondValue restValues => rfl
}

/-- Keep one leading typed position while applying a permutation to the
remaining positions. -/
private def keepHead (signature : Sig)
    (permutation : TypedPermutation source target) :
    TypedPermutation (signature :: source) (signature :: target) := {
  value := {
    mapVars := fun
      | .cons head tail => .cons head (permutation.value.mapVars tail)
    unmapVars := fun
      | .cons head tail => .cons head (permutation.value.unmapVars tail)
    mapValues := fun model values =>
      (values.1, permutation.value.mapValues model values.2)
    unmapValues := fun model values =>
      (values.1, permutation.value.unmapValues model values.2)
    map_unmap_vars := by
      intro context variables
      cases variables with
      | cons head tail =>
          exact congrArg (Vars.cons head)
            (permutation.value.map_unmap_vars tail)
    unmap_map_vars := by
      intro context variables
      cases variables with
      | cons head tail =>
          exact congrArg (Vars.cons head)
            (permutation.value.unmap_map_vars tail)
    map_unmap_values := by
      intro model values
      cases values with
      | mk head tail =>
          exact congrArg (Prod.mk head)
            (permutation.value.map_unmap_values model tail)
    unmap_map_values := by
      intro model values
      cases values with
      | mk head tail =>
          exact congrArg (Prod.mk head)
            (permutation.value.unmap_map_values model tail)
    evaluate_map := by
      intro context model variables env
      cases variables with
      | cons head tail =>
          exact congrArg (Prod.mk (env.lookup head))
            (permutation.value.evaluate_map model tail env)
    evaluate_unmap := by
      intro context model variables env
      cases variables with
      | cons head tail =>
          exact congrArg (Prod.mk (env.lookup head))
            (permutation.value.evaluate_unmap model tail env)
  }
  map_natural := by
    intro before after variables rename
    cases variables with
    | cons head tail =>
        exact congrArg (Vars.cons (rename head))
          (permutation.map_natural tail rename)
}

end TypedPermutation

@[simp] private theorem duplicateAt_map
    (before : List Sig)
    (variables : Vars source (before ++ signature :: after))
    (rename : WireRenaming source target) :
    (Argument.Duplicate.Vars.duplicateAt before variables).map
        (fun wire => rename wire) =
      Argument.Duplicate.Vars.duplicateAt before
        (variables.map fun wire => rename wire) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          exact congrArg (Vars.cons (rename first)) (induction rest)

@[simp] private theorem dropAt_insertAt
    (before : List Sig) (inserted : Var context signature)
    (variables : Vars context (before ++ after)) :
    Argument.Projection.Vars.dropAt before
        (Argument.Projection.Vars.insertAt before inserted variables) =
      variables := by
  induction before with
  | nil => rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          exact congrArg (Vars.cons first) (induction rest)

@[simp] private theorem dropAt_map
    (before : List Sig)
    (variables : Vars source (before ++ signature :: after))
    (rename : WireRenaming source target) :
    (Argument.Projection.Vars.dropAt before variables).map
        (fun wire => rename wire) =
      Argument.Projection.Vars.dropAt before
        (variables.map fun wire => rename wire) := by
  induction before with
  | nil => cases variables; rfl
  | cons head tail induction =>
      cases variables with
      | cons first rest =>
          exact congrArg (Vars.cons (rename first)) (induction rest)

/-- A syntax-indexed factor from one typed argument vector to another.  Its
constructors are exactly the three argument primitives used by the compiler,
plus reflexive and transitive composition. -/
private inductive VarsFactor {context : List Sig} :
    {source target : List Sig} →
      Vars context source → Vars context target → Prop
  | refl (variables : Vars context arguments) :
      VarsFactor variables variables
  | permute (permutation : TypedPermutation source target)
      (variables : Vars context source) :
      VarsFactor variables (permutation.value.mapVars variables)
  | contract (before : List Sig)
      (variables : Vars context (before ++ signature :: after)) :
      VarsFactor (Argument.Duplicate.Vars.duplicateAt before variables)
        variables
  | extend (before : List Sig) (inserted : Var context signature)
      (variables : Vars context (before ++ after)) :
      VarsFactor variables
        (Argument.Projection.Vars.insertAt before inserted variables)
  | trans (first : VarsFactor source middle)
      (second : VarsFactor middle target) :
      VarsFactor source target

namespace VarsFactor

/-- A fixed syntax factor survives every ambient wire substitution. -/
private theorem natural
    {before sourceArguments targetArguments : List Sig}
    {source : Vars before sourceArguments}
    {target : Vars before targetArguments}
    (factor : VarsFactor source target)
    (rename : WireRenaming before after) :
    VarsFactor (source.map fun wire => rename wire)
      (target.map fun wire => rename wire) := by
  induction factor with
  | refl variables => exact .refl _
  | @permute sourceArguments targetArguments permutation variables =>
      rw [permutation.map_natural]
      exact .permute permutation _
  | contract position variables =>
      rw [duplicateAt_map]
      exact .contract position _
  | extend position inserted variables =>
      rw [Argument.Projection.Vars.insertAt_map]
      exact .extend position (rename inserted) _
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

/-- Keep one leading argument while applying a factor to the tail. -/
private theorem keepHead (head : Var context signature)
    (factor : VarsFactor source target) :
    VarsFactor (.cons head source) (.cons head target) := by
  induction factor with
  | refl variables => exact .refl _
  | @permute sourceArguments targetArguments permutation variables =>
      exact .permute (TypedPermutation.keepHead signature permutation)
        (.cons head variables)
  | contract position variables =>
      exact .contract (signature :: position) (.cons head variables)
  | extend position inserted variables =>
      exact .extend (signature :: position) inserted (.cons head variables)
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

/-- Normalize all occurrences of the leading context wire to one leading
argument, preserving the remaining selection over the tail context. -/
private theorem factorHead
    (selection : Vars (signature :: context) arguments) :
    ∃ (tailArguments : List Sig) (tail : Vars context tailArguments),
      VarsFactor selection
        (.cons .here (tail.map fun wire => .there wire)) := by
  induction selection with
  | nil =>
      exact ⟨[], .nil, .extend [] (.here : Var (signature :: context) signature)
        .nil⟩
  | @cons selectedSignature rest selected tail induction =>
      obtain ⟨tailArguments, normalizedTail, tailFactor⟩ := induction
      cases selected with
      | here =>
          let retained : Vars (signature :: context)
              (signature :: tailArguments) :=
            .cons .here (normalizedTail.map fun wire => .there wire)
          exact ⟨tailArguments, normalizedTail,
            (tailFactor.keepHead
              (.here : Var (signature :: context) signature)).trans
              (.contract [] retained)⟩
      | there tailSelected =>
          let swapped := TypedPermutation.swapHead selectedSignature signature
            tailArguments
          exact ⟨selectedSignature :: tailArguments,
            .cons tailSelected normalizedTail,
            (tailFactor.keepHead (.there tailSelected)).trans
              (.permute swapped
                (.cons (.there tailSelected)
                  (.cons .here
                    (normalizedTail.map fun wire => .there wire))))⟩

/-- Every syntax selection factors to the ordered identity vector.  The proof
is structural in the source context and never compares substituted site
wires. -/
private theorem factorSelection
    (selection : Vars patternWires supportArguments) :
    VarsFactor selection
      (Erasure.Exposure.identityBoundary patternWires) := by
  induction patternWires generalizing supportArguments with
  | nil =>
      cases selection with
      | nil => exact .refl .nil
      | cons head tail => exact nomatch head
  | cons signature context induction =>
      obtain ⟨tailArguments, tail, headFactor⟩ := factorHead selection
      let tailRename : WireRenaming context (signature :: context) :=
        ⟨fun wire => .there wire⟩
      have tailFactor := (induction tail).natural tailRename
      exact headFactor.trans
        (tailFactor.keepHead (.here : Var (signature :: context) signature))

end VarsFactor

/-! Positional atom support.  The support context contains one distinct wire
for the atom head and one distinct wire for every port position.  Its collapse
renaming is allowed to identify those syntax positions in the ambient
pattern; the support pattern itself remains linear and canonical. -/

private def atomSupportWires (arguments : List Sig) : List Sig :=
  .rel arguments :: arguments

private def atomSupportHead (arguments : List Sig) :
    Var (atomSupportWires arguments) (.rel arguments) :=
  .here

private def atomSupportPorts (arguments : List Sig) :
    Vars (atomSupportWires arguments) arguments :=
  (Erasure.Exposure.identityBoundary arguments).map fun wire => .there wire

private def atomSupportItem (arguments : List Sig) :
    Item (atomSupportWires arguments) :=
  .atom (atomSupportHead arguments) (atomSupportPorts arguments)

private def atomSelection
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) :
    Vars patternWires (atomSupportWires atomArguments) :=
  .cons head ports

private def atomSupportCollapse
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) :
    WireRenaming (atomSupportWires atomArguments) patternWires :=
  EqualityNormalization.formalSubstitution (atomSelection head ports)

private theorem Vars.countIndex_map_of_index
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (indexEq : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val)
    (index : Nat) :
    (variables.map fun wire => rename wire).countIndex index =
      variables.countIndex index := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, indexEq head, induction]

@[simp] private theorem atomSupportItem_rename
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) :
    (atomSupportItem atomArguments).renameWires
    (atomSupportCollapse head ports) =
      .atom head ports := by
  let tailRename : WireRenaming atomArguments
      (atomSupportWires atomArguments) := ⟨fun wire => .there wire⟩
  let collapse := atomSupportCollapse head ports
  have portsEq : (atomSupportPorts atomArguments).map
      (fun wire => collapse wire) = ports := by
    calc
      (atomSupportPorts atomArguments).map (fun wire => collapse wire) =
          (Erasure.Exposure.identityBoundary atomArguments).map
            (fun wire => collapse (tailRename wire)) := by
              simpa only [atomSupportPorts, tailRename] using
                Diagram.vars_map_comp
                  (Erasure.Exposure.identityBoundary atomArguments)
                  tailRename collapse
      _ = ports := by
        change (Erasure.Exposure.identityBoundary atomArguments).map
            (fun wire =>
              EqualityNormalization.formalSubstitution ports wire) = ports
        exact EqualityNormalization.formalPorts_map_substitution ports
  change Item.atom (collapse (atomSupportHead atomArguments))
      ((atomSupportPorts atomArguments).map fun wire => collapse wire) =
    Item.atom head ports
  rw [show collapse (atomSupportHead atomArguments) = head by rfl, portsEq]

private theorem atomSupportCanonical (arguments : List Sig) :
    (Region.singleton (atomSupportItem arguments)).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

private theorem atomSupportBoundarySurjective
    (wire : Fin (atomSupportWires arguments).length) :
    ∃ position : Fin (atomSupportWires arguments).length,
      ((Erasure.Exposure.identityBoundary
        (atomSupportWires arguments)).get position).index = wire := by
  exact ⟨wire, Erasure.Exposure.identityBoundary_get_index wire⟩

private theorem atomSupportExternalTwoEnded (arguments : List Sig) :
    OpenDiagram.ExternalTwoEnded
      (Erasure.Exposure.identityBoundary (atomSupportWires arguments))
      (Region.singleton (atomSupportItem arguments)) := by
  intro signature wire
  have boundaryPositive : 0 <
      (Erasure.Exposure.identityBoundary
        (atomSupportWires arguments)).countIndex wire.index.val := by
    have positive :=
      (Erasure.Exposure.identityBoundary (atomSupportWires arguments))
        |>.countIndex_get_positive wire.index
    rw [Erasure.Exposure.identityBoundary_get_index] at positive
    exact positive
  have bodyPositive : 0 <
      ((Region.singleton (atomSupportItem arguments)).incidencePaths
        wire.index.val).length := by
    simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
      ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
      Item.incidencePaths, List.append_nil, List.length_replicate,
      Var.index_appendLeft, atomSupportItem, atomSupportHead]
    let appendNil : WireRenaming (atomSupportWires arguments)
        (atomSupportWires arguments ++ []) :=
      ⟨fun wire => wire.appendLeft []⟩
    have portCountEq :
        ((atomSupportPorts arguments).map
          (fun wire => appendNil wire)).countIndex wire.index.val =
        (atomSupportPorts arguments).countIndex wire.index.val := by
      exact Vars.countIndex_map_of_index (atomSupportPorts arguments)
        appendNil (fun selected => Var.index_appendLeft selected [])
          wire.index.val
    rw [show ((atomSupportPorts arguments).map
        (fun wire => wire.appendLeft [])).countIndex wire.index.val =
          (atomSupportPorts arguments).countIndex wire.index.val by
      simpa only [appendNil] using portCountEq]
    change 0 <
      (Erasure.Exposure.identityBoundary
        (atomSupportWires arguments)).countIndex wire.index.val
    exact boundaryPositive
  omega

private theorem atomSupportIncidenceNonempty
    (arguments : List Sig) (wire : Var (atomSupportWires arguments) signature) :
    (Region.singleton (atomSupportItem arguments)).incidencePaths
      wire.index.val ≠ [] := by
  have boundaryPositive : 0 <
      (Erasure.Exposure.identityBoundary
        (atomSupportWires arguments)).countIndex wire.index.val := by
    have positive :=
      (Erasure.Exposure.identityBoundary (atomSupportWires arguments))
        |>.countIndex_get_positive wire.index
    rw [Erasure.Exposure.identityBoundary_get_index] at positive
    exact positive
  rw [← List.length_pos_iff]
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, List.length_replicate,
    Var.index_appendLeft, atomSupportItem, atomSupportHead]
  let appendNil : WireRenaming (atomSupportWires arguments)
      (atomSupportWires arguments ++ []) :=
    ⟨fun selected => selected.appendLeft []⟩
  have portCountEq :
      ((atomSupportPorts arguments).map
        (fun selected => appendNil selected)).countIndex wire.index.val =
      (atomSupportPorts arguments).countIndex wire.index.val :=
    Vars.countIndex_map_of_index (atomSupportPorts arguments) appendNil
      (fun selected => Var.index_appendLeft selected []) wire.index.val
  rw [show ((atomSupportPorts arguments).map
      (fun selected => selected.appendLeft [])).countIndex wire.index.val =
        (atomSupportPorts arguments).countIndex wire.index.val by
    simpa only [appendNil] using portCountEq]
  change 0 <
    (Erasure.Exposure.identityBoundary
      (atomSupportWires arguments)).countIndex wire.index.val
  exact boundaryPositive

private def atomFormalShape (arguments : List Sig) :
    FormalShape (atomSupportHead arguments) (atomSupportPorts arguments) := {
  before := []
  after := arguments
  formal := atomSupportHead arguments
  retained := atomSupportPorts arguments
  head_eq := HEq.rfl
  ports_eq := HEq.rfl
  boundaryWire :=
    Erasure.Exposure.identityBoundary (atomSupportWires arguments)
  boundary_eq := rfl
  boundarySurjective := atomSupportBoundarySurjective
  canonical := atomSupportCanonical arguments
  externalTwoEnded := atomSupportExternalTwoEnded arguments
}

private theorem atomSupportPins_eq_nil (arguments : List Sig) :
    Erasure.Exposure.supportPins
      (Region.singleton (atomSupportItem arguments))
      (atomSupportWires arguments)
      (Erasure.Exposure.identityBoundary (atomSupportWires arguments)) =
        .nil := by
  apply EqualityNormalization.supportPins_eq_nil
  intro position
  exact atomSupportIncidenceNonempty arguments
    ((Erasure.Exposure.identityBoundary
      (atomSupportWires arguments)).get position)

private theorem atomSupportBody_eq (arguments : List Sig) :
    Erasure.Exposure.supportBody
      (Region.singleton (atomSupportItem arguments)) =
        Region.singleton (atomSupportItem arguments) := by
  exact EqualityNormalization.supportBody_eq_of_supportPins_nil _
    (atomSupportPins_eq_nil arguments)

private theorem atomSupportPattern_eq (arguments : List Sig) :
    Erasure.Exposure.supportPattern
      (Region.singleton (atomSupportItem arguments))
      (atomSupportCanonical arguments) =
        (atomFormalShape arguments).pattern := by
  apply EqualityNormalization.OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq (atomSupportBody_eq arguments)

/-! Exact first-item presentation of one selected application of an
identity-boundary cons pattern.  The host is everything except the atom head:
the sibling tail followed by the authoritative boundary equalities. -/

private def atomBodyWire
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (common : List Sig) :
    WireRenaming patternWires
      (common ++ EqualityNormalization.locals shape.pattern) :=
  let appendNil : WireRenaming patternWires (patternWires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  WireRenaming.comp
    (EqualityNormalization.bodyEmbedding shape.pattern common) appendNil

private def atomSiteHostItems
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    ItemSeq (common ++ EqualityNormalization.locals shape.pattern) :=
  (tail.renameWires (atomBodyWire shape common)).append
    (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      (application.map fun wire =>
        EqualityNormalization.actualEmbedding shape.pattern common wire)
      (shape.pattern.boundaryWire.map fun wire =>
        EqualityNormalization.patternEmbedding shape.pattern common wire))

private theorem atomInstantiationItems_eq
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    EqualityNormalization.items shape.pattern application =
      .cons
        (.atom (atomBodyWire shape common head)
          (ports.map fun wire => atomBodyWire shape common wire))
        (atomSiteHostItems shape application) := by
  let appendNil : WireRenaming patternWires (patternWires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  let embedding := EqualityNormalization.bodyEmbedding shape.pattern common
  have headEq : embedding (appendNil head) = atomBodyWire shape common head :=
    rfl
  have portsEq :
      (ports.map fun wire => appendNil wire).map
          (fun wire => embedding wire) =
        ports.map (fun wire => atomBodyWire shape common wire) := by
    simpa only [embedding, appendNil, atomBodyWire, WireRenaming.comp] using
      Diagram.vars_map_comp ports appendNil embedding
  have tailEq :
      (tail.renameWires appendNil).renameWires embedding =
        tail.renameWires (atomBodyWire shape common) := by
    simpa only [embedding, appendNil, atomBodyWire] using
      ItemSeq.renameWires_comp tail appendNil embedding
  have bodyItems : shape.pattern.body.items =
      (ItemSeq.cons (.atom head ports) tail).renameWires appendNil := by
    rfl
  simp only [EqualityNormalization.items]
  rw [bodyItems]
  simp only [ItemSeq.renameWires, Item.renameWires]
  rw [headEq, portsEq, tailEq]
  rfl

private def atomExposureDescription
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    Rule.Erasure.Description common where
  materialWires := atomSupportWires atomArguments
  hostLocals := EqualityNormalization.locals shape.pattern
  hostItems := atomSiteHostItems shape application
  material := Region.singleton (atomSupportItem atomArguments)
  wireMap := WireRenaming.comp (atomBodyWire shape common)
    (atomSupportCollapse head ports)

private theorem atomExposureApplicationPorts
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    Erasure.Exposure.applicationPorts
        (atomExposureDescription shape application) =
      .cons (atomBodyWire shape common head)
        (ports.map fun wire => atomBodyWire shape common wire) := by
  change (Erasure.Exposure.identityBoundary
      (atomSupportWires atomArguments)).map
        (fun wire =>
          atomBodyWire shape common (atomSupportCollapse head ports wire)) = _
  rw [← EqualityNormalization.formalPorts_eq_exposure]
  rw [← Diagram.vars_map_comp
    (EqualityNormalization.formalPorts (atomSupportWires atomArguments))
    (atomSupportCollapse head ports) (atomBodyWire shape common)]
  rw [show (EqualityNormalization.formalPorts
      (atomSupportWires atomArguments)).map
        (fun wire => atomSupportCollapse head ports wire) =
      atomSelection head ports by
    exact EqualityNormalization.formalPorts_map_substitution
      (atomSelection head ports)]
  rfl

private theorem canonical_of_eq
    {before after : Region wires} (equality : before = after)
    (canonical : after.Canonical) : before.Canonical := by
  rw [equality]
  exact canonical

private theorem atomExposureMaterialRename
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    (Region.singleton (atomSupportItem atomArguments)).renameWires
        (atomExposureDescription shape application).wireMap =
      Region.singleton
        (.atom (atomBodyWire shape common head)
          (ports.map fun wire => atomBodyWire shape common wire)) := by
  change (Region.singleton (atomSupportItem atomArguments)).renameWires
      (WireRenaming.comp (atomBodyWire shape common)
        (atomSupportCollapse head ports)) = _
  rw [← Region.renameWires_comp]
  rw [Region.singleton_renameWires, atomSupportItem_rename,
    Region.singleton_renameWires]
  rfl

private def atomSelectedItem
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (common : List Sig) :
    Item (common ++ EqualityNormalization.locals shape.pattern) :=
  .atom (atomBodyWire shape common head)
    (ports.map fun wire => atomBodyWire shape common wire)

private theorem atomInstantiation_eq
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        shape.pattern application =
      Region.mk (EqualityNormalization.locals shape.pattern)
        (.cons (atomSelectedItem shape common)
          (atomSiteHostItems shape application)) := by
  rw [EqualityNormalization.instantiate_eq_presentation,
    atomInstantiationItems_eq]
  rfl

private theorem atomExposureWires_nonempty
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (common : List Sig) :
    common ++ EqualityNormalization.locals shape.pattern ≠ [] := by
  intro empty
  have localsEmpty : EqualityNormalization.locals shape.pattern = [] :=
    (List.append_eq_nil_iff.mp empty).2
  have patternEmpty : patternWires = [] := by
    have both : patternWires = [] ∧
        (Region.ofItems (.cons (.atom head ports) tail)).locals = [] := by
      simpa [EqualityNormalization.locals, PatternShape.pattern] using
        localsEmpty
    exact both.1
  subst patternWires
  exact Fin.elim0 head.index

private noncomputable def atomExposureSourceIso
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    RegionIso (WireEquiv.refl common)
      (atomExposureDescription shape application).source
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        shape.pattern application) := by
  let selected := atomSelectedItem shape common
  let materialIso : RegionIso
      (WireEquiv.refl
        (common ++ EqualityNormalization.locals shape.pattern))
      ((Region.singleton (atomSupportItem atomArguments)).renameWires
        (atomExposureDescription shape application).wireMap)
      (Region.singleton selected) := by
    exact RegionIso.ofEq (atomExposureMaterialRename shape application)
  let adjoined := RegionIso.adjoinAt
    (EqualityNormalization.locals shape.pattern)
    (atomSiteHostItems shape application) materialIso
  let flattened := RegionIso.adjoinAtSingleton
    (EqualityNormalization.locals shape.pattern)
    (atomSiteHostItems shape application) selected
  let front := RegionIso.appendSingletonFront
    (EqualityNormalization.locals shape.pattern)
    (atomSiteHostItems shape application) selected
  rw [atomInstantiation_eq shape application]
  let combined := (adjoined.trans flattened).trans front
  simpa only [Rule.Erasure.Description.source, Region.spliceAt,
    atomExposureDescription, selected, WireEquiv.refl_trans] using combined

private def atomPinnedExposureDescription
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    Rule.Erasure.Description common :=
  let raw := atomExposureDescription shape application
  {
    materialWires := raw.materialWires
    hostLocals := raw.hostLocals
    hostItems := raw.hostItems.append
      (EqualityNormalization.contextPins common raw.hostLocals)
    material := raw.material
    wireMap := raw.wireMap
  }

private theorem atomSelectedCanonical
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    (Region.singleton (.atom head ports)).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

private theorem atomPinnedHostCanonical
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    (Region.mk (EqualityNormalization.locals shape.pattern)
      ((atomSiteHostItems shape application).append
        (EqualityNormalization.contextPins common
          (EqualityNormalization.locals shape.pattern)))).Canonical := by
  let locals := EqualityNormalization.locals shape.pattern
  let hostItems := atomSiteHostItems shape application
  have sourceCanonical :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
      shape.pattern application
  rw [atomInstantiation_eq shape application] at sourceCanonical
  constructor
  · intro localIndex
    let localWire := Var.appendRight common (Var.ofIndex localIndex)
    have pinRoot := EqualityNormalization.allPins_twice_rooted
      (common ++ locals) WireRenaming.id localWire hostItems.length
    rw [ItemSeq.incidencePaths_append]
    apply RegionPath.RootedTwo.of_sublist
      (List.sublist_append_right _ _)
    simpa [EqualityNormalization.contextPins, locals, localWire, hostItems,
      WireRenaming.id] using pinRoot
  · apply (ItemSeq.childrenCanonical_append _ _).mpr
    constructor
    · simpa only [locals, hostItems] using sourceCanonical.2.2
    · exact EqualityNormalization.allPins_twice_childrenCanonical
        (common ++ locals) WireRenaming.id

private def atomPinnedRawRegion
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) : Region common :=
  let locals := EqualityNormalization.locals shape.pattern
  let items : ItemSeq (common ++ locals) :=
    ItemSeq.cons (atomSelectedItem shape common)
    (atomSiteHostItems shape application)
  let pins : ItemSeq (common ++ locals) :=
    EqualityNormalization.allPins (common ++ locals)
    WireRenaming.id
  .mk locals ((items.append pins).append pins)

private noncomputable def atomPinnedSourceIso
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    RegionIso (WireEquiv.refl common)
      (atomPinnedExposureDescription shape application).source
      (atomPinnedRawRegion shape application) := by
  let locals := EqualityNormalization.locals shape.pattern
  let selected := atomSelectedItem shape common
  let pinnedHost := (atomSiteHostItems shape application).append
    (EqualityNormalization.contextPins common locals)
  let materialIso : RegionIso (WireEquiv.refl (common ++ locals))
      ((Region.singleton (atomSupportItem atomArguments)).renameWires
        (atomExposureDescription shape application).wireMap)
      (Region.singleton selected) := by
    exact RegionIso.ofEq (atomExposureMaterialRename shape application)
  let adjoined := RegionIso.adjoinAt locals pinnedHost
    materialIso
  let flattened := RegionIso.adjoinAtSingleton locals pinnedHost selected
  let front := RegionIso.appendSingletonFront locals pinnedHost selected
  let combined := (adjoined.trans flattened).trans front
  simpa only [atomPinnedExposureDescription, atomExposureDescription,
    Rule.Erasure.Description.source, Region.spliceAt, locals, selected,
    pinnedHost, atomPinnedRawRegion, EqualityNormalization.contextPins,
    ItemSeq.append_assoc, WireEquiv.refl_trans] using combined

private theorem atomPinnedRaw_incidence_nonempty
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires)
    (wire : Var common signature) :
    (atomPinnedRawRegion shape application).incidencePaths
      wire.index.val ≠ [] := by
  let locals := EqualityNormalization.locals shape.pattern
  let base : ItemSeq (common ++ locals) :=
    .cons (atomSelectedItem shape common)
      (atomSiteHostItems shape application)
  let embedded := wire.appendLeft locals
  have pinsNonempty := EqualityNormalization.contextPins_incidence_nonempty
    common locals embedded base.length
  simp only [atomPinnedRawRegion, Region.incidencePaths]
  rw [ItemSeq.append_assoc, ItemSeq.incidencePaths_append]
  apply List.append_ne_nil_of_right_ne_nil
  simpa [EqualityNormalization.contextPins, locals, embedded,
    Var.index_appendLeft, base] using pinsNonempty

private theorem atomPinnedSource_incidence_nonempty
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires)
    (wire : Var common signature) :
    (atomPinnedExposureDescription shape application).source.incidencePaths
      wire.index.val ≠ [] := by
  let locals := EqualityNormalization.locals shape.pattern
  let hostItems := atomSiteHostItems shape application
  let pinnedItems := hostItems.append
    (EqualityNormalization.contextPins common locals)
  have hostNonempty := EqualityNormalization.pinnedHost_incidence_nonempty
    locals hostItems wire
  have sublist := Region.incidencePaths_adjoinAt_host_sublist
    locals pinnedItems
    ((Region.singleton (atomSupportItem atomArguments)).renameWires
      (atomExposureDescription shape application).wireMap) wire
  have positive := Nat.lt_of_lt_of_le
    (List.length_pos_iff.mpr (by
      simpa only [locals, hostItems, pinnedItems] using hostNonempty))
    sublist.length_le
  simpa only [atomPinnedExposureDescription, atomExposureDescription,
    Rule.Erasure.Description.source, Region.spliceAt, locals, hostItems,
    pinnedItems] using List.length_pos_iff.mp positive

private theorem atomSiteExposurePinned
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        shape.pattern application) source) :
    let description := atomPinnedExposureDescription shape application
    ∃ targetCanonical :
        (occurrence.context.fill
          (Erasure.Exposure.exposedRegion description
            (atomSupportCanonical atomArguments))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Erasure.Exposure.exposedRegion description
              (atomSupportCanonical atomArguments))),
        Equates occurrence
          (Erasure.Exposure.exposedRegion description
            (atomSupportCanonical atomArguments))
          targetCanonical targetExternalTwoEnded := by
  dsimp only
  let description := atomPinnedExposureDescription shape application
  let locals := EqualityNormalization.locals shape.pattern
  let baseItems : ItemSeq (common ++ locals) :=
    .cons (atomSelectedItem shape common)
      (atomSiteHostItems shape application)
  have baseSourceCanonical :
      (occurrence.context.fill (.mk locals baseItems)).Canonical := by
    rw [← atomInstantiation_eq shape application]
    exact occurrence.sourceCanonical
  have baseSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (.mk locals baseItems)) := by
    intro signature wire
    rw [← atomInstantiation_eq shape application]
    exact occurrence.sourceExternalTwoEnded wire
  let baseBodyIso := DiagramContext.fillIso occurrence.context
    (RegionIso.ofEq (atomInstantiation_eq shape application))
  let baseEndpointIso : OpenDiagramIso
      (occurrence.interface.withBody
        (occurrence.context.fill
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            shape.pattern application))
        occurrence.sourceCanonical occurrence.sourceExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill (.mk locals baseItems))
        baseSourceCanonical baseSourceExternalTwoEnded) :=
    OpenDiagram.withBody_iso occurrence.sourceCanonical baseSourceCanonical
      occurrence.sourceExternalTwoEnded baseSourceExternalTwoEnded baseBodyIso
  have baseHostIso : OpenDiagramIso source
      (occurrence.interface.withBody
        (occurrence.context.fill (.mk locals baseItems))
        baseSourceCanonical baseSourceExternalTwoEnded) :=
    occurrence.host_iso.trans baseEndpointIso
  let baseOccurrence : Occurrence (.mk locals baseItems) source := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := baseSourceCanonical
    sourceExternalTwoEnded := baseSourceExternalTwoEnded
    host_iso := baseHostIso
  }
  obtain ⟨rawCanonical, rawExternalTwoEnded, rawSteps⟩ :=
    EqualityNormalization.pinAllTwiceOfNonempty baseOccurrence
      (WireRenaming.id : WireRenaming (common ++ locals)
        (common ++ locals))
      (atomExposureWires_nonempty shape common)
  let rawRegion := atomPinnedRawRegion shape application
  have rawCanonical' :
      (occurrence.context.fill rawRegion).Canonical := by
    simpa only [baseOccurrence, locals, baseItems, rawRegion,
      atomPinnedRawRegion] using rawCanonical
  have rawExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill rawRegion) := by
    intro signature wire
    simpa only [baseOccurrence, locals, baseItems, rawRegion,
      atomPinnedRawRegion] using rawExternalTwoEnded wire
  let rawEndpoint := occurrence.interface.withBody
    (occurrence.context.fill rawRegion) rawCanonical'
      rawExternalTwoEnded'
  have rawForward : Relation.TransGen Step source rawEndpoint := by
    simpa only [baseOccurrence, locals, baseItems, rawRegion,
      atomPinnedRawRegion, rawEndpoint] using rawSteps.1
  have rawReverse : Relation.TransGen Step rawEndpoint source := by
    simpa only [baseOccurrence, locals, baseItems, rawRegion,
      atomPinnedRawRegion, rawEndpoint] using rawSteps.2
  let rawOccurrence : Occurrence rawRegion rawEndpoint :=
    exactOccurrence occurrence.interface occurrence.context rawRegion
      rawCanonical' rawExternalTwoEnded'
  let pinnedHost := (atomSiteHostItems shape application).append
    (EqualityNormalization.contextPins common locals)
  have pinnedHostCanonical : (Region.mk locals pinnedHost).Canonical := by
    simpa only [locals, pinnedHost] using
      atomPinnedHostCanonical shape application
  have pinnedSourceLocalCanonical : description.source.Canonical := by
    change (Region.adjoinAt locals pinnedHost
      ((Region.singleton (atomSupportItem atomArguments)).renameWires
        (atomExposureDescription shape application).wireMap)).Canonical
    have materialCanonical :
        ((Region.singleton (atomSupportItem atomArguments)).renameWires
          (atomExposureDescription shape application).wireMap).Canonical :=
      canonical_of_eq (atomExposureMaterialRename shape application)
        (atomSelectedCanonical _ _)
    exact Region.Canonical.adjoinAt locals pinnedHost
      ((Region.singleton (atomSupportItem atomArguments)).renameWires
        (atomExposureDescription shape application).wireMap)
      pinnedHostCanonical materialCanonical
  have rawSourceSameNonempty : ∀ {signature} (wire : Var common signature),
      rawRegion.incidencePaths wire.index.val ≠ [] ↔
        description.source.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    exact ⟨fun _ => atomPinnedSource_incidence_nonempty shape application wire,
      fun _ => atomPinnedRaw_incidence_nonempty shape application wire⟩
  let pinnedOccurrence : Occurrence description.source rawEndpoint :=
    EqualityNormalization.presentationOccurrence rawOccurrence
      pinnedSourceLocalCanonical rawSourceSameNonempty
      (atomPinnedSourceIso shape application).symm
  have erasedLocalCanonical : description.target.Canonical := by
    simpa only [description, atomPinnedExposureDescription,
      Rule.Erasure.Description.target, locals, pinnedHost] using
      pinnedHostCanonical
  have erasedNonempty : ∀ {signature} (wire : Var common signature),
      description.target.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    simpa only [description, atomPinnedExposureDescription,
      Rule.Erasure.Description.target, locals, pinnedHost] using
      EqualityNormalization.pinnedHost_incidence_nonempty
        (EqualityNormalization.locals shape.pattern)
        (atomSiteHostItems shape application) wire
  have erasedSameNonempty : ∀ {signature} (wire : Var common signature),
      description.source.incidencePaths wire.index.val ≠ [] ↔
        description.target.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    exact ⟨fun _ => erasedNonempty wire,
      fun _ => atomPinnedSource_incidence_nonempty shape application wire⟩
  have erasedReplacement := pinnedOccurrence.context.replaceCanonical
    description.source description.target pinnedOccurrence.sourceCanonical
      erasedLocalCanonical erasedSameNonempty
  let erasedCanonical := erasedReplacement.1
  let pinnedExact := pinnedOccurrence.interface.withBody
    (pinnedOccurrence.context.fill description.source)
    pinnedOccurrence.sourceCanonical
    pinnedOccurrence.sourceExternalTwoEnded
  have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      pinnedOccurrence.interface.boundaryWire
      (pinnedOccurrence.context.fill description.target) :=
    pinnedExact.externalTwoEnded_of_nonempty_iff _ erasedReplacement.2
  obtain ⟨materialCanonical, exposedCanonical,
      exposedExternalTwoEnded, exposedEquates⟩ :=
    Erasure.Exposure.equates description pinnedOccurrence
      erasedCanonical erasedExternalTwoEnded
  have materialProof : materialCanonical =
      atomSupportCanonical atomArguments := Subsingleton.elim _ _
  subst materialCanonical
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pinnedOccurrence, rawOccurrence, description] using
      exposedCanonical
  · intro signature wire
    simpa only [pinnedOccurrence, rawOccurrence, description] using
      exposedExternalTwoEnded wire
  · have strict : EqualityNormalization.StrictEquates occurrence
        (Erasure.Exposure.exposedRegion description
          (atomSupportCanonical atomArguments)) exposedCanonical
          exposedExternalTwoEnded := by
      refine ⟨?_, ?_⟩
      · exact rawForward.reflTransGen (by
          simpa only [pinnedOccurrence, rawOccurrence] using exposedEquates.1)
      · have reverseExposure : Relation.ReflTransGen Step
            (pinnedOccurrence.interface.withBody
              (pinnedOccurrence.context.fill
                (Erasure.Exposure.exposedRegion description
                  (atomSupportCanonical atomArguments)))
              exposedCanonical exposedExternalTwoEnded)
            rawEndpoint := by
          simpa only [pinnedOccurrence, rawOccurrence] using
            exposedEquates.2
        exact reverseExposure.transGen rawReverse
    simpa only [description] using strict.toEquates

/-! An arbitrary retained host is merged into the atom exposure description
before the exposure rule is invoked.  This is the constructor needed by the
outer evidence fold: sibling material is ordinary host syntax, not another
kind of occurrence path. -/

private def atomExposureDescriptionWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    Rule.Erasure.Description outer :=
  let inner := atomExposureDescription shape application
  let innerHost : Region (outer ++ hostLocals) :=
    .mk inner.hostLocals inner.hostItems
  {
    materialWires := inner.materialWires
    hostLocals := hostLocals ++ inner.hostLocals
    hostItems := Region.extendHostItems hostLocals hostItems
      innerHost
    material := inner.material
    wireMap := WireRenaming.comp
      (Region.adjoinMaterialWire outer hostLocals inner.hostLocals)
      inner.wireMap
  }

private def atomPinnedExposureDescriptionWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    Rule.Erasure.Description outer :=
  let raw := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  {
    materialWires := raw.materialWires
    hostLocals := raw.hostLocals
    hostItems := raw.hostItems.append
      (EqualityNormalization.contextPins outer raw.hostLocals)
    material := raw.material
    wireMap := raw.wireMap
  }

private noncomputable def atomExposureDescriptionWithHost_exposedIso
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    RegionIso (WireEquiv.refl outer)
      (Erasure.Exposure.exposedRegion
        (atomExposureDescriptionWithHost shape hostLocals hostItems
          application)
        (atomSupportCanonical atomArguments))
      (Region.adjoinAt hostLocals hostItems
        (Erasure.Exposure.exposedRegion
          (atomExposureDescription shape application)
          (atomSupportCanonical atomArguments))) := by
  let inner := atomExposureDescription shape application
  let combined := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  let innerMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern inner.material
        (atomSupportCanonical atomArguments))
      (Erasure.Exposure.applicationPorts inner)
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
    inner.hostLocals
  have applicationPortsEq :
      Erasure.Exposure.applicationPorts combined =
        (Erasure.Exposure.applicationPorts inner).map
          (fun wire => assoc wire) := by
    simp only [combined, inner, assoc,
      Erasure.Exposure.applicationPorts, atomExposureDescriptionWithHost,
      atomExposureDescription]
    exact (Diagram.vars_map_comp
      (Erasure.Exposure.identityBoundary (atomSupportWires atomArguments))
      ((atomBodyWire shape (outer ++ hostLocals)).comp
        (atomSupportCollapse head ports))
      (Region.adjoinMaterialWire outer hostLocals
        (EqualityNormalization.locals shape.pattern))).symm
  have materialEq :
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern combined.material
            (atomSupportCanonical atomArguments))
          (Erasure.Exposure.applicationPorts combined) =
        innerMaterial.renameWires assoc.toRenaming := by
    rw [EqualityNormalization.instantiate_renameWires]
    rw [applicationPortsEq]
    rfl
  let flat := Region.adjoinAt (hostLocals ++ inner.hostLocals)
    (Region.extendHostItems hostLocals hostItems
      (.mk inner.hostLocals inner.hostItems))
    (innerMaterial.renameWires assoc.toRenaming)
  let nested := Region.adjoinAt hostLocals hostItems
    (Region.adjoinAt inner.hostLocals inner.hostItems innerMaterial)
  let associated := RegionIso.adjoinAtAssoc hostLocals
    hostItems inner.hostLocals inner.hostItems innerMaterial
  have combinedEq :
      Erasure.Exposure.exposedRegion combined
          (atomSupportCanonical atomArguments) = flat := by
    change Region.adjoinAt combined.hostLocals combined.hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern combined.material
          (atomSupportCanonical atomArguments))
        (Erasure.Exposure.applicationPorts combined)) = flat
    rw [materialEq]
    rfl
  have nestedEq : nested =
      Region.adjoinAt hostLocals hostItems
        (Erasure.Exposure.exposedRegion inner
          (atomSupportCanonical atomArguments)) := by
    rfl
  exact (RegionIso.ofEq combinedEq).trans
    (associated.trans (RegionIso.ofEq nestedEq))

private theorem atomExposureHostChildrenWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires)
    (sourceCanonical :
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern application)).Canonical) :
    (atomExposureDescriptionWithHost shape hostLocals hostItems application)
      |>.hostItems.ChildrenCanonical := by
  rw [atomInstantiation_eq shape application] at sourceCanonical
  simp only [Region.adjoinAt, Region.Canonical,
    ItemSeq.childrenCanonical_append] at sourceCanonical
  have hostChildren : hostItems.ChildrenCanonical :=
    (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff hostItems).mp
      sourceCanonical.2.1
  have instantiatedChildren :
      (ItemSeq.cons (atomSelectedItem shape (outer ++ hostLocals))
        (atomSiteHostItems shape application)).ChildrenCanonical :=
    (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mp
      sourceCanonical.2.2
  simp only [atomExposureDescriptionWithHost,
    atomExposureDescription, Region.extendHostItems,
    Region.locals, Region.items]
  apply (ItemSeq.childrenCanonical_append _ _).mpr
  exact ⟨
    (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff hostItems).mpr
      hostChildren,
    (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
      instantiatedChildren.2⟩

private theorem pinnedHostCanonicalOfChildren
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (children : hostItems.ChildrenCanonical) :
    (Region.mk hostLocals
      (hostItems.append
        (EqualityNormalization.contextPins outer hostLocals))).Canonical := by
  constructor
  · intro localIndex
    let localWire := Var.appendRight outer (Var.ofIndex localIndex)
    have pinRoot := EqualityNormalization.allPins_twice_rooted
      (outer ++ hostLocals) WireRenaming.id localWire hostItems.length
    rw [ItemSeq.incidencePaths_append]
    apply RegionPath.RootedTwo.of_sublist
      (List.sublist_append_right _ _)
    simpa [EqualityNormalization.contextPins, localWire,
      WireRenaming.id] using pinRoot
  · exact (ItemSeq.childrenCanonical_append _ _).mpr
      ⟨children, EqualityNormalization.allPins_twice_childrenCanonical
        (outer ++ hostLocals) WireRenaming.id⟩

private noncomputable def appendPinsTwiceIso
    {sourceOuter targetOuter pinWires : List Sig}
    {before : Region sourceOuter} {after : Region targetOuter}
    {ambient : WireEquiv sourceOuter targetOuter}
    (localIso : WireEquiv before.locals after.locals)
    (itemsIso : ItemSeqIso (ambient.append localIso)
      before.items after.items)
    (sourceRename : WireRenaming pinWires
      (sourceOuter ++ before.locals))
    (targetRename : WireRenaming pinWires
      (targetOuter ++ after.locals))
    (commutes : ∀ {signature} (wire : Var pinWires signature),
      (ambient.append localIso) (sourceRename wire) = targetRename wire) :
    RegionIso ambient
      (.mk before.locals
        ((before.items.append
          (EqualityNormalization.allPins pinWires sourceRename)).append
            (EqualityNormalization.allPins pinWires sourceRename)))
      (.mk after.locals
        ((after.items.append
          (EqualityNormalization.allPins pinWires targetRename)).append
            (EqualityNormalization.allPins pinWires targetRename))) := by
  let fullAmbient := ambient.append localIso
  let sourcePins := EqualityNormalization.allPins pinWires sourceRename
  let targetPins := EqualityNormalization.allPins pinWires targetRename
  let rawPins := ItemSeqIso.renameWires sourcePins WireRenaming.id
    fullAmbient.toRenaming fullAmbient (by
      intro signature wire
      rfl)
  have renameEq : WireRenaming.comp fullAmbient.toRenaming sourceRename =
      targetRename := by
    apply WireRenaming.ext
    exact commutes
  have renamedPins : sourcePins.renameWires fullAmbient.toRenaming =
      targetPins := by
    rw [show sourcePins = EqualityNormalization.allPins pinWires sourceRename
      by rfl]
    rw [EqualityNormalization.allPins_renameWires, renameEq]
  let pinsIso : ItemSeqIso fullAmbient sourcePins targetPins := by
    simpa only [ItemSeq.renameWires_id, renamedPins] using rawPins
  exact .mk localIso
    (ItemSeqIso.append (ItemSeqIso.append itemsIso pinsIso) pinsIso)

private def atomOriginalItemsWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    ItemSeq (outer ++
      (hostLocals ++ EqualityNormalization.locals shape.pattern)) :=
  (hostItems.renameWires
    (Region.adjoinHostWire outer hostLocals
      (EqualityNormalization.locals shape.pattern))).append
  ((ItemSeq.cons (atomSelectedItem shape (outer ++ hostLocals))
      (atomSiteHostItems shape application)).renameWires
    (Region.adjoinMaterialWire outer hostLocals
      (EqualityNormalization.locals shape.pattern)))

private def atomOriginalRegionWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) : Region outer :=
  .mk (hostLocals ++ EqualityNormalization.locals shape.pattern)
    (atomOriginalItemsWithHost shape hostLocals hostItems application)

private noncomputable def atomExposureDescriptionWithHost_source
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    RegionIso (WireEquiv.refl outer)
      (atomExposureDescriptionWithHost shape hostLocals hostItems
        application).source
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern application)) := by
  let inner := atomExposureDescription shape application
  let combined := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  let innerMaterial := inner.material.renameWires inner.wireMap
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
    inner.hostLocals
  let materialPresentation :=
    (RegionIso.renameWiresComp inner.material inner.wireMap
      assoc.toRenaming).symm
  let flatPresentation := RegionIso.adjoinAt
    (hostLocals ++ inner.hostLocals)
    (Region.extendHostItems hostLocals hostItems
      (.mk inner.hostLocals inner.hostItems))
    materialPresentation
  let associated := RegionIso.adjoinAtAssoc hostLocals
    hostItems inner.hostLocals inner.hostItems innerMaterial
  let nestedPresentation := flatPresentation.trans associated
  let sourcePresentation := nestedPresentation.trans
    (RegionIso.adjoinAt hostLocals hostItems
      (atomExposureSourceIso shape application))
  simpa only [combined, inner, innerMaterial, assoc,
    atomExposureDescriptionWithHost, Rule.Erasure.Description.source,
    Region.spliceAt, WireEquiv.adjoinMaterialAssoc] using
      sourcePresentation

private def atomExposureHostPinRename
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    WireRenaming
      (outer ++ (atomExposureDescriptionWithHost shape hostLocals hostItems
        application).hostLocals)
      (outer ++ (atomExposureDescriptionWithHost shape hostLocals hostItems
        application).source.locals) := by
  change WireRenaming
    (outer ++ (hostLocals ++ EqualityNormalization.locals shape.pattern))
    (outer ++ ((hostLocals ++ EqualityNormalization.locals shape.pattern) ++ []))
  exact Region.adjoinHostWire outer
    (hostLocals ++ EqualityNormalization.locals shape.pattern) []

private def atomRawPinnedRegionWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) : Region outer :=
  let raw := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  let pinWires := outer ++ raw.hostLocals
  let rename := atomExposureHostPinRename shape hostLocals hostItems
    application
  let pins := EqualityNormalization.allPins pinWires rename
  .mk raw.source.locals ((raw.source.items.append pins).append pins)

private theorem atomRawPinnedRegionWithHost_eq
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires) :
    atomRawPinnedRegionWithHost shape hostLocals hostItems application =
      Region.appendAdjoinedHostSuffix
        (atomExposureDescriptionWithHost shape hostLocals hostItems
          application).hostLocals
        (atomExposureDescriptionWithHost shape hostLocals hostItems
          application).hostItems
        (EqualityNormalization.contextPins outer
          (atomExposureDescriptionWithHost shape hostLocals hostItems
            application).hostLocals)
        ((atomExposureDescriptionWithHost shape hostLocals hostItems
          application).material.renameWires
            (atomExposureDescriptionWithHost shape hostLocals hostItems
              application).wireMap) := by
  simp only [atomRawPinnedRegionWithHost,
    atomExposureDescriptionWithHost, atomExposureDescription,
    atomExposureHostPinRename, Region.appendAdjoinedHostSuffix,
    EqualityNormalization.contextPins, Region.renameWires, Region.locals,
    Region.items, Region.singleton, Region.ofItems,
    Rule.Erasure.Description.source, Region.spliceAt, Region.adjoinAt,
    ItemSeq.renameWires_append, ItemSeq.renameWires_comp,
    ItemSeq.append_assoc]
  rw [EqualityNormalization.allPins_renameWires]
  congr 2

private theorem atomSiteExposurePinnedWithHost
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern application)) source) :
    let description := atomPinnedExposureDescriptionWithHost shape
      hostLocals hostItems application
    ∃ targetCanonical :
        (occurrence.context.fill
          (Erasure.Exposure.exposedRegion description
            (atomSupportCanonical atomArguments))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Erasure.Exposure.exposedRegion description
              (atomSupportCanonical atomArguments))),
        Equates occurrence
          (Erasure.Exposure.exposedRegion description
            (atomSupportCanonical atomArguments))
          targetCanonical targetExternalTwoEnded := by
  dsimp only
  let raw := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  let description := atomPinnedExposureDescriptionWithHost shape hostLocals
    hostItems application
  let original := Region.adjoinAt hostLocals hostItems
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      shape.pattern application)
  let originalOccurrence : Occurrence original source := occurrence
  let sourcePresentation : RegionIso (WireEquiv.refl outer) raw.source
      original :=
    atomExposureDescriptionWithHost_source shape hostLocals hostItems
      application
  let localIso := sourcePresentation.localEquiv
  let itemsIso := sourcePresentation.itemSeqIso
  exact (by
      let sourceRename := atomExposureHostPinRename shape hostLocals
        hostItems application
      let fullAmbient := (WireEquiv.refl outer).append localIso
      let targetRename := WireRenaming.comp fullAmbient.toRenaming sourceRename
      let pinWires := outer ++ raw.hostLocals
      have pinWiresNonempty : pinWires ≠ [] := by
        simpa only [pinWires, raw, atomExposureDescriptionWithHost,
          atomExposureDescription, List.append_assoc] using
          atomExposureWires_nonempty shape (outer ++ hostLocals)
      obtain ⟨pinnedCanonical, pinnedExternalTwoEnded, pinnedSteps⟩ :=
        EqualityNormalization.pinAllTwiceRegionOfNonempty originalOccurrence
          targetRename pinWiresNonempty
      let sourcePins := EqualityNormalization.allPins pinWires sourceRename
      let targetPins := EqualityNormalization.allPins pinWires targetRename
      let rawPinned : Region outer :=
        .mk raw.source.locals
          ((raw.source.items.append sourcePins).append sourcePins)
      let originalPinned : Region outer :=
        .mk original.locals
          ((original.items.append targetPins).append targetPins)
      have rawPinnedEq : rawPinned =
          atomRawPinnedRegionWithHost shape hostLocals hostItems application := by
        rfl
      have originalPinnedCanonical :
          (originalOccurrence.context.fill originalPinned).Canonical := by
        simpa only [originalOccurrence, originalPinned, targetPins,
          pinWires, targetRename] using pinnedCanonical
      have originalPinnedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          originalOccurrence.interface.boundaryWire
          (originalOccurrence.context.fill originalPinned) := by
        intro signature wire
        simpa only [originalOccurrence, originalPinned, targetPins,
          pinWires, targetRename] using pinnedExternalTwoEnded wire
      let pinnedEndpoint := originalOccurrence.interface.withBody
        (originalOccurrence.context.fill originalPinned) originalPinnedCanonical
          originalPinnedExternalTwoEnded
      have pinnedForward : Relation.TransGen Step source pinnedEndpoint := by
        simpa only [originalOccurrence, originalPinned, targetPins,
          pinWires, targetRename, pinnedEndpoint] using pinnedSteps.1
      have pinnedReverse : Relation.TransGen Step pinnedEndpoint source := by
        simpa only [originalOccurrence, originalPinned, targetPins,
          pinWires, targetRename, pinnedEndpoint] using pinnedSteps.2
      let extended : RegionIso (WireEquiv.refl outer) rawPinned
          originalPinned := by
        simpa only [rawPinned, originalPinned, sourcePins, targetPins,
          fullAmbient] using
          appendPinsTwiceIso localIso itemsIso sourceRename targetRename
            (by intro signature wire; rfl)
      let moved := RegionIso.adjoinAtMoveHostSuffix raw.hostLocals
        raw.hostItems (EqualityNormalization.contextPins outer raw.hostLocals)
        (raw.material.renameWires raw.wireMap)
      let rawToDescription : RegionIso (WireEquiv.refl outer) rawPinned
          description.source := by
        exact (RegionIso.ofEq (rawPinnedEq.trans
          (atomRawPinnedRegionWithHost_eq shape hostLocals hostItems
            application))).trans (by
              simpa only [description,
                atomPinnedExposureDescriptionWithHost, raw] using moved)
      let pinnedPresentation : RegionIso (WireEquiv.refl outer)
          originalPinned description.source :=
        extended.symm.trans rawToDescription
      have sourceLocalCanonical :
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              shape.pattern application)).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have rawHostChildren : raw.hostItems.ChildrenCanonical := by
        simpa only [raw] using atomExposureHostChildrenWithHost shape
          hostLocals hostItems application sourceLocalCanonical
      have pinnedHostCanonical :
          (Region.mk raw.hostLocals
            (raw.hostItems.append
              (EqualityNormalization.contextPins outer raw.hostLocals)))
              |>.Canonical :=
        pinnedHostCanonicalOfChildren raw.hostLocals raw.hostItems
          rawHostChildren
      have materialCanonical :
          (raw.material.renameWires raw.wireMap).Canonical := by
        apply (Region.Canonical.renameWires_iff raw.material raw.wireMap).mpr
        simpa only [raw, atomExposureDescriptionWithHost,
          atomExposureDescription] using atomSupportCanonical atomArguments
      have descriptionSourceCanonical : description.source.Canonical := by
        change (Region.adjoinAt raw.hostLocals
          (raw.hostItems.append
            (EqualityNormalization.contextPins outer raw.hostLocals))
          (raw.material.renameWires raw.wireMap)).Canonical
        exact Region.Canonical.adjoinAt raw.hostLocals
          (raw.hostItems.append
            (EqualityNormalization.contextPins outer raw.hostLocals))
          (raw.material.renameWires raw.wireMap) pinnedHostCanonical
            materialCanonical
      have originalPinnedNonempty : ∀ {signature}
          (wire : Var outer signature),
          originalPinned.incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        let pinWire := wire.appendLeft raw.hostLocals
        have mapped : (targetRename pinWire).index.val = wire.index.val := by
          have sourceMapped : sourceRename pinWire =
              wire.appendLeft raw.source.locals := by
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (sourceRename pinWire).index.val = pinWire.index.val := by
                dsimp only [sourceRename, atomExposureHostPinRename]
                exact Region.adjoinHostWire_index_val pinWire
              _ = wire.index.val := Var.index_appendLeft wire raw.hostLocals
              _ = (wire.appendLeft raw.source.locals).index.val := by
                symm
                exact Var.index_appendLeft wire raw.source.locals
          rw [show targetRename pinWire =
            fullAmbient (sourceRename pinWire) by rfl, sourceMapped]
          exact WireEquiv.refl_append_left_index_val localIso wire
        have member := EqualityNormalization.allPins_mem_nil pinWires
          targetRename pinWire 0
        have pinsNonempty : targetPins.incidencePaths wire.index.val 0 ≠ [] := by
          rw [← mapped]
          exact List.ne_nil_of_mem member
        simp only [originalPinned, Region.incidencePaths]
        rw [EqualityNormalization.ItemSeq.incidencePaths_append_nonempty_iff]
        exact Or.inr pinsNonempty
      have descriptionSourceNonempty : ∀ {signature}
          (wire : Var outer signature),
          description.source.incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        have hostNonempty := EqualityNormalization.pinnedHost_incidence_nonempty
          raw.hostLocals raw.hostItems wire
        have sublist := Region.incidencePaths_adjoinAt_host_sublist
          raw.hostLocals
          (raw.hostItems.append
            (EqualityNormalization.contextPins outer raw.hostLocals))
          (raw.material.renameWires raw.wireMap) wire
        have positive := Nat.lt_of_lt_of_le
          (List.length_pos_iff.mpr hostNonempty) sublist.length_le
        simpa only [description, atomPinnedExposureDescriptionWithHost,
          raw, Rule.Erasure.Description.source, Region.spliceAt] using
          List.length_pos_iff.mp positive
      let pinnedOriginalOccurrence : Occurrence originalPinned
          pinnedEndpoint :=
        exactOccurrence originalOccurrence.interface originalOccurrence.context
          originalPinned originalPinnedCanonical originalPinnedExternalTwoEnded
      let exposureOccurrence : Occurrence description.source pinnedEndpoint :=
        EqualityNormalization.presentationOccurrence pinnedOriginalOccurrence
          descriptionSourceCanonical (by
            intro signature wire
            exact ⟨fun _ => descriptionSourceNonempty wire,
              fun _ => originalPinnedNonempty wire⟩)
          pinnedPresentation
      have erasedLocalCanonical : description.target.Canonical := by
        simpa only [description, atomPinnedExposureDescriptionWithHost,
          raw, Rule.Erasure.Description.target] using pinnedHostCanonical
      have erasedNonempty : ∀ {signature} (wire : Var outer signature),
          description.target.incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        simpa only [description, atomPinnedExposureDescriptionWithHost,
          raw, Rule.Erasure.Description.target] using
          EqualityNormalization.pinnedHost_incidence_nonempty
            raw.hostLocals raw.hostItems wire
      have erasedReplacement := exposureOccurrence.context.replaceCanonical
        description.source description.target exposureOccurrence.sourceCanonical
          erasedLocalCanonical (by
            intro signature wire
            exact ⟨fun _ => erasedNonempty wire,
              fun _ => descriptionSourceNonempty wire⟩)
      let exposureSourceEndpoint := exposureOccurrence.interface.withBody
        (exposureOccurrence.context.fill description.source)
        exposureOccurrence.sourceCanonical
        exposureOccurrence.sourceExternalTwoEnded
      have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          exposureOccurrence.interface.boundaryWire
          (exposureOccurrence.context.fill description.target) :=
        exposureSourceEndpoint.externalTwoEnded_of_nonempty_iff _
          erasedReplacement.2
      obtain ⟨foundMaterialCanonical, exposedCanonical,
          exposedExternalTwoEnded, exposedEquates⟩ :=
        Erasure.Exposure.equates description exposureOccurrence
          erasedReplacement.1 erasedExternalTwoEnded
      have materialProof : foundMaterialCanonical =
          atomSupportCanonical atomArguments := Subsingleton.elim _ _
      subst foundMaterialCanonical
      refine ⟨?_, ?_, ?_⟩
      · simpa only [exposureOccurrence,
          EqualityNormalization.presentationOccurrence_context,
          pinnedOriginalOccurrence,
          originalOccurrence, description] using exposedCanonical
      · intro signature wire
        simpa only [exposureOccurrence,
          EqualityNormalization.presentationOccurrence_interface,
          EqualityNormalization.presentationOccurrence_context,
          pinnedOriginalOccurrence,
          originalOccurrence, description] using exposedExternalTwoEnded wire
      · have strict : EqualityNormalization.StrictEquates originalOccurrence
            (Erasure.Exposure.exposedRegion description
              (atomSupportCanonical atomArguments)) exposedCanonical
              exposedExternalTwoEnded := by
          refine ⟨?_, ?_⟩
          · exact pinnedForward.reflTransGen (by
              simpa only [exposureOccurrence, pinnedOriginalOccurrence] using
                exposedEquates.1)
          · have reverseExposure : Relation.ReflTransGen Step
                (exposureOccurrence.interface.withBody
                  (exposureOccurrence.context.fill
                    (Erasure.Exposure.exposedRegion description
                      (atomSupportCanonical atomArguments)))
                  exposedCanonical exposedExternalTwoEnded)
                pinnedEndpoint := by
              simpa only [exposureOccurrence, pinnedOriginalOccurrence] using
                exposedEquates.2
            exact reverseExposure.transGen pinnedReverse
        simpa only [originalOccurrence, description] using strict.toEquates
    )

private theorem atomExposedSelectedWithHostStrict
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostLocals : List Sig)
    (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternWires)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern application)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (Erasure.Exposure.exposedRegion
            (atomExposureDescription shape application)
            (atomSupportCanonical atomArguments)))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (Erasure.Exposure.exposedRegion
            (atomExposureDescription shape application)
            (atomSupportCanonical atomArguments))))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (Erasure.Exposure.exposedRegion
          (atomExposureDescription shape application)
          (atomSupportCanonical atomArguments)))
      targetCanonical targetExternalTwoEnded := by
  let raw := atomExposureDescriptionWithHost shape hostLocals hostItems
    application
  let pinned := atomPinnedExposureDescriptionWithHost shape hostLocals
    hostItems application
  let targetRegion := Region.adjoinAt hostLocals hostItems
    (Erasure.Exposure.exposedRegion
      (atomExposureDescription shape application)
      (atomSupportCanonical atomArguments))
  let targetOccurrence : Occurrence targetRegion
      (occurrence.interface.withBody
        (occurrence.context.fill targetRegion) targetCanonical
          targetExternalTwoEnded) :=
    exactOccurrence occurrence.interface occurrence.context targetRegion
      targetCanonical targetExternalTwoEnded
  let material :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern raw.material
        (atomSupportCanonical atomArguments))
      (Erasure.Exposure.applicationPorts raw)
  let rawTarget : Region outer :=
    .mk (raw.hostLocals ++ material.locals)
      ((raw.hostItems.renameWires
        (Region.adjoinHostWire outer raw.hostLocals material.locals)).append
        (material.items.renameWires
          (Region.adjoinMaterialWire outer raw.hostLocals material.locals)))
  have rawTargetEq : rawTarget = Erasure.Exposure.exposedRegion raw
      (atomSupportCanonical atomArguments) := by
    change rawTarget = Region.adjoinAt raw.hostLocals raw.hostItems material
    dsimp only [rawTarget]
    cases material
    rfl
  let presentation : RegionIso (WireEquiv.refl outer) rawTarget
      targetRegion := by
    let combined := (RegionIso.ofEq rawTargetEq).trans (by
        simpa only [targetRegion, raw] using
          atomExposureDescriptionWithHost_exposedIso shape hostLocals
            hostItems application)
    simpa only [WireEquiv.refl_trans] using combined
  let fullAmbient := (WireEquiv.refl outer).append presentation.localEquiv
  let pinWires := outer ++ raw.hostLocals
  let sourceRename : WireRenaming pinWires (outer ++ rawTarget.locals) :=
    Region.adjoinHostWire outer raw.hostLocals material.locals
  let targetRename := WireRenaming.comp fullAmbient.toRenaming sourceRename
  have pinWiresNonempty : pinWires ≠ [] := by
    simpa only [pinWires, raw, atomExposureDescriptionWithHost,
      atomExposureDescription, List.append_assoc] using
      atomExposureWires_nonempty shape (outer ++ hostLocals)
  obtain ⟨targetPinnedCanonical, targetPinnedExternalTwoEnded, targetPins⟩ :=
    EqualityNormalization.pinAllTwiceRegionOfNonempty targetOccurrence
      targetRename pinWiresNonempty
  let sourcePins := EqualityNormalization.allPins pinWires sourceRename
  let targetPinsItems := EqualityNormalization.allPins pinWires targetRename
  let rawPinned : Region outer :=
    .mk rawTarget.locals
      ((rawTarget.items.append sourcePins).append sourcePins)
  let targetPinned : Region outer :=
    .mk targetRegion.locals
      ((targetRegion.items.append targetPinsItems).append targetPinsItems)
  let extended : RegionIso (WireEquiv.refl outer) rawPinned targetPinned := by
    exact appendPinsTwiceIso presentation.localEquiv presentation.itemSeqIso
      sourceRename targetRename (by
        intro signature wire
        rfl)
  have rawPinnedEq : rawPinned =
      Region.appendAdjoinedHostSuffix raw.hostLocals raw.hostItems
        (EqualityNormalization.contextPins outer raw.hostLocals) material := by
    have compId : ∀ {left right : List Sig}
        (rename : WireRenaming left right),
        WireRenaming.comp rename WireRenaming.id = rename := by
      intro left right rename
      apply WireRenaming.ext
      intro signature wire
      rfl
    dsimp only [rawPinned, rawTarget, sourcePins, sourceRename, pinWires]
    cases materialEq : material with
    | mk materialLocals materialItems =>
      simp only [Region.appendAdjoinedHostSuffix,
        EqualityNormalization.contextPins, Region.locals, Region.items,
        ItemSeq.renameWires_append,
        EqualityNormalization.allPins_renameWires, compId,
        ItemSeq.append_assoc]
  let moved := RegionIso.adjoinAtMoveHostSuffix raw.hostLocals raw.hostItems
    (EqualityNormalization.contextPins outer raw.hostLocals) material
  let rawToPinned : RegionIso (WireEquiv.refl outer) rawPinned
      (Erasure.Exposure.exposedRegion pinned
        (atomSupportCanonical atomArguments)) := by
    exact (RegionIso.ofEq rawPinnedEq).trans (by
      simpa only [pinned, raw, atomPinnedExposureDescriptionWithHost,
        Erasure.Exposure.exposedRegion, material] using moved)
  let pinnedPresentation : RegionIso (WireEquiv.refl outer) targetPinned
      (Erasure.Exposure.exposedRegion pinned
        (atomSupportCanonical atomArguments)) :=
    extended.symm.trans rawToPinned
  obtain ⟨exposedCanonical, exposedExternalTwoEnded, exposedEquates⟩ :=
    atomSiteExposurePinnedWithHost shape hostLocals hostItems application
      occurrence
  let targetPinnedEndpoint := targetOccurrence.interface.withBody
    (targetOccurrence.context.fill targetPinned) targetPinnedCanonical
      targetPinnedExternalTwoEnded
  let exposedEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Erasure.Exposure.exposedRegion pinned
        (atomSupportCanonical atomArguments))) exposedCanonical
      exposedExternalTwoEnded
  let pinnedIso : OpenDiagramIso targetPinnedEndpoint exposedEndpoint :=
    OpenDiagram.withBody_iso targetPinnedCanonical exposedCanonical
      targetPinnedExternalTwoEnded exposedExternalTwoEnded
      (DiagramContext.fillIso occurrence.context pinnedPresentation)
  have exposureStrict := EqualityNormalization.strictEquates_of_equates
    occurrence exposedEquates
  have exposureForward : Relation.TransGen Step source exposedEndpoint := by
    simpa only [pinned, exposedEndpoint] using exposureStrict.1
  have exposureReverse : Relation.TransGen Step exposedEndpoint source := by
    simpa only [pinned, exposedEndpoint] using exposureStrict.2
  have targetPinForward : Relation.TransGen Step
      (occurrence.interface.withBody
        (occurrence.context.fill targetRegion) targetCanonical
          targetExternalTwoEnded) targetPinnedEndpoint := by
    simpa only [targetOccurrence, targetPinned, targetPinsItems,
      targetPinnedEndpoint] using targetPins.1
  have targetPinReverse : Relation.TransGen Step targetPinnedEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill targetRegion) targetCanonical
          targetExternalTwoEnded) := by
    simpa only [targetOccurrence, targetPinned, targetPinsItems,
      targetPinnedEndpoint] using targetPins.2
  have exposureToPinned : Relation.TransGen Step source
      targetPinnedEndpoint :=
    transGen_iso (OpenDiagramIso.refl source) exposureForward pinnedIso.symm
  have pinnedToExposure : Relation.TransGen Step targetPinnedEndpoint
      source :=
    transGen_iso pinnedIso.symm exposureReverse (OpenDiagramIso.refl source)
  exact ⟨exposureToPinned.trans targetPinReverse,
    targetPinForward.trans pinnedToExposure⟩

private theorem atomBodyWire_natural
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (rename : WireRenaming source target) :
    WireRenaming.comp
        (rename.appendRight (EqualityNormalization.locals shape.pattern))
        (atomBodyWire shape source) =
      atomBodyWire shape target := by
  apply WireRenaming.ext
  intro signature wire
  let appendNil : WireRenaming patternWires (patternWires ++ []) :=
    ⟨fun selected => selected.appendLeft []⟩
  exact congrArg (fun map => map (appendNil wire))
    (EqualityNormalization.bodyEmbedding_natural shape.pattern rename)

private theorem atomSiteHostItems_renameWires
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars source patternWires)
    (rename : WireRenaming source target) :
    (atomSiteHostItems shape application).renameWires
        (rename.appendRight (EqualityNormalization.locals shape.pattern)) =
      atomSiteHostItems shape
        (application.map fun wire => rename wire) := by
  have actualMap :
      ((application.map fun wire =>
          EqualityNormalization.actualEmbedding shape.pattern source wire).map
        fun wire =>
          rename.appendRight
            (EqualityNormalization.locals shape.pattern) wire) =
        (application.map fun wire => rename wire).map fun wire =>
          EqualityNormalization.actualEmbedding shape.pattern target wire := by
    calc
      _ = application.map (fun wire =>
          rename.appendRight (EqualityNormalization.locals shape.pattern)
            (EqualityNormalization.actualEmbedding shape.pattern source
              wire)) :=
        Diagram.vars_map_comp application
          (EqualityNormalization.actualEmbedding shape.pattern source)
          (rename.appendRight
            (EqualityNormalization.locals shape.pattern))
      _ = application.map (fun wire =>
          EqualityNormalization.actualEmbedding shape.pattern target
            (rename wire)) := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming source
              (target ++ EqualityNormalization.locals shape.pattern) =>
            application.map fun wire => map wire)
          (EqualityNormalization.actualEmbedding_natural shape.pattern rename)
      _ = _ := (Diagram.vars_map_comp application rename
        (EqualityNormalization.actualEmbedding shape.pattern target)).symm
  have patternMap :
      (shape.pattern.boundaryWire.map fun wire =>
          EqualityNormalization.patternEmbedding shape.pattern source wire).map
        (fun wire => rename.appendRight
          (EqualityNormalization.locals shape.pattern) wire) =
      shape.pattern.boundaryWire.map fun wire =>
        EqualityNormalization.patternEmbedding shape.pattern target wire := by
    calc
      _ = shape.pattern.boundaryWire.map (fun wire =>
          rename.appendRight (EqualityNormalization.locals shape.pattern)
            (EqualityNormalization.patternEmbedding shape.pattern source
              wire)) :=
        Diagram.vars_map_comp shape.pattern.boundaryWire
          (EqualityNormalization.patternEmbedding shape.pattern source)
          (rename.appendRight
            (EqualityNormalization.locals shape.pattern))
      _ = _ := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming shape.pattern.external
              (target ++ EqualityNormalization.locals shape.pattern) =>
            shape.pattern.boundaryWire.map fun wire => map wire)
          (EqualityNormalization.patternEmbedding_natural shape.pattern rename)
  simp only [atomSiteHostItems, ItemSeq.renameWires_append,
    ItemSeq.renameWires_comp,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
  rw [atomBodyWire_natural shape rename, actualMap, patternMap]

private theorem atomSelectedAt_renameWires
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars source patternWires)
    (rename : WireRenaming source target) :
    (Erasure.Exposure.exposedRegion
        (atomExposureDescription shape application)
        (atomSupportCanonical atomArguments)).renameWires rename =
      Erasure.Exposure.exposedRegion
        (atomExposureDescription shape
          (application.map fun wire => rename wire))
        (atomSupportCanonical atomArguments) := by
  simp only [Erasure.Exposure.exposedRegion, atomExposureDescription]
  rw [Region.renameWires_adjoinAt,
    atomSiteHostItems_renameWires]
  congr 1
  rw [EqualityNormalization.instantiate_renameWires]
  congr 1
  change
    (Erasure.Exposure.applicationPorts
      (atomExposureDescription shape application)).map
        (fun wire => rename.appendRight
          (EqualityNormalization.locals shape.pattern) wire) =
      Erasure.Exposure.applicationPorts
        (atomExposureDescription shape
          (application.map fun wire => rename wire))
  rw [atomExposureApplicationPorts, atomExposureApplicationPorts]
  calc
    _ = (atomSelection head ports).map (fun wire =>
        rename.appendRight (EqualityNormalization.locals shape.pattern)
          (atomBodyWire shape source wire)) :=
      Diagram.vars_map_comp (atomSelection head ports)
        (atomBodyWire shape source)
        (rename.appendRight (EqualityNormalization.locals shape.pattern))
    _ = (atomSelection head ports).map (fun wire =>
        atomBodyWire shape target wire) := by
      simpa only [WireRenaming.comp] using congrArg
        (fun map : WireRenaming patternWires
            (target ++ EqualityNormalization.locals shape.pattern) =>
          (atomSelection head ports).map fun wire => map wire)
        (atomBodyWire_natural shape rename)
    _ = _ := rfl

private noncomputable def atomSelectedAtNaturality
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires) :
    ∀ {common middle target : List Sig}
      (application : Vars common patternWires)
      (rename : WireRenaming common middle)
      (post : WireRenaming middle target),
      RegionIso (WireEquiv.refl target)
        ((Erasure.Exposure.exposedRegion
            (atomExposureDescription shape
              (application.map fun wire => rename wire))
            (atomSupportCanonical atomArguments)).renameWires post)
        (Erasure.Exposure.exposedRegion
          (atomExposureDescription shape
            (application.map fun wire => WireRenaming.comp post rename wire))
          (atomSupportCanonical atomArguments)) := by
  intro common middle target application rename post
  apply RegionIso.ofEq
  rw [atomSelectedAt_renameWires]
  apply congrArg (fun mapped => Erasure.Exposure.exposedRegion
    (atomExposureDescription shape mapped)
    (atomSupportCanonical atomArguments))
  simpa only [WireRenaming.comp] using
    Diagram.vars_map_comp application rename post

private noncomputable def atomSelectedLeaf
    {patternWires atomArguments : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires) :
    EqualityNormalization.SelectedLeafCompiler shape.pattern := {
  selectedAt := fun application rename =>
    Erasure.Exposure.exposedRegion
      (atomExposureDescription shape
        (application.map fun wire => rename wire))
      (atomSupportCanonical atomArguments)
  selectedNaturality := atomSelectedAtNaturality shape
  selectedStrict := fun {_common _outer _hostLocals _boundary} application
      rename hostItems {_source} occurrence targetCanonical
      targetExternalTwoEnded => by
    have sourceEq :
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern application).renameWires rename =
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          shape.pattern (application.map fun wire => rename wire) :=
      EqualityNormalization.instantiate_renameWires
        shape.pattern application rename
    let mappedOccurrence : Occurrence
        (Region.adjoinAt _hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            shape.pattern (application.map fun wire => rename wire)))
        _source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := by
        rw [← sourceEq]
        exact occurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro signature wire
        rw [← sourceEq]
        exact occurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq] using occurrence.host_iso
    }
    have strict := atomExposedSelectedWithHostStrict shape _ hostItems
      (application.map fun wire => rename wire) mappedOccurrence
      (by simpa only [mappedOccurrence] using targetCanonical)
      (by
        intro signature wire
        simpa only [mappedOccurrence] using targetExternalTwoEnded wire)
    simpa only [mappedOccurrence] using strict
}
/-! Retained syntax is reindexed through a generated constructor frame.  The
three mutually recursive theorems below are the nonselected branch of the
atom-head fold; their result is the original region syntax, not a second
description of it. -/

private theorem singleton_conjoin_ofItems
    (item : Item wires) (tail : ItemSeq wires) :
    (Region.singleton item).conjoin (Region.ofItems tail) =
      Region.ofItems (.cons item tail) := by
  rw [show Region.singleton item = Region.ofItems (.cons item .nil) by rfl,
    Region.ofItems_conjoin]
  rfl

mutual
  private def retainedRegionPresentation : Region wires → Region wires
    | .mk locals items =>
        Region.adjoinAt locals .nil (retainedItemsPresentation items)

  private def retainedItemsPresentation : ItemSeq wires → Region wires
    | .nil => Region.blank wires
    | .cons item tail =>
        (retainedItemPresentation item).conjoin
          (retainedItemsPresentation tail)

  private def retainedItemPresentation : Item wires → Region wires
    | .atom head ports => Region.singleton (.atom head ports)
    | .identity signature arity ports =>
        Region.singleton (.identity signature arity ports)
    | .cut body =>
        Region.singleton (.cut (retainedRegionPresentation body))
end

mutual
  private theorem retainedRegionResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (region : Region common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult pattern
        frame.sourceKeep frame.selected
        (region.renameWires frame.sourceKeep)
        (retainedRegionPresentation region) := by
    cases region with
    | mk locals items =>
        simp only [Region.renameWires]
        have sourceKeepEq :
            (frame.append locals).sourceKeep =
              frame.sourceKeep.appendRight locals := by
          rfl
        rw [← sourceKeepEq]
        exact
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            (retainedItemsResult pattern (frame.append locals) items)
  termination_by sizeOf region

  private theorem retainedItemsResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (items : ItemSeq common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        frame.sourceKeep frame.selected
        (items.renameWires frame.sourceKeep)
        (retainedItemsPresentation items) := by
    cases items with
    | nil =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
    | cons item tail =>
        exact
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            (retainedItemResult pattern frame item)
            (retainedItemsResult pattern frame tail)
  termination_by sizeOf items

  private theorem retainedItemResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (item : Item common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        frame.sourceKeep frame.selected
        (item.renameWires frame.sourceKeep)
        (retainedItemPresentation item) := by
    cases item with
    | atom head ports =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
          head ports
    | identity signature arity ports =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          signature arity ports
    | cut body =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
          (retainedRegionResult pattern frame body)
  termination_by sizeOf item
end

mutual
  private def retainedRegionSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (region : Region common) :
      RegionSites operation data
        (retainedRegionResult pattern frame region) :=
    match region with
    | .mk locals items =>
        .mk (retainedItemsSites pattern operation (frame.append locals)
          (operation.appendData frame data locals) items)
  termination_by sizeOf region

  private def retainedItemsSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (items : ItemSeq common) :
      ItemsSites operation data
        (retainedItemsResult pattern frame items) :=
    match items with
    | .nil => .nil _
    | .cons item tail =>
        .cons (retainedItemSites pattern operation frame data item)
          (retainedItemsSites pattern operation frame data tail)
  termination_by sizeOf items

  private def retainedItemSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (item : Item common) :
      ItemSites operation data (retainedItemResult pattern frame item) :=
    match item with
    | .atom head ports =>
        ItemSites.atom (pattern := pattern) (frame := frame) head ports
    | .identity signature arity ports =>
        ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports
    | .cut body =>
        ItemSites.cut (pattern := pattern) (frame := frame)
          (retainedRegionSites pattern operation frame data body)
  termination_by sizeOf item
end

/-! A selected atom site is presented to FormalApplication as one generated
positional-binder application after an arbitrary retained host prefix.  Both
the Instantiation evidence and the matching Transform sites are constructed
from that literal host syntax. -/

private def atomFormalPrefixSource
    (frame : Transform.Frame (atomSupportWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) : ItemSeq sourceWires :=
  (hostItems.renameWires frame.sourceKeep).append
    (.cons (.atom frame.selected
      ((Vars.cons formal retained).map fun wire => frame.sourceKeep wire)) .nil)

private def atomFormalPrefixResult
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) : Region common :=
  match hostItems with
  | .nil =>
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (atomFormalShape atomArguments).pattern (.cons formal retained)).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (atomFormalPrefixResult tail formal retained)

private theorem atomFormalPrefixEvidence
    (frame : Transform.Frame (atomSupportWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
      (atomFormalPrefixSource frame hostItems formal retained)
      (atomFormalPrefixResult hostItems formal retained) := by
  cases hostItems with
  | nil =>
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (.cons formal retained))
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
  | cons item tail =>
      simp only [atomFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, atomFormalPrefixResult]
      change _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        (.cons (item.renameWires frame.sourceKeep)
          (atomFormalPrefixSource frame tail formal retained))
        ((retainedItemPresentation item).conjoin
          (atomFormalPrefixResult tail formal retained))
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (retainedItemResult (atomFormalShape atomArguments).pattern frame item)
        (atomFormalPrefixEvidence frame tail formal retained)
  termination_by sizeOf hostItems

private def atomFormalPrefixSites
    (frame : Transform.Frame (atomSupportWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    ItemsSites (Leaf.Formal.operation [] atomArguments) PUnit.unit
      (atomFormalPrefixEvidence frame hostItems formal retained) :=
  match hostItems with
  | .nil =>
      let siteData :
          (Leaf.Formal.operation [] atomArguments).SiteData frame PUnit.unit
            (.cons formal retained) :=
        ⟨formal, ⟨retained, rfl⟩⟩
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (atomFormalShape atomArguments).pattern frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom (pattern := (atomFormalShape atomArguments).pattern)
          (frame := frame) (.cons formal retained) siteData)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (atomFormalShape atomArguments).pattern
          (Leaf.Formal.operation [] atomArguments) frame PUnit.unit item)
        (atomFormalPrefixSites frame tail formal retained)
  termination_by sizeOf hostItems

mutual
  /-- The retained Formal prefix uses the same region syntax as its source,
  presented through the conjunction layout needed by one shared transform
  root. -/
  private noncomputable def retainedRegionPresentationIso
      (region : Region wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedRegionPresentation region) region :=
    match region with
    | .mk locals items => by
        let child := RegionIso.adjoinAt locals .nil
          (retainedItemsPresentationIso items)
        exact child.trans (RegionIso.adjoinAtOfItems locals items)
  termination_by sizeOf region

  private noncomputable def retainedItemsPresentationIso
      (items : ItemSeq wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedItemsPresentation items) (Region.ofItems items) :=
    match items with
    | .nil => RegionIso.refl _
    | .cons item tail => by
        let children := RegionIso.conjoinCongr
          (retainedItemPresentationIso item)
          (retainedItemsPresentationIso tail)
        let presented := RegionIso.ofEq
          (singleton_conjoin_ofItems item tail)
        exact children.trans presented
  termination_by sizeOf items

  private noncomputable def retainedItemPresentationIso
      (item : Item wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedItemPresentation item) (Region.singleton item) :=
    match item with
    | .atom _ _ => RegionIso.refl _
    | .identity _ _ _ => RegionIso.refl _
    | .cut body =>
        RegionIso.singletonCutCongr (retainedRegionPresentationIso body)
  termination_by sizeOf item
end

/-- The literal result of the selected-leaf Formal evidence presents its
retained host followed by the one positional Formal instantiation. -/
private noncomputable def atomFormalPrefixResultIso
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    RegionIso (WireEquiv.refl common)
      (atomFormalPrefixResult hostItems formal retained)
      ((Region.ofItems hostItems).conjoin
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (atomFormalShape atomArguments).pattern
          (.cons formal retained))) :=
  match hostItems with
  | .nil => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (atomFormalShape atomArguments).pattern (.cons formal retained)
      exact (RegionIso.conjoinBlank inner).trans
        (RegionIso.blankConjoin inner).symm
  | .cons item tail => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (atomFormalShape atomArguments).pattern (.cons formal retained)
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (atomFormalPrefixResultIso tail formal retained)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) inner).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl inner)
      exact children.trans (associated.trans prefixIso)
  termination_by sizeOf hostItems

/-- Close the selected-leaf prefix presentation under the equality locals
owned by exposure. -/
private noncomputable def atomFormalSelectedResultIso
    {patternWires atomArguments common : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (application : Vars common patternWires) :
    let locals := EqualityNormalization.locals shape.pattern
    let formal : Var (common ++ EqualityNormalization.locals shape.pattern)
        (.rel atomArguments) := atomBodyWire shape common head
    let retained : Vars
        (common ++ EqualityNormalization.locals shape.pattern) atomArguments :=
      ports.map fun wire => atomBodyWire shape common wire
    let hostItems : ItemSeq
        (common ++ EqualityNormalization.locals shape.pattern) :=
      atomSiteHostItems (patternWires := patternWires)
        (atomArguments := atomArguments) (head := head) (ports := ports)
        (tail := tail) shape application
    RegionIso (WireEquiv.refl common)
      (Region.adjoinAt locals .nil
        (atomFormalPrefixResult hostItems formal retained))
      (Region.adjoinAt locals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (atomFormalShape atomArguments).pattern
          (.cons formal retained))) := by
  dsimp only
  let hostItems := atomSiteHostItems
    (patternWires := patternWires) (atomArguments := atomArguments)
    (head := head) (ports := ports) (tail := tail) shape application
  let formal : Var (common ++ EqualityNormalization.locals shape.pattern)
      (.rel atomArguments) := atomBodyWire shape common head
  let retained : Vars
      (common ++ EqualityNormalization.locals shape.pattern) atomArguments :=
    ports.map fun wire => atomBodyWire shape common wire
  let inner :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (atomFormalShape atomArguments).pattern (.cons formal retained)
  let prefixIso := RegionIso.adjoinAt
    (EqualityNormalization.locals shape.pattern) .nil
    (atomFormalPrefixResultIso hostItems formal retained)
  let hosted := adjoinAt_hostedMaterial
    (EqualityNormalization.locals shape.pattern) hostItems inner
  exact prefixIso.trans (RegionIso.ofEq hosted.symm)

/-! A factor layout remembers only the substitution originally carried by
each selected Formal site. The authoritative Formal evidence and site tree
fix the recursive shape; the current frame and literal source are indices. -/
mutual
  private def FactorRegionLayout
      {baseContext baseArguments currentArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (current : Vars baseContext currentArguments)
      (factor : VarsFactor base current)
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : Region formalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern formalFrame.sourceKeep formalFrame.selected source result)
      (sites : RegionSites operation data evidence)
      (currentFrame : Transform.Frame currentArguments common sourceWires
        targetWires)
      (currentSource : Region sourceWires) : Prop :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites =>
      ∃ currentItems : ItemSeq (sourceWires ++ locals),
        currentSource = .mk locals currentItems ∧
          FactorItemsLayout base current factor childEvidence childSites
            (currentFrame.append locals) currentItems
  termination_by 3 * sizeOf sites

  private def FactorItemsLayout
      {baseContext baseArguments currentArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (current : Vars baseContext currentArguments)
      (factor : VarsFactor base current)
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : ItemSeq formalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern formalFrame.sourceKeep formalFrame.selected source result)
      (sites : ItemsSites operation data evidence)
      (currentFrame : Transform.Frame currentArguments common sourceWires
        targetWires)
      (currentSource : ItemSeq sourceWires) : Prop :=
    match sites with
    | .nil _ => currentSource = .nil
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites =>
      ∃ currentItem : Item sourceWires,
        ∃ currentTail : ItemSeq sourceWires,
          currentSource = .cons currentItem currentTail ∧
            FactorItemLayout base current factor itemEvidence itemSites
              currentFrame currentItem ∧
            FactorItemsLayout base current factor tailEvidence tailSites
              currentFrame currentTail
  termination_by 3 * sizeOf sites + 2

  private def FactorItemLayout
      {baseContext baseArguments currentArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (current : Vars baseContext currentArguments)
      (factor : VarsFactor base current)
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : Item formalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern formalFrame.sourceKeep formalFrame.selected source result)
      (sites : ItemSites operation data evidence)
      (currentFrame : Transform.Frame currentArguments common sourceWires
        targetWires)
      (currentSource : Item sourceWires) : Prop :=
    match sites with
    | .atom head ports =>
        currentSource = .atom (currentFrame.sourceKeep head)
          (ports.map fun wire => currentFrame.sourceKeep wire)
    | .selectedAtom application _ =>
        ∃ siteRename : WireRenaming baseContext common,
          application = base.map (fun wire => siteRename wire) ∧
            currentSource = .atom currentFrame.selected
              ((current.map fun wire => siteRename wire).map
                fun wire => currentFrame.sourceKeep wire)
    | .identity signature arity ports =>
        currentSource = .identity signature arity
          (fun index => currentFrame.sourceKeep (ports index))
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites =>
      ∃ currentBody : Region sourceWires,
        currentSource = .cut currentBody ∧
          FactorRegionLayout base current factor childEvidence childSites
            currentFrame currentBody
  termination_by 3 * sizeOf sites + 1
end

/-! FormalApplication evidence is transported only along the explicit source
and retained-wire embeddings used to combine accumulator branches.  The
existing Instantiation proof remains the recursion authority; this theorem
merely rebuilds that proof and its matching Formal site annotations at the
renamed indices. -/

mutual
  private theorem formalRegionReindex
      {atomArguments common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
      {frame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame (atomSupportWires atomArguments)
        mappedCommon mappedSourceWires mappedTargetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (atomFormalShape atomArguments).pattern frame.sourceKeep
          frame.selected source result)
      (sites : RegionSites (Leaf.Formal.operation [] atomArguments)
        PUnit.unit evidence)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected) :
      ∃ mappedSource : Region mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
                (atomFormalShape atomArguments).pattern mappedFrame.sourceKeep
                mappedFrame.selected mappedSource mappedResult,
            ∃ mappedSites : RegionSites
                (Leaf.Formal.operation [] atomArguments) PUnit.unit
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
              Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                (result.renameWires commonRename) mappedResult) ∧
              (∀ {baseContext : List Sig}
                  (base : Vars baseContext (atomSupportWires atomArguments)),
                FactorRegionLayout base base (.refl base) evidence sites frame
                    source →
                  FactorRegionLayout base base (.refl base) mappedEvidence
                    mappedSites mappedFrame mappedSource) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have appendedKeep : ∀ {signature}
            (wire : Var (common ++ locals) signature),
            sourceRename.appendRight locals
                ((frame.append locals).sourceKeep wire) =
              (mappedFrame.append locals).sourceKeep
                (commonRename.appendRight locals wire) := by
          intro signature wire
          change sourceRename.appendRight locals
              (frame.sourceKeep.appendRight locals wire) =
            mappedFrame.sourceKeep.appendRight locals
              (commonRename.appendRight locals wire)
          rw [WireRenaming.appendRight_comp_apply,
            WireRenaming.appendRight_comp_apply, keepMaps]
        have appendedSelected :
            sourceRename.appendRight locals
                (frame.append locals).selected =
              (mappedFrame.append locals).selected := by
          simpa only [Transform.Frame.append, WireRenaming.appendRight,
            Var.appendMap_left] using
              congrArg (fun wire => wire.appendLeft locals) selectedCommutes
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq, ⟨mappedChildIso⟩,
            childLayout⟩ :=
          formalItemsReindex childEvidence childSites
            (commonRename.appendRight locals)
            (sourceRename.appendRight locals) appendedKeep appendedSelected
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            mappedChildEvidence
        let mappedSites : RegionSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence :=
          RegionSites.mk (data := PUnit.unit) (by
            simpa only [Leaf.Formal.operation] using mappedChildSites)
        have mappedSourceEq :
            (Region.mk locals items).renameWires sourceRename =
              Region.mk locals mappedChildSource := by
          simpa only [Region.renameWires] using
            congrArg (Region.mk locals) mappedChildSourceEq
        let exposed := RegionIso.renameWiresAdjoinAtNil childResult
          commonRename
        let child := RegionIso.adjoinAt locals .nil mappedChildIso
        exact ⟨Region.mk locals mappedChildSource,
          Region.adjoinAt locals .nil mappedChildResult, mappedEvidence,
          mappedSites, mappedSourceEq, ⟨exposed.trans child⟩, by
            intro baseContext base layout
            unfold FactorRegionLayout at layout ⊢
            obtain ⟨currentItems, currentEq, currentLayout⟩ := layout
            cases currentEq
            exact ⟨mappedChildSource, rfl, childLayout base currentLayout⟩⟩
  termination_by sizeOf source

  private theorem formalItemsReindex
      {atomArguments common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
      {frame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame (atomSupportWires atomArguments)
        mappedCommon mappedSourceWires mappedTargetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (atomFormalShape atomArguments).pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemsSites (Leaf.Formal.operation [] atomArguments)
        PUnit.unit evidence)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected) :
      ∃ mappedSource : ItemSeq mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (atomFormalShape atomArguments).pattern mappedFrame.sourceKeep
                mappedFrame.selected mappedSource mappedResult,
            ∃ mappedSites : ItemsSites
                (Leaf.Formal.operation [] atomArguments) PUnit.unit
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
              Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                (result.renameWires commonRename) mappedResult) ∧
              (∀ {baseContext : List Sig}
                  (base : Vars baseContext (atomSupportWires atomArguments)),
                FactorItemsLayout base base (.refl base) evidence sites frame
                    source →
                  FactorItemsLayout base base (.refl base) mappedEvidence
                    mappedSites mappedFrame mappedSource) :=
    match sites with
    | .nil _ =>
        by
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
        exact ⟨.nil, Region.blank mappedCommon, mappedEvidence,
          .nil mappedEvidence, rfl, ⟨RegionIso.refl _⟩, by
            intro baseContext base layout
            unfold FactorItemsLayout at layout ⊢
            rfl⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult itemEvidence
        tailEvidence itemSites tailSites =>
        by
        obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
            mappedItemSites, mappedItemSourceEq, ⟨mappedItemIso⟩,
            itemLayout⟩ :=
          formalItemReindex itemEvidence itemSites commonRename sourceRename
            keepCommutes selectedCommutes
        obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
            mappedTailSites, mappedTailSourceEq, ⟨mappedTailIso⟩,
            tailLayout⟩ :=
          formalItemsReindex tailEvidence tailSites commonRename sourceRename
            keepCommutes selectedCommutes
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            mappedItemEvidence mappedTailEvidence
        let mappedSites : ItemsSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence := .cons mappedItemSites mappedTailSites
        have mappedSourceEq :
            (ItemSeq.cons item tail).renameWires sourceRename =
              .cons mappedItemSource mappedTailSource := by
          simp only [ItemSeq.renameWires, mappedItemSourceEq,
            mappedTailSourceEq]
        let exposed := RegionIso.renameWiresConjoin itemResult tailResult
          commonRename
        let children := RegionIso.conjoinCongr mappedItemIso mappedTailIso
        exact ⟨.cons mappedItemSource mappedTailSource,
          mappedItemResult.conjoin mappedTailResult, mappedEvidence,
          mappedSites, mappedSourceEq, ⟨exposed.trans children⟩, by
            intro baseContext base layout
            unfold FactorItemsLayout at layout ⊢
            obtain ⟨currentItem, currentTail, currentEq, currentItemLayout,
              currentTailLayout⟩ := layout
            cases currentEq
            exact ⟨mappedItemSource, mappedTailSource, rfl,
              itemLayout base currentItemLayout,
              tailLayout base currentTailLayout⟩⟩
  termination_by sizeOf source

  private theorem formalItemReindex
      {atomArguments common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
      {frame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame (atomSupportWires atomArguments)
        mappedCommon mappedSourceWires mappedTargetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (atomFormalShape atomArguments).pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemSites (Leaf.Formal.operation [] atomArguments)
        PUnit.unit evidence)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected) :
      ∃ mappedSource : Item mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
                (atomFormalShape atomArguments).pattern mappedFrame.sourceKeep
                mappedFrame.selected mappedSource mappedResult,
            ∃ mappedSites : ItemSites
                (Leaf.Formal.operation [] atomArguments) PUnit.unit
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
              Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                (result.renameWires commonRename) mappedResult) ∧
              (∀ {baseContext : List Sig}
                  (base : Vars baseContext (atomSupportWires atomArguments)),
                FactorItemLayout base base (.refl base) evidence sites frame
                    source →
                  FactorItemLayout base base (.refl base) mappedEvidence
                    mappedSites mappedFrame mappedSource) :=
    match sites with
    | .atom head ports =>
        by
        let mappedPorts := ports.map fun wire => commonRename wire
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have mappedPortWires :
            (ports.map fun wire => frame.sourceKeep wire).map
                (fun wire => sourceRename wire) =
              mappedPorts.map fun wire => mappedFrame.sourceKeep wire := by
          calc
            _ = ports.map (fun wire =>
                WireRenaming.comp sourceRename frame.sourceKeep wire) :=
              Diagram.vars_map_comp ports frame.sourceKeep sourceRename
            _ = ports.map (fun wire =>
                WireRenaming.comp mappedFrame.sourceKeep commonRename wire) :=
              congrArg (fun rename : WireRenaming common mappedSourceWires =>
                ports.map fun wire => rename wire) keepMaps
            _ = _ := (Diagram.vars_map_comp ports commonRename
              mappedFrame.sourceKeep).symm
        have mappedSource :
            (Item.atom (frame.sourceKeep head)
              (ports.map fun wire => frame.sourceKeep wire)).renameWires
                sourceRename =
              Item.atom (mappedFrame.sourceKeep (commonRename head))
                (mappedPorts.map fun wire => mappedFrame.sourceKeep wire) := by
          simp only [Item.renameWires]
          rw [keepCommutes head]
          exact congrArg
            (Item.atom (mappedFrame.sourceKeep (commonRename head)))
            mappedPortWires
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
            (commonRename head) mappedPorts
        let mappedSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence := ItemSites.atom (pattern :=
            (atomFormalShape atomArguments).pattern) (frame := mappedFrame)
              (commonRename head) mappedPorts
        have mappedResult :
            (Region.singleton (.atom head ports)).renameWires commonRename =
              Region.singleton (.atom (commonRename head) mappedPorts) := by
          rw [Region.singleton_renameWires]
          rfl
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          ⟨RegionIso.ofEq mappedResult⟩, by
            intro baseContext base layout
            unfold FactorItemLayout at layout ⊢
            rfl⟩
    | .selectedAtom ports siteData =>
        by
        obtain ⟨formal, retained, portsEq⟩ := siteData
        let mappedPorts := ports.map fun wire => commonRename wire
        let mappedFormal := commonRename formal
        let mappedRetained := retained.map fun wire => commonRename wire
        have mappedPortsEq : mappedPorts =
            Argument.Projection.Vars.insertAt [] mappedFormal
              mappedRetained := by
          dsimp only [mappedPorts, mappedFormal, mappedRetained]
          rw [portsEq]
          exact Argument.Projection.Vars.insertAt_map [] formal retained
            commonRename
        let mappedData :
            (Leaf.Formal.operation [] atomArguments).SiteData mappedFrame
              PUnit.unit mappedPorts :=
          ⟨mappedFormal, ⟨mappedRetained, mappedPortsEq⟩⟩
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected) mappedPorts
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have mappedPortWires :
            (ports.map fun wire => frame.sourceKeep wire).map
                (fun wire => sourceRename wire) =
              mappedPorts.map fun wire => mappedFrame.sourceKeep wire := by
          calc
            _ = ports.map (fun wire =>
                WireRenaming.comp sourceRename frame.sourceKeep wire) :=
              Diagram.vars_map_comp ports frame.sourceKeep sourceRename
            _ = ports.map (fun wire =>
                WireRenaming.comp mappedFrame.sourceKeep commonRename wire) :=
              congrArg (fun rename : WireRenaming common mappedSourceWires =>
                ports.map fun wire => rename wire) keepMaps
            _ = _ := (Diagram.vars_map_comp ports commonRename
              mappedFrame.sourceKeep).symm
        have mappedSource :
            (Item.atom frame.selected
              (ports.map fun wire => frame.sourceKeep wire)).renameWires
                sourceRename =
              Item.atom mappedFrame.selected
                (mappedPorts.map fun wire => mappedFrame.sourceKeep wire) := by
          simp only [Item.renameWires, selectedCommutes]
          exact congrArg (Item.atom mappedFrame.selected) mappedPortWires
        let mappedSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence := ItemSites.selectedAtom
            (pattern := (atomFormalShape atomArguments).pattern)
            (frame := mappedFrame) mappedPorts mappedData
        have mappedResult :
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (atomFormalShape atomArguments).pattern ports).renameWires
                commonRename =
              _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                (atomFormalShape atomArguments).pattern mappedPorts := by
          exact EqualityNormalization.instantiate_renameWires
            (atomFormalShape atomArguments).pattern ports commonRename
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          ⟨RegionIso.ofEq mappedResult⟩, by
            intro baseContext base layout
            unfold FactorItemLayout at layout ⊢
            obtain ⟨siteRename, portsFromBase, sourceFromBase⟩ := layout
            let mappedSiteRename : WireRenaming baseContext mappedCommon :=
              WireRenaming.comp commonRename siteRename
            refine ⟨mappedSiteRename, ?_, ?_⟩
            · calc
                mappedPorts = ports.map (fun wire => commonRename wire) := rfl
                _ = (base.map fun wire => siteRename wire).map
                      (fun wire => commonRename wire) := by
                  rw [portsFromBase]
                  rfl
                _ = base.map (fun wire => mappedSiteRename wire) :=
                  by
                    simpa only [mappedSiteRename, WireRenaming.comp] using
                      Diagram.vars_map_comp base siteRename commonRename
            · change Item.atom mappedFrame.selected
                  (mappedPorts.map fun wire => mappedFrame.sourceKeep wire) = _
              congr 1
              rw [show base.map (fun wire => mappedSiteRename wire) =
                  mappedPorts by
                calc
                  _ = (base.map fun wire => siteRename wire).map
                      (fun wire => commonRename wire) :=
                    (Diagram.vars_map_comp base siteRename commonRename).symm
                  _ = ports.map (fun wire => commonRename wire) := by
                    rw [← portsFromBase]
                    rfl
                  _ = mappedPorts := rfl]⟩
    | .identity signature arity ports =>
        by
        let mappedPorts := fun position => commonRename (ports position)
        have mappedSource :
            (Item.identity signature arity
              (fun position => frame.sourceKeep (ports position))).renameWires
                sourceRename =
              Item.identity signature arity
                (fun position => mappedFrame.sourceKeep
                  (mappedPorts position)) := by
          simp only [Item.renameWires, mappedPorts]
          apply congrArg (Item.identity signature arity)
          funext position
          exact keepCommutes (ports position)
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected) signature arity mappedPorts
        let mappedSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence := ItemSites.identity
            (pattern := (atomFormalShape atomArguments).pattern)
            (frame := mappedFrame) signature arity mappedPorts
        have mappedResult :
            (Region.singleton (.identity signature arity ports)).renameWires
                commonRename =
              Region.singleton (.identity signature arity mappedPorts) := by
          rw [Region.singleton_renameWires]
          rfl
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          ⟨RegionIso.ofEq mappedResult⟩, by
            intro baseContext base layout
            unfold FactorItemLayout at layout ⊢
            rfl⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence childSites =>
        by
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq, ⟨mappedChildIso⟩,
            childLayout⟩ :=
          formalRegionReindex childEvidence childSites commonRename sourceRename
            keepCommutes selectedCommutes
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            mappedChildEvidence
        let mappedSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence := .cut mappedChildSites
        have mappedSourceEq :
            (Item.cut body).renameWires sourceRename =
              Item.cut mappedChildSource := by
          simpa only [Item.renameWires] using
            congrArg Item.cut mappedChildSourceEq
        let exposed : RegionIso (WireEquiv.refl mappedCommon)
            ((Region.singleton (.cut childResult)).renameWires commonRename)
            (Region.singleton (.cut
              (childResult.renameWires commonRename))) := by
          rw [Region.singleton_renameWires]
          exact RegionIso.refl _
        let child := RegionIso.singletonCutCongr mappedChildIso
        exact ⟨.cut mappedChildSource,
          Region.singleton (.cut mappedChildResult), mappedEvidence,
          mappedSites, mappedSourceEq, ⟨exposed.trans child⟩, by
            intro baseContext base layout
            unfold FactorItemLayout at layout ⊢
            obtain ⟨currentBody, currentEq, currentLayout⟩ := layout
            have bodyEq : currentBody = body := by
              injection currentEq.symm
            subst currentBody
            exact ⟨mappedChildSource, rfl, childLayout base currentLayout⟩⟩
  termination_by sizeOf source
end

/-! Concatenating two generated Formal segments preserves their literal
Instantiation evidence while recording conjunction reassociation only as a
proof presentation. -/
private theorem formalItemsAppend
    {atomArguments common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires}
    {firstSource secondSource : ItemSeq sourceWires}
    {firstResult secondResult : Region common}
    (firstEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        firstSource firstResult)
    (firstSites : ItemsSites (Leaf.Formal.operation [] atomArguments)
      PUnit.unit firstEvidence)
    (secondEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        secondSource secondResult)
    (secondSites : ItemsSites (Leaf.Formal.operation [] atomArguments)
      PUnit.unit secondEvidence) :
    ∃ combinedResult : Region common,
      ∃ combinedEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (atomFormalShape atomArguments).pattern frame.sourceKeep
            frame.selected (firstSource.append secondSource) combinedResult,
        ∃ combinedSites : ItemsSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
            combinedEvidence,
          Nonempty (RegionIso (WireEquiv.refl common)
              (firstResult.conjoin secondResult) combinedResult) ∧
            (∀ {baseContext : List Sig}
                (base : Vars baseContext (atomSupportWires atomArguments)),
              FactorItemsLayout base base (.refl base) firstEvidence firstSites
                  frame firstSource →
                FactorItemsLayout base base (.refl base) secondEvidence
                    secondSites frame secondSource →
                  FactorItemsLayout base base (.refl base) combinedEvidence
                    combinedSites frame
                    (firstSource.append secondSource)) :=
  match firstSites with
  | .nil _ => by
      exact ⟨secondResult, secondEvidence, secondSites,
        ⟨RegionIso.blankConjoin secondResult⟩, by
          intro baseContext base firstLayout secondLayout
          simpa only [ItemSeq.nil_append] using secondLayout⟩
  | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
      itemEvidence tailEvidence itemSites tailSites => by
      obtain ⟨combinedTailResult, combinedTailEvidence,
          combinedTailSites, ⟨combinedTailIso⟩, combineTailLayout⟩ :=
        formalItemsAppend tailEvidence tailSites secondEvidence secondSites
      let combinedEvidence :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          itemEvidence combinedTailEvidence
      let combinedSites : ItemsSites
          (Leaf.Formal.operation [] atomArguments) PUnit.unit
            combinedEvidence := .cons itemSites combinedTailSites
      let associated := RegionIso.conjoinAssoc itemResult tailResult
        secondResult
      let tailPresented := RegionIso.conjoinCongr
        (RegionIso.refl itemResult) combinedTailIso
      exact ⟨itemResult.conjoin combinedTailResult, combinedEvidence,
        combinedSites, ⟨associated.trans tailPresented⟩, by
          intro baseContext base firstLayout secondLayout
          unfold FactorItemsLayout at firstLayout ⊢
          obtain ⟨currentItem, currentTail, currentEq, currentItemLayout,
            currentTailLayout⟩ := firstLayout
          cases currentEq
          exact ⟨item, tail.append secondSource, rfl,
            currentItemLayout,
            combineTailLayout base currentTailLayout secondLayout⟩⟩
  termination_by sizeOf firstSource

/-! An empty retained partition still changes the dependent Formal frame from
`frame` to `frame.append []`.  Transport the literal evidence once, then close
that dependent presentation with the public empty-adjoin unit law. -/
private theorem formalItemsEmptyRetained
    {atomArguments common sourceWires targetWires : List Sig}
    {frame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires}
    {source : ItemSeq sourceWires} {result endpoint : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        source result)
    (sites : ItemsSites (Leaf.Formal.operation [] atomArguments)
      PUnit.unit evidence)
    (presentation : RegionIso (WireEquiv.refl common) endpoint result) :
    ∃ mappedSource : ItemSeq (sourceWires ++ []),
      ∃ mappedResult : Region (common ++ []),
        ∃ mappedEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              (atomFormalShape atomArguments).pattern
              (frame.append []).sourceKeep (frame.append []).selected
              mappedSource mappedResult,
          ∃ mappedSites : ItemsSites
              (Leaf.Formal.operation [] atomArguments) PUnit.unit
              mappedEvidence,
            Nonempty (RegionIso (WireEquiv.refl common) endpoint
              (Region.adjoinAt [] .nil mappedResult)) ∧
            (∀ {baseContext : List Sig}
                (base : Vars baseContext (atomSupportWires atomArguments)),
              FactorItemsLayout base base (.refl base) evidence sites frame
                  source →
                FactorItemsLayout base base (.refl base) mappedEvidence
                  mappedSites (frame.append []) mappedSource) := by
  let commonEquiv := WireEquiv.appendNil common
  let sourceEquiv := WireEquiv.appendNil sourceWires
  let commonAppend := commonEquiv.symm.toRenaming
  let sourceAppend := sourceEquiv.symm.toRenaming
  have keepCommutes : ∀ {signature} (wire : Var common signature),
      sourceAppend (frame.sourceKeep wire) =
        (frame.append []).sourceKeep (commonAppend wire) := by
    intro signature wire
    rw [show sourceAppend (frame.sourceKeep wire) =
        (frame.sourceKeep wire).appendLeft [] by
      exact WireEquiv.appendNil_symm_apply sourceWires
        (frame.sourceKeep wire)]
    rw [show commonAppend wire = wire.appendLeft [] by
      exact WireEquiv.appendNil_symm_apply common wire]
    simp [Transform.Frame.append, WireRenaming.appendRight]
  have selectedCommutes : sourceAppend frame.selected =
      (frame.append []).selected := by
    exact WireEquiv.appendNil_symm_apply sourceWires frame.selected
  obtain ⟨mappedSource, mappedResult, mappedEvidence, mappedSites,
      mappedSourceEq, ⟨mappedResultIso⟩, mapLayout⟩ :=
    formalItemsReindex evidence sites commonAppend sourceAppend
      keepCommutes selectedCommutes
  let resultForward : RegionIso commonEquiv.symm result
      (result.renameWires commonAppend) :=
    by
      simpa only [Region.renameWires_id] using
        RegionIso.renameWires result WireRenaming.id commonAppend
          commonEquiv.symm (fun _ => rfl)
  let endpointForward : RegionIso
      (((WireEquiv.refl common).trans commonEquiv.symm).trans
        (WireEquiv.refl (common ++ []))) endpoint mappedResult :=
    (presentation.trans resultForward).trans mappedResultIso
  let mappedBack : RegionIso commonEquiv mappedResult
      (mappedResult.renameWires commonEquiv.toRenaming) :=
    by
      simpa only [Region.renameWires_id] using
        RegionIso.renameWires mappedResult WireRenaming.id
          commonEquiv.toRenaming commonEquiv (fun _ => rfl)
  let closed : RegionIso
      (((((WireEquiv.refl common).trans commonEquiv.symm).trans
        (WireEquiv.refl (common ++ []))).trans commonEquiv).trans
          (WireEquiv.refl common))
      endpoint (Region.adjoinAt [] .nil mappedResult) :=
    (endpointForward.trans mappedBack).trans
      (RegionIso.adjoinAtNil mappedResult)
  have ambientEq :
      ((((WireEquiv.refl common).trans commonEquiv.symm).trans
        (WireEquiv.refl (common ++ []))).trans commonEquiv).trans
          (WireEquiv.refl common) = WireEquiv.refl common := by
    apply WireEquiv.ext
    intro signature wire
    exact commonEquiv.right_inv wire
  exact ⟨mappedSource, mappedResult, mappedEvidence, mappedSites,
    ⟨closed.castAmbient ambientEq⟩, mapLayout⟩

/-! The Formal accumulator eliminates only into propositions.  Its literal
witnesses are primitive Instantiation evidence derived from the authoritative
site tree; the exact prepared endpoint remains the EvidenceFold result. -/

/-! Factor layouts depend only on the source-facing part of their current
frame.  Primitive edits choose different target wire lists, so this mutual
transport principle prevents that unused choice from leaking into every
constructor proof. -/
mutual
  private theorem factorRegionLayout_sourceFace
      {baseContext baseArguments currentArguments common sourceWires
        firstTargetWires secondTargetWires : List Sig}
      {base : Vars baseContext baseArguments}
      {current : Vars baseContext currentArguments}
      {factor : VarsFactor base current}
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : Region formalSourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern formalFrame.sourceKeep formalFrame.selected source result}
      (sites : RegionSites operation data evidence)
      (first : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (second : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (keepEq : second.sourceKeep = first.sourceKeep)
      (selectedEq : second.selected = first.selected)
      {currentSource : Region sourceWires}
      (layout : FactorRegionLayout base current factor evidence sites first
        currentSource) :
      FactorRegionLayout base current factor evidence sites second
        currentSource :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold FactorRegionLayout at layout ⊢
      obtain ⟨currentItems, rfl, currentItemsLayout⟩ := layout
      refine ⟨currentItems, rfl, ?_⟩
      exact factorItemsLayout_sourceFace childSites (first.append locals)
        (second.append locals) (by
          simp only [Transform.Frame.append]
          exact congrArg (fun keep => keep.appendRight locals) keepEq)
        (by
          simp only [Transform.Frame.append]
          exact congrArg (fun selected => selected.appendLeft locals)
            selectedEq) currentItemsLayout
  termination_by 3 * sizeOf sites

  private theorem factorItemsLayout_sourceFace
      {baseContext baseArguments currentArguments common sourceWires
        firstTargetWires secondTargetWires : List Sig}
      {base : Vars baseContext baseArguments}
      {current : Vars baseContext currentArguments}
      {factor : VarsFactor base current}
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : ItemSeq formalSourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern formalFrame.sourceKeep formalFrame.selected source result}
      (sites : ItemsSites operation data evidence)
      (first : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (second : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (keepEq : second.sourceKeep = first.sourceKeep)
      (selectedEq : second.selected = first.selected)
      {currentSource : ItemSeq sourceWires}
      (layout : FactorItemsLayout base current factor evidence sites first
        currentSource) :
      FactorItemsLayout base current factor evidence sites second
        currentSource :=
    match sites with
    | .nil _ => by simpa only [FactorItemsLayout] using layout
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold FactorItemsLayout at layout ⊢
      obtain ⟨currentItem, currentTail, rfl, itemLayout, tailLayout⟩ := layout
      exact ⟨currentItem, currentTail, rfl,
        factorItemLayout_sourceFace itemSites first second keepEq selectedEq
          itemLayout,
        factorItemsLayout_sourceFace tailSites first second keepEq selectedEq
          tailLayout⟩
  termination_by 3 * sizeOf sites + 2

  private theorem factorItemLayout_sourceFace
      {baseContext baseArguments currentArguments common sourceWires
        firstTargetWires secondTargetWires : List Sig}
      {base : Vars baseContext baseArguments}
      {current : Vars baseContext currentArguments}
      {factor : VarsFactor base current}
      {pattern : OpenDiagram baseArguments}
      {formalSourceWires formalTargetWires : List Sig}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {data : operation.Data formalFrame}
      {source : Item formalSourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern formalFrame.sourceKeep formalFrame.selected source result}
      (sites : ItemSites operation data evidence)
      (first : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (second : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (keepEq : second.sourceKeep = first.sourceKeep)
      (selectedEq : second.selected = first.selected)
      {currentSource : Item sourceWires}
      (layout : FactorItemLayout base current factor evidence sites first
        currentSource) :
      FactorItemLayout base current factor evidence sites second
        currentSource :=
    match sites with
    | .atom _ _ => by
        simpa only [FactorItemLayout, keepEq] using layout
    | .selectedAtom _ _ => by
        simpa only [FactorItemLayout, keepEq, selectedEq] using layout
    | .identity _ _ _ => by
        simpa only [FactorItemLayout, keepEq] using layout
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold FactorItemLayout at layout ⊢
      obtain ⟨currentBody, rfl, bodyLayout⟩ := layout
      exact ⟨currentBody, rfl,
        factorRegionLayout_sourceFace childSites first second keepEq selectedEq
          bodyLayout⟩
  termination_by 3 * sizeOf sites + 1
end

/-! Every authoritative source has the reflexive factor layout over its
identity argument vector.  At a selected site the application itself induces
the unique positional substitution used by the layout. -/
mutual
  private theorem factorRegionLayout_refl
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {operation : Transform.Operation arguments}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) :
      FactorRegionLayout (EqualityNormalization.formalPorts arguments)
        (EqualityNormalization.formalPorts arguments)
        (.refl (EqualityNormalization.formalPorts arguments)) evidence sites
        frame source :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold FactorRegionLayout
      exact ⟨items, rfl, factorItemsLayout_refl childSites⟩
  termination_by structural sites

  private theorem factorItemsLayout_refl
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {operation : Transform.Operation arguments}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) :
      FactorItemsLayout (EqualityNormalization.formalPorts arguments)
        (EqualityNormalization.formalPorts arguments)
        (.refl (EqualityNormalization.formalPorts arguments)) evidence sites
        frame source :=
    match sites with
    | .nil _ => by
      unfold FactorItemsLayout
      rfl
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold FactorItemsLayout
      exact ⟨item, tail, rfl, factorItemLayout_refl itemSites,
        factorItemsLayout_refl tailSites⟩
  termination_by structural sites

  private theorem factorItemLayout_refl
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {operation : Transform.Operation arguments}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) :
      FactorItemLayout (EqualityNormalization.formalPorts arguments)
        (EqualityNormalization.formalPorts arguments)
        (.refl (EqualityNormalization.formalPorts arguments)) evidence sites
        frame source :=
    match sites with
    | .atom _ _ => by
      unfold FactorItemLayout
      rfl
    | .selectedAtom application _ => by
      unfold FactorItemLayout
      let substitution := EqualityNormalization.formalSubstitution application
      have applicationEq :=
        EqualityNormalization.formalPorts_map_substitution application
      refine ⟨substitution, applicationEq.symm, ?_⟩
      rw [applicationEq]
    | .identity _ _ _ => by
      unfold FactorItemLayout
      rfl
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold FactorItemLayout
      exact ⟨body, rfl, factorRegionLayout_refl childSites⟩
  termination_by structural sites
end

/-! Retained syntax contains no selected application.  Consequently its
factor layout is parametric in the selected argument vector: only the fixed
source face of the current frame is observable in these branches. -/
mutual
  private theorem retainedRegionFactorLayout
      {baseContext baseArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (pattern : OpenDiagram baseArguments)
      (operation : Transform.Operation baseArguments)
      (frame : Transform.Frame baseArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (region : Region common) :
      FactorRegionLayout base base (.refl base)
        (retainedRegionResult pattern frame region)
        (retainedRegionSites pattern operation frame data region)
        frame (region.renameWires frame.sourceKeep) := by
    cases region with
    | mk locals items =>
        unfold retainedRegionSites Region.renameWires
        simp_wf
        unfold FactorRegionLayout
        simp_wf
        exact retainedItemsFactorLayout base pattern operation
          (frame.append locals) (operation.appendData frame data locals) items
  termination_by sizeOf region

  private theorem retainedItemsFactorLayout
      {baseContext baseArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (pattern : OpenDiagram baseArguments)
      (operation : Transform.Operation baseArguments)
      (frame : Transform.Frame baseArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (items : ItemSeq common) :
      FactorItemsLayout base base (.refl base)
        (retainedItemsResult pattern frame items)
        (retainedItemsSites pattern operation frame data items)
        frame (items.renameWires frame.sourceKeep) := by
    cases items with
    | nil =>
        unfold retainedItemsSites
        simp_wf
        unfold FactorItemsLayout
        simp_wf
        change ItemSeq.renameWires frame.sourceKeep .nil = .nil
        rfl
    | cons item tail =>
        unfold retainedItemsSites ItemSeq.renameWires
        simp_wf
        unfold FactorItemsLayout
        simp_wf
        refine ⟨item.renameWires frame.sourceKeep,
          tail.renameWires frame.sourceKeep, ⟨rfl, rfl⟩, ?_, ?_⟩
        · exact retainedItemFactorLayout base pattern operation frame data item
        · exact retainedItemsFactorLayout base pattern operation frame data tail
  termination_by sizeOf items

  private theorem retainedItemFactorLayout
      {baseContext baseArguments common sourceWires
        targetWires : List Sig}
      (base : Vars baseContext baseArguments)
      (pattern : OpenDiagram baseArguments)
      (operation : Transform.Operation baseArguments)
      (frame : Transform.Frame baseArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (item : Item common) :
      FactorItemLayout base base (.refl base)
        (retainedItemResult pattern frame item)
        (retainedItemSites pattern operation frame data item)
        frame (item.renameWires frame.sourceKeep) := by
    cases item with
    | atom head ports =>
        unfold retainedItemSites Item.renameWires
        simp_wf
        unfold FactorItemLayout
        simp_wf
    | identity signature arity ports =>
        unfold retainedItemSites Item.renameWires
        simp_wf
        unfold FactorItemLayout
        simp_wf
    | cut body =>
        unfold retainedItemSites Item.renameWires
        simp_wf
        unfold FactorItemLayout
        simp_wf
        exact retainedRegionFactorLayout base pattern operation frame data body
  termination_by sizeOf item
end

/-! The generated Formal prefix retains the originating atom selection at
each selected site.  This is the load-bearing link from the authoritative
atom syntax to the later argument-vector factorization. -/
private theorem atomFormalPrefixFactorLayout
    {patternWires atomArguments common sourceWires targetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    (hostItems : ItemSeq
      (common ++ EqualityNormalization.locals shape.pattern))
    (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires) :
    let retainedLocals := EqualityNormalization.locals shape.pattern
    let frame := formalFrame.append retainedLocals
    let formal : Var (common ++ retainedLocals) (.rel atomArguments) :=
      atomBodyWire shape common head
    let retainedPorts : Vars (common ++ retainedLocals) atomArguments :=
      ports.map fun wire => atomBodyWire shape common wire
    FactorItemsLayout (atomSelection head ports) (atomSelection head ports)
      (.refl (atomSelection head ports))
      (atomFormalPrefixEvidence frame hostItems formal retainedPorts)
      (atomFormalPrefixSites frame hostItems formal retainedPorts)
      frame (atomFormalPrefixSource frame hostItems formal retainedPorts) :=
  match hostItems with
  | .nil => by
      dsimp only
      unfold atomFormalPrefixSites
        atomFormalPrefixSource
      simp_wf
      unfold FactorItemsLayout FactorItemLayout
      simp_wf
      let siteRename : WireRenaming patternWires
          (common ++ EqualityNormalization.locals shape.pattern) :=
        atomBodyWire shape common
      let selectedItem : Item
          (sourceWires ++ EqualityNormalization.locals shape.pattern) :=
        .atom
          (formalFrame.append
            (EqualityNormalization.locals shape.pattern)).selected
          (((atomSelection head ports).map fun wire => siteRename wire).map
            fun wire => (formalFrame.append
              (EqualityNormalization.locals shape.pattern)).sourceKeep wire)
      refine ⟨selectedItem, .nil, ?_, ?_, ?_⟩
      · simp only [ItemSeq.renameWires, ItemSeq.append, selectedItem,
          siteRename, atomSelection, Vars.map]
      · exact ⟨siteRename, rfl, rfl⟩
      · unfold FactorItemsLayout
        simp_wf
  | .cons item rest => by
      dsimp only
      unfold atomFormalPrefixSites
        atomFormalPrefixSource
      simp_wf
      unfold FactorItemsLayout
      simp_wf
      refine ⟨item.renameWires
          (formalFrame.append
            (EqualityNormalization.locals shape.pattern)).sourceKeep,
        atomFormalPrefixSource
          (formalFrame.append
            (EqualityNormalization.locals shape.pattern)) rest
          (atomBodyWire shape common head)
          (ports.map fun wire => atomBodyWire shape common wire), ?_, ?_, ?_⟩
      · simp only [ItemSeq.renameWires, ItemSeq.append,
          atomFormalPrefixSource]
      · exact retainedItemFactorLayout (atomSelection head ports)
          (atomFormalShape atomArguments).pattern
          (Leaf.Formal.operation [] atomArguments)
          (formalFrame.append
            (EqualityNormalization.locals shape.pattern)) PUnit.unit item
      · exact atomFormalPrefixFactorLayout shape rest formalFrame
  termination_by sizeOf hostItems

private def factorSourceFrame (outer localBefore localAfter arguments : List Sig) :
    Transform.Frame arguments (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++ .rel arguments :: localAfter))
      (outer ++ (localBefore ++ localAfter)) :=
  Transform.Frame.replace outer localBefore localAfter [] arguments

/-- Initial atom assembly frame before selected sites contribute their
retained local partitions. -/
private def factorInitialFrame (outer arguments : List Sig) :
    Transform.Frame arguments outer (outer ++ [.rel arguments]) outer where
  sourceKeep := ⟨fun wire => wire.appendLeft [.rel arguments]⟩
  targetKeep := WireRenaming.id
  selected := Var.appendRight outer .here

private def factorBinderRegion (outer localBefore localAfter : List Sig)
    {arguments : List Sig}
    (items : ItemSeq
      (outer ++ (localBefore ++ .rel arguments :: localAfter))) :
    Region outer :=
  .mk (localBefore ++ .rel arguments :: localAfter) items

/-! The bridge contains only the exact primitive relation and proof
presentation between consecutive literal binder-home sources.  In
particular, transitive factors expose their intermediate literal source. -/
private inductive FactorItemsBridge
    (outer localBefore localAfter : List Sig) :
    {baseContext sourceArguments targetArguments : List Sig} →
      {sourceVariables : Vars baseContext sourceArguments} →
      {targetVariables : Vars baseContext targetArguments} →
      VarsFactor sourceVariables targetVariables →
      ItemSeq (outer ++
        (localBefore ++ .rel sourceArguments :: localAfter)) →
      ItemSeq (outer ++
        (localBefore ++ .rel targetArguments :: localAfter)) → Prop
  | refl
      (variables : Vars baseContext arguments)
      (items : ItemSeq
        (outer ++ (localBefore ++ .rel arguments :: localAfter))) :
      FactorItemsBridge outer localBefore localAfter (.refl variables) items
        items
  | permute
      (permutation : TypedPermutation sourceArguments targetArguments)
      (variables : Vars baseContext sourceArguments)
      (sourceItems : ItemSeq
        (outer ++ (localBefore ++ .rel sourceArguments :: localAfter)))
      (targetItems : ItemSeq
        (outer ++ (localBefore ++ .rel targetArguments :: localAfter)))
      (primitiveTarget : Region outer)
      (step : ArgumentPermutation.Permutes
        (factorBinderRegion outer localBefore localAfter sourceItems)
        primitiveTarget)
      (presentation : Nonempty (RegionIso (WireEquiv.refl outer)
        primitiveTarget
        (factorBinderRegion outer localBefore localAfter targetItems))) :
      FactorItemsBridge outer localBefore localAfter
        (.permute permutation variables) sourceItems targetItems
  | contract
      (variables : Vars baseContext (before ++ signature :: after))
      (sourceItems : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)))
      (targetItems : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ signature :: after) :: localAfter)))
      (primitiveTarget : Region outer)
      (step : Argument.Duplicate.Duplicates
        (factorBinderRegion outer localBefore localAfter targetItems)
        primitiveTarget)
      (presentation : Nonempty (RegionIso (WireEquiv.refl outer)
        primitiveTarget
        (factorBinderRegion outer localBefore localAfter sourceItems))) :
      FactorItemsBridge outer localBefore localAfter
        (.contract before variables) sourceItems targetItems
  | extend
      (inserted : Var baseContext signature)
      (variables : Vars baseContext (before ++ after))
      (sourceItems : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ after) :: localAfter)))
      (targetItems : ItemSeq (outer ++ (localBefore ++
        .rel (before ++ signature :: after) :: localAfter)))
      (primitiveTarget : Region outer)
      (step : Argument.Projection.Drops
        (factorBinderRegion outer localBefore localAfter targetItems)
        primitiveTarget)
      (presentation : Nonempty (RegionIso (WireEquiv.refl outer)
        primitiveTarget
        (factorBinderRegion outer localBefore localAfter sourceItems))) :
      FactorItemsBridge outer localBefore localAfter
        (.extend before inserted variables) sourceItems targetItems
  | trans
      {baseContext sourceArguments middleArguments targetArguments : List Sig}
      {sourceVariables : Vars baseContext sourceArguments}
      {middleVariables : Vars baseContext middleArguments}
      {targetVariables : Vars baseContext targetArguments}
      (first : VarsFactor sourceVariables middleVariables)
      (second : VarsFactor middleVariables targetVariables)
      (sourceItems : ItemSeq (outer ++ (localBefore ++
        .rel sourceArguments :: localAfter)))
      (middleItems : ItemSeq (outer ++ (localBefore ++
        .rel middleArguments :: localAfter)))
      (targetItems : ItemSeq (outer ++ (localBefore ++
        .rel targetArguments :: localAfter)))
      (firstBridge : FactorItemsBridge outer localBefore localAfter first
        sourceItems middleItems)
      (secondBridge : FactorItemsBridge outer localBefore localAfter second
        middleItems targetItems) :
      FactorItemsBridge outer localBefore localAfter (.trans first second)
        sourceItems targetItems

private structure PermuteFrames
    (sourceArguments targetArguments common sourceWires targetWires
      nextWires : List Sig) where
  current : Transform.Frame sourceArguments common sourceWires targetWires
  next : Transform.Frame targetArguments common targetWires nextWires
  targetHead : Var targetWires (.rel targetArguments)
  keepEq : next.sourceKeep = current.targetKeep
  selectedEq : next.selected = targetHead

private def PermuteFrames.append
    (frames : PermuteFrames sourceArguments targetArguments common sourceWires
      targetWires nextWires)
    (locals : List Sig) :
    PermuteFrames sourceArguments targetArguments (common ++ locals)
      (sourceWires ++ locals) (targetWires ++ locals) (nextWires ++ locals) := {
  current := frames.current.append locals
  next := frames.next.append locals
  targetHead := frames.targetHead.appendLeft locals
  keepEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun keep => keep.appendRight locals) frames.keepEq
  selectedEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun selected => selected.appendLeft locals)
      frames.selectedEq
}

private structure ReverseFrames
    (currentArguments nextArguments common currentSourceWires
      currentTargetWires nextSourceWires nextTargetWires : List Sig) where
  current : Transform.Frame currentArguments common currentSourceWires
    currentTargetWires
  next : Transform.Frame nextArguments common nextSourceWires nextTargetWires
  edit : Transform.Frame nextArguments common nextSourceWires
    currentSourceWires
  targetHead : Var currentSourceWires (.rel currentArguments)
  editSourceKeepEq : edit.sourceKeep = next.sourceKeep
  editSelectedEq : edit.selected = next.selected
  editTargetKeepEq : edit.targetKeep = current.sourceKeep
  targetHeadEq : targetHead = current.selected

private def ReverseFrames.append
    (frames : ReverseFrames currentArguments nextArguments common
      currentSourceWires currentTargetWires nextSourceWires nextTargetWires)
    (locals : List Sig) :
    ReverseFrames currentArguments nextArguments (common ++ locals)
      (currentSourceWires ++ locals) (currentTargetWires ++ locals)
      (nextSourceWires ++ locals) (nextTargetWires ++ locals) := {
  current := frames.current.append locals
  next := frames.next.append locals
  edit := frames.edit.append locals
  targetHead := frames.targetHead.appendLeft locals
  editSourceKeepEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun keep => keep.appendRight locals)
      frames.editSourceKeepEq
  editSelectedEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun selected => selected.appendLeft locals)
      frames.editSelectedEq
  editTargetKeepEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun keep => keep.appendRight locals)
      frames.editTargetKeepEq
  targetHeadEq := by
    simp only [Transform.Frame.append]
    exact congrArg (fun selected => selected.appendLeft locals)
      frames.targetHeadEq
}

mutual
  private theorem permuteFactorRegion
      {baseContext baseArguments sourceArguments targetArguments common
        formalSourceWires formalTargetWires currentSourceWires
        currentTargetWires nextTargetWires : List Sig}
      {baseVariables : Vars baseContext baseArguments}
      {variables : Vars baseContext sourceArguments}
      (prior : VarsFactor baseVariables variables)
      (permutation : TypedPermutation sourceArguments targetArguments)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Region formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : RegionSites operation formalData formalEvidence)
      (frames : PermuteFrames sourceArguments targetArguments common
        currentSourceWires currentTargetWires nextTargetWires)
      {currentSource : Region currentSourceWires}
      (currentLayout : FactorRegionLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Region currentTargetWires,
        FactorRegionLayout baseVariables
            (permutation.value.mapVars variables)
            (.trans prior (.permute permutation variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.RegionEdit
              (ArgumentPermutation.operation sourceArguments targetArguments
                permutation.value)
              frames.current frames.targetHead currentSource,
            Nonempty (RegionIso (WireEquiv.refl currentTargetWires)
              edit.run nextSource) :=
    match formalSites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold FactorRegionLayout at currentLayout ⊢
      obtain ⟨currentItems, rfl, currentItemsLayout⟩ := currentLayout
      obtain ⟨nextItems, nextItemsLayout, childEdit, ⟨childIso⟩⟩ :=
        permuteFactorItems prior permutation childSites (frames.append locals)
          currentItemsLayout
      let nextSource : Region currentTargetWires := .mk locals nextItems
      let edit : Transform.RegionEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead (.mk locals currentItems) :=
        .mk childEdit
      let presentation :=
        (RegionIso.adjoinAt locals .nil childIso).trans
          (RegionIso.adjoinAtOfItems locals nextItems)
      exact ⟨nextSource, ⟨nextItems, rfl, nextItemsLayout⟩, edit,
        ⟨by
          simpa only [edit, nextSource, Transform.RegionEdit.run] using
            presentation⟩⟩
  termination_by structural formalSites

  private theorem permuteFactorItems
      {baseContext baseArguments sourceArguments targetArguments common
        formalSourceWires formalTargetWires currentSourceWires
        currentTargetWires nextTargetWires : List Sig}
      {baseVariables : Vars baseContext baseArguments}
      {variables : Vars baseContext sourceArguments}
      (prior : VarsFactor baseVariables variables)
      (permutation : TypedPermutation sourceArguments targetArguments)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : ItemSeq formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemsSites operation formalData formalEvidence)
      (frames : PermuteFrames sourceArguments targetArguments common
        currentSourceWires currentTargetWires nextTargetWires)
      {currentSource : ItemSeq currentSourceWires}
      (currentLayout : FactorItemsLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : ItemSeq currentTargetWires,
        FactorItemsLayout baseVariables
            (permutation.value.mapVars variables)
            (.trans prior (.permute permutation variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemsEdit
              (ArgumentPermutation.operation sourceArguments targetArguments
                permutation.value)
              frames.current frames.targetHead currentSource,
            Nonempty (RegionIso (WireEquiv.refl currentTargetWires)
              edit.run (Region.ofItems nextSource)) :=
    match formalSites with
    | .nil _ => by
        unfold FactorItemsLayout at currentLayout ⊢
        subst currentSource
        exact ⟨.nil, rfl, .nil, ⟨RegionIso.refl _⟩⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold FactorItemsLayout at currentLayout ⊢
      obtain ⟨currentItem, currentTail, rfl, currentItemLayout,
        currentTailLayout⟩ := currentLayout
      obtain ⟨nextItem, nextItemLayout, itemEdit, ⟨itemIso⟩⟩ :=
        permuteFactorItem prior permutation itemSites frames currentItemLayout
      obtain ⟨nextTail, nextTailLayout, tailEdit, ⟨tailIso⟩⟩ :=
        permuteFactorItems prior permutation tailSites frames currentTailLayout
      let edit : Transform.ItemsEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead (.cons currentItem currentTail) :=
        .cons itemEdit tailEdit
      let presentation := (RegionIso.conjoinCongr itemIso tailIso).trans
        (RegionIso.ofEq (singleton_conjoin_ofItems nextItem nextTail))
      exact ⟨.cons nextItem nextTail,
        ⟨nextItem, nextTail, rfl, nextItemLayout, nextTailLayout⟩,
        edit, ⟨by
          simpa only [edit, Transform.ItemsEdit.run] using presentation⟩⟩
  termination_by structural formalSites

  private theorem permuteFactorItem
      {baseContext baseArguments sourceArguments targetArguments common
        formalSourceWires formalTargetWires currentSourceWires
        currentTargetWires nextTargetWires : List Sig}
      {baseVariables : Vars baseContext baseArguments}
      {variables : Vars baseContext sourceArguments}
      (prior : VarsFactor baseVariables variables)
      (permutation : TypedPermutation sourceArguments targetArguments)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Item formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemSites operation formalData formalEvidence)
      (frames : PermuteFrames sourceArguments targetArguments common
        currentSourceWires currentTargetWires nextTargetWires)
      {currentSource : Item currentSourceWires}
      (currentLayout : FactorItemLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Item currentTargetWires,
        FactorItemLayout baseVariables
            (permutation.value.mapVars variables)
            (.trans prior (.permute permutation variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemEdit
              (ArgumentPermutation.operation sourceArguments targetArguments
                permutation.value)
              frames.current frames.targetHead currentSource,
            Nonempty (RegionIso (WireEquiv.refl currentTargetWires)
              edit.run (Region.singleton nextSource)) :=
    match formalSites with
    | .atom head ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.atom (frames.next.sourceKeep head)
        (ports.map fun wire => frames.next.sourceKeep wire)
      let edit : Transform.ItemEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead
          (.atom (frames.current.sourceKeep head)
            (ports.map fun wire => frames.current.sourceKeep wire)) :=
        .atom head ports
      have runEq : edit.run = Region.singleton nextSource := by
        simp only [edit, nextSource, Transform.ItemEdit.run]
        rw [frames.keepEq]
      exact ⟨nextSource, rfl, edit, ⟨RegionIso.ofEq runEq⟩⟩
    | .selectedAtom application siteData => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨siteRename, applicationEq, currentSourceEq⟩ := currentLayout
      subst currentSource
      let currentPorts := variables.map fun wire => siteRename wire
      let nextPorts := (permutation.value.mapVars variables).map
        fun wire => siteRename wire
      let nextSource := Item.atom frames.next.selected
        (nextPorts.map fun wire => frames.next.sourceKeep wire)
      let edit : Transform.ItemEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead
          (.atom frames.current.selected
            (currentPorts.map fun wire => frames.current.sourceKeep wire)) :=
        .selectedAtom currentPorts PUnit.unit
      have portsEq : permutation.value.mapVars
            (currentPorts.map fun wire => frames.current.targetKeep wire) =
          nextPorts.map fun wire => frames.next.sourceKeep wire := by
        calc
          permutation.value.mapVars
              (currentPorts.map fun wire => frames.current.targetKeep wire) =
              (permutation.value.mapVars currentPorts).map
                (fun wire => frames.current.targetKeep wire) :=
            (permutation.map_natural currentPorts
              frames.current.targetKeep).symm
          _ = nextPorts.map (fun wire => frames.current.targetKeep wire) := by
            exact congrArg
              (fun ports => ports.map
                (fun wire => frames.current.targetKeep wire))
              (permutation.map_natural variables siteRename).symm
          _ = nextPorts.map (fun wire => frames.next.sourceKeep wire) := by
            rw [frames.keepEq]
      have runEq : edit.run = Region.singleton nextSource := by
        simp only [edit, nextSource, ArgumentPermutation.operation,
          Transform.ItemEdit.run]
        rw [frames.selectedEq, portsEq]
      exact ⟨nextSource, ⟨siteRename, applicationEq, rfl⟩, edit,
        ⟨RegionIso.ofEq runEq⟩⟩
    | .identity signature arity ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.identity signature arity
        (fun index => frames.next.sourceKeep (ports index))
      let edit : Transform.ItemEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead
          (.identity signature arity
            (fun index => frames.current.sourceKeep (ports index))) :=
        .identity signature arity ports
      have runEq : edit.run = Region.singleton nextSource := by
        simp only [edit, nextSource, Transform.ItemEdit.run]
        rw [frames.keepEq]
      exact ⟨nextSource, rfl, edit, ⟨RegionIso.ofEq runEq⟩⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨currentBody, rfl, currentBodyLayout⟩ := currentLayout
      obtain ⟨nextBody, nextBodyLayout, bodyEdit, ⟨bodyIso⟩⟩ :=
        permuteFactorRegion prior permutation childSites frames
          currentBodyLayout
      let nextSource := Item.cut nextBody
      let edit : Transform.ItemEdit
          (ArgumentPermutation.operation sourceArguments targetArguments
            permutation.value)
          frames.current frames.targetHead (.cut currentBody) := .cut bodyEdit
      exact ⟨nextSource, ⟨nextBody, rfl, nextBodyLayout⟩, edit, ⟨by
        simpa only [edit, nextSource, Transform.ItemEdit.run] using
          RegionIso.singletonCutCongr bodyIso⟩⟩
  termination_by structural formalSites
end

mutual
  private theorem contractFactorRegion
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (variables : Vars baseContext (before ++ signature :: after))
      (prior : VarsFactor baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables))
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Region formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : RegionSites operation formalData formalEvidence)
      (frames : ReverseFrames
        (before ++ signature :: signature :: after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : Region currentSourceWires}
      (currentLayout : FactorRegionLayout baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables) prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Region nextSourceWires,
        FactorRegionLayout baseVariables variables
            (.trans prior (.contract before variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.RegionEdit
              (Argument.Duplicate.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run currentSource) :=
    match formalSites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold FactorRegionLayout at currentLayout ⊢
      obtain ⟨currentItems, rfl, currentItemsLayout⟩ := currentLayout
      obtain ⟨nextItems, nextItemsLayout, childEdit, ⟨childIso⟩⟩ :=
        contractFactorItems variables prior childSites (frames.append locals)
          currentItemsLayout
      let nextSource : Region nextSourceWires := .mk locals nextItems
      let edit : Transform.RegionEdit
          (Argument.Duplicate.operation before after signature)
          frames.edit frames.targetHead nextSource := .mk childEdit
      let presentation :=
        (RegionIso.adjoinAt locals .nil childIso).trans
          (RegionIso.adjoinAtOfItems locals currentItems)
      exact ⟨nextSource, ⟨nextItems, rfl, nextItemsLayout⟩, edit, ⟨by
        simpa only [edit, nextSource, Transform.RegionEdit.run] using
          presentation⟩⟩
  termination_by structural formalSites

  private theorem contractFactorItems
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (variables : Vars baseContext (before ++ signature :: after))
      (prior : VarsFactor baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables))
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : ItemSeq formalSourceWires}
      {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemsSites operation formalData formalEvidence)
      (frames : ReverseFrames
        (before ++ signature :: signature :: after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : ItemSeq currentSourceWires}
      (currentLayout : FactorItemsLayout baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables) prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : ItemSeq nextSourceWires,
        FactorItemsLayout baseVariables variables
            (.trans prior (.contract before variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemsEdit
              (Argument.Duplicate.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run (Region.ofItems currentSource)) :=
    match formalSites with
    | .nil _ => by
      unfold FactorItemsLayout at currentLayout ⊢
      subst currentSource
      exact ⟨.nil, rfl, .nil, ⟨RegionIso.refl _⟩⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold FactorItemsLayout at currentLayout ⊢
      obtain ⟨currentItem, currentTail, rfl, currentItemLayout,
        currentTailLayout⟩ := currentLayout
      obtain ⟨nextItem, nextItemLayout, itemEdit, ⟨itemIso⟩⟩ :=
        contractFactorItem variables prior itemSites frames currentItemLayout
      obtain ⟨nextTail, nextTailLayout, tailEdit, ⟨tailIso⟩⟩ :=
        contractFactorItems variables prior tailSites frames currentTailLayout
      let edit : Transform.ItemsEdit
          (Argument.Duplicate.operation before after signature)
          frames.edit frames.targetHead (.cons nextItem nextTail) :=
        .cons itemEdit tailEdit
      let presentation := (RegionIso.conjoinCongr itemIso tailIso).trans
        (RegionIso.ofEq (singleton_conjoin_ofItems currentItem currentTail))
      exact ⟨.cons nextItem nextTail,
        ⟨nextItem, nextTail, rfl, nextItemLayout, nextTailLayout⟩,
        edit, ⟨by
          simpa only [edit, Transform.ItemsEdit.run] using presentation⟩⟩
  termination_by structural formalSites

  private theorem contractFactorItem
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (variables : Vars baseContext (before ++ signature :: after))
      (prior : VarsFactor baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables))
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Item formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemSites operation formalData formalEvidence)
      (frames : ReverseFrames
        (before ++ signature :: signature :: after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : Item currentSourceWires}
      (currentLayout : FactorItemLayout baseVariables
        (Argument.Duplicate.Vars.duplicateAt before variables) prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Item nextSourceWires,
        FactorItemLayout baseVariables variables
            (.trans prior (.contract before variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemEdit
              (Argument.Duplicate.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run (Region.singleton currentSource)) :=
    match formalSites with
    | .atom head ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.atom (frames.edit.sourceKeep head)
        (ports.map fun wire => frames.edit.sourceKeep wire)
      let edit : Transform.ItemEdit
          (Argument.Duplicate.operation before after signature)
          frames.edit frames.targetHead nextSource := .atom head ports
      have runEq : edit.run = Region.singleton
          (.atom (frames.current.sourceKeep head)
            (ports.map fun wire => frames.current.sourceKeep wire)) := by
        simp only [edit, nextSource, Transform.ItemEdit.run]
        rw [frames.editTargetKeepEq]
      exact ⟨nextSource, by
        simp only [nextSource, frames.editSourceKeepEq], edit,
          ⟨RegionIso.ofEq runEq⟩⟩
    | .selectedAtom application siteData => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨siteRename, applicationEq, currentSourceEq⟩ := currentLayout
      subst currentSource
      let nextPorts := variables.map fun wire => siteRename wire
      let currentPorts :=
        (Argument.Duplicate.Vars.duplicateAt before variables).map
          fun wire => siteRename wire
      let nextSource := Item.atom frames.edit.selected
        (nextPorts.map fun wire => frames.edit.sourceKeep wire)
      let edit : Transform.ItemEdit
          (Argument.Duplicate.operation before after signature)
          frames.edit frames.targetHead
          nextSource := .selectedAtom nextPorts PUnit.unit
      have portsEq : Argument.Duplicate.Vars.duplicateAt before
            (nextPorts.map fun wire => frames.edit.targetKeep wire) =
          currentPorts.map fun wire => frames.current.sourceKeep wire := by
        calc
          Argument.Duplicate.Vars.duplicateAt before
              (nextPorts.map fun wire => frames.edit.targetKeep wire) =
              (Argument.Duplicate.Vars.duplicateAt before nextPorts).map
                (fun wire => frames.edit.targetKeep wire) :=
            (duplicateAt_map before nextPorts frames.edit.targetKeep).symm
          _ = currentPorts.map
                (fun wire => frames.edit.targetKeep wire) := by
            exact congrArg
              (fun ports => ports.map
                (fun wire => frames.edit.targetKeep wire))
              (duplicateAt_map before variables siteRename).symm
          _ = currentPorts.map
                (fun wire => frames.current.sourceKeep wire) := by
            rw [frames.editTargetKeepEq]
      have runEq : edit.run = Region.singleton
          (.atom frames.current.selected
            (currentPorts.map fun wire => frames.current.sourceKeep wire)) := by
        simp only [edit, nextSource, Argument.Duplicate.operation,
          Transform.ItemEdit.run]
        rw [frames.targetHeadEq, portsEq]
      exact ⟨nextSource, ⟨siteRename, applicationEq, by
        simp only [nextSource, nextPorts, frames.editSourceKeepEq,
          frames.editSelectedEq]⟩, edit,
        ⟨RegionIso.ofEq runEq⟩⟩
    | .identity signature arity ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.identity signature arity
        (fun index => frames.edit.sourceKeep (ports index))
      let edit : Transform.ItemEdit
          (Argument.Duplicate.operation before after _)
          frames.edit frames.targetHead nextSource :=
        .identity signature arity ports
      have runEq : edit.run = Region.singleton
          (.identity signature arity
            (fun index => frames.current.sourceKeep (ports index))) := by
        simp only [edit, Transform.ItemEdit.run]
        rw [frames.editTargetKeepEq]
      exact ⟨nextSource, by
        simp only [nextSource, frames.editSourceKeepEq], edit,
          ⟨RegionIso.ofEq runEq⟩⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨currentBody, rfl, currentBodyLayout⟩ := currentLayout
      obtain ⟨nextBody, nextBodyLayout, bodyEdit, ⟨bodyIso⟩⟩ :=
        contractFactorRegion variables prior childSites frames
          currentBodyLayout
      let nextSource := Item.cut nextBody
      let edit : Transform.ItemEdit
          (Argument.Duplicate.operation before after signature)
          frames.edit frames.targetHead nextSource := .cut bodyEdit
      exact ⟨nextSource, ⟨nextBody, rfl, nextBodyLayout⟩, edit, ⟨by
        simpa only [edit, nextSource, Transform.ItemEdit.run] using
          RegionIso.singletonCutCongr bodyIso⟩⟩
  termination_by structural formalSites
end

mutual
  private theorem extendFactorRegion
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (inserted : Var baseContext signature)
      (variables : Vars baseContext (before ++ after))
      (prior : VarsFactor baseVariables variables)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Region formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : RegionSites operation formalData formalEvidence)
      (frames : ReverseFrames (before ++ after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : Region currentSourceWires}
      (currentLayout : FactorRegionLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Region nextSourceWires,
        FactorRegionLayout baseVariables
            (Argument.Projection.Vars.insertAt before inserted variables)
            (.trans prior (.extend before inserted variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.RegionEdit
              (Argument.Projection.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run currentSource) :=
    match formalSites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
      unfold FactorRegionLayout at currentLayout ⊢
      obtain ⟨currentItems, rfl, currentItemsLayout⟩ := currentLayout
      obtain ⟨nextItems, nextItemsLayout, childEdit, ⟨childIso⟩⟩ :=
        extendFactorItems inserted variables prior childSites
          (frames.append locals) currentItemsLayout
      let nextSource : Region nextSourceWires := .mk locals nextItems
      let edit : Transform.RegionEdit
          (Argument.Projection.operation before after signature)
          frames.edit frames.targetHead nextSource := .mk childEdit
      let presentation :=
        (RegionIso.adjoinAt locals .nil childIso).trans
          (RegionIso.adjoinAtOfItems locals currentItems)
      exact ⟨nextSource, ⟨nextItems, rfl, nextItemsLayout⟩, edit, ⟨by
        simpa only [edit, nextSource, Transform.RegionEdit.run] using
          presentation⟩⟩
  termination_by structural formalSites

  private theorem extendFactorItems
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (inserted : Var baseContext signature)
      (variables : Vars baseContext (before ++ after))
      (prior : VarsFactor baseVariables variables)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : ItemSeq formalSourceWires}
      {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemsSites operation formalData formalEvidence)
      (frames : ReverseFrames (before ++ after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : ItemSeq currentSourceWires}
      (currentLayout : FactorItemsLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : ItemSeq nextSourceWires,
        FactorItemsLayout baseVariables
            (Argument.Projection.Vars.insertAt before inserted variables)
            (.trans prior (.extend before inserted variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemsEdit
              (Argument.Projection.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run (Region.ofItems currentSource)) :=
    match formalSites with
    | .nil _ => by
      unfold FactorItemsLayout at currentLayout ⊢
      subst currentSource
      exact ⟨.nil, rfl, .nil, ⟨RegionIso.refl _⟩⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
      unfold FactorItemsLayout at currentLayout ⊢
      obtain ⟨currentItem, currentTail, rfl, currentItemLayout,
        currentTailLayout⟩ := currentLayout
      obtain ⟨nextItem, nextItemLayout, itemEdit, ⟨itemIso⟩⟩ :=
        extendFactorItem inserted variables prior itemSites frames
          currentItemLayout
      obtain ⟨nextTail, nextTailLayout, tailEdit, ⟨tailIso⟩⟩ :=
        extendFactorItems inserted variables prior tailSites frames
          currentTailLayout
      let edit : Transform.ItemsEdit
          (Argument.Projection.operation before after signature)
          frames.edit frames.targetHead (.cons nextItem nextTail) :=
        .cons itemEdit tailEdit
      let presentation := (RegionIso.conjoinCongr itemIso tailIso).trans
        (RegionIso.ofEq (singleton_conjoin_ofItems currentItem currentTail))
      exact ⟨.cons nextItem nextTail,
        ⟨nextItem, nextTail, rfl, nextItemLayout, nextTailLayout⟩,
        edit, ⟨by
          simpa only [edit, Transform.ItemsEdit.run] using presentation⟩⟩
  termination_by structural formalSites

  private theorem extendFactorItem
      {baseContext baseArguments before after common formalSourceWires
        formalTargetWires currentSourceWires currentTargetWires
        nextSourceWires nextTargetWires : List Sig}
      {signature : Sig}
      {baseVariables : Vars baseContext baseArguments}
      (inserted : Var baseContext signature)
      (variables : Vars baseContext (before ++ after))
      (prior : VarsFactor baseVariables variables)
      {pattern : OpenDiagram baseArguments}
      {formalFrame : Transform.Frame baseArguments common formalSourceWires
        formalTargetWires}
      {operation : Transform.Operation baseArguments}
      {formalData : operation.Data formalFrame}
      {formalSource : Item formalSourceWires} {formalResult : Region common}
      {formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern formalFrame.sourceKeep formalFrame.selected formalSource
          formalResult}
      (formalSites : ItemSites operation formalData formalEvidence)
      (frames : ReverseFrames (before ++ after)
        (before ++ signature :: after) common currentSourceWires
        currentTargetWires nextSourceWires nextTargetWires)
      {currentSource : Item currentSourceWires}
      (currentLayout : FactorItemLayout baseVariables variables prior
        formalEvidence formalSites frames.current currentSource) :
      ∃ nextSource : Item nextSourceWires,
        FactorItemLayout baseVariables
            (Argument.Projection.Vars.insertAt before inserted variables)
            (.trans prior (.extend before inserted variables)) formalEvidence
            formalSites frames.next nextSource ∧
          ∃ edit : Transform.ItemEdit
              (Argument.Projection.operation before after signature)
              frames.edit frames.targetHead nextSource,
            Nonempty (RegionIso (WireEquiv.refl currentSourceWires)
              edit.run (Region.singleton currentSource)) :=
    match formalSites with
    | .atom head ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.atom (frames.edit.sourceKeep head)
        (ports.map fun wire => frames.edit.sourceKeep wire)
      let edit : Transform.ItemEdit
          (Argument.Projection.operation before after signature)
          frames.edit frames.targetHead nextSource := .atom head ports
      have runEq : edit.run = Region.singleton
          (.atom (frames.current.sourceKeep head)
            (ports.map fun wire => frames.current.sourceKeep wire)) := by
        simp only [edit, nextSource, Transform.ItemEdit.run]
        rw [frames.editTargetKeepEq]
      exact ⟨nextSource, by
        simp only [nextSource, frames.editSourceKeepEq], edit,
          ⟨RegionIso.ofEq runEq⟩⟩
    | .selectedAtom application siteData => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨siteRename, applicationEq, currentSourceEq⟩ := currentLayout
      subst currentSource
      let currentPorts := variables.map fun wire => siteRename wire
      let nextPorts :=
        (Argument.Projection.Vars.insertAt before inserted variables).map
          fun wire => siteRename wire
      let nextSource := Item.atom frames.edit.selected
        (nextPorts.map fun wire => frames.edit.sourceKeep wire)
      let edit : Transform.ItemEdit
          (Argument.Projection.operation before after signature)
          frames.edit frames.targetHead nextSource :=
        .selectedAtom nextPorts PUnit.unit
      have portsEq : Argument.Projection.Vars.dropAt before
            (nextPorts.map fun wire => frames.edit.targetKeep wire) =
          currentPorts.map fun wire => frames.current.sourceKeep wire := by
        calc
          Argument.Projection.Vars.dropAt before
              (nextPorts.map fun wire => frames.edit.targetKeep wire) =
              Argument.Projection.Vars.dropAt before
                ((Argument.Projection.Vars.insertAt before
                    (siteRename inserted) currentPorts).map
                  fun wire => frames.edit.targetKeep wire) := by
            rw [show nextPorts = Argument.Projection.Vars.insertAt before
                (siteRename inserted) currentPorts by
              exact Argument.Projection.Vars.insertAt_map before inserted
                variables siteRename]
          _ = (Argument.Projection.Vars.dropAt before
                (Argument.Projection.Vars.insertAt before
                  (siteRename inserted) currentPorts)).map
                (fun wire => frames.edit.targetKeep wire) := by
            exact (dropAt_map before
              (Argument.Projection.Vars.insertAt before
                (siteRename inserted) currentPorts)
              frames.edit.targetKeep).symm
          _ = currentPorts.map
                (fun wire => frames.edit.targetKeep wire) := by
            rw [dropAt_insertAt]
          _ = currentPorts.map
                (fun wire => frames.current.sourceKeep wire) := by
            rw [frames.editTargetKeepEq]
      have runEq : edit.run = Region.singleton
          (.atom frames.current.selected
            (currentPorts.map fun wire => frames.current.sourceKeep wire)) := by
        simp only [edit, nextSource, Argument.Projection.operation,
          Transform.ItemEdit.run]
        rw [frames.targetHeadEq, portsEq]
      exact ⟨nextSource, ⟨siteRename, applicationEq, by
        simp only [nextSource, nextPorts, frames.editSourceKeepEq,
          frames.editSelectedEq]⟩, edit, ⟨RegionIso.ofEq runEq⟩⟩
    | .identity signature arity ports => by
      unfold FactorItemLayout at currentLayout ⊢
      subst currentSource
      let nextSource := Item.identity signature arity
        (fun index => frames.edit.sourceKeep (ports index))
      let edit : Transform.ItemEdit
          (Argument.Projection.operation before after _)
          frames.edit frames.targetHead nextSource :=
        .identity signature arity ports
      have runEq : edit.run = Region.singleton
          (.identity signature arity
            (fun index => frames.current.sourceKeep (ports index))) := by
        simp only [edit, Transform.ItemEdit.run]
        rw [frames.editTargetKeepEq]
      exact ⟨nextSource, by
        simp only [nextSource, frames.editSourceKeepEq], edit,
          ⟨RegionIso.ofEq runEq⟩⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
      unfold FactorItemLayout at currentLayout ⊢
      obtain ⟨currentBody, rfl, currentBodyLayout⟩ := currentLayout
      obtain ⟨nextBody, nextBodyLayout, bodyEdit, ⟨bodyIso⟩⟩ :=
        extendFactorRegion inserted variables prior childSites frames
          currentBodyLayout
      let nextSource := Item.cut nextBody
      let edit : Transform.ItemEdit
          (Argument.Projection.operation before after signature)
          frames.edit frames.targetHead nextSource := .cut bodyEdit
      exact ⟨nextSource, ⟨nextBody, rfl, nextBodyLayout⟩, edit, ⟨by
        simpa only [edit, nextSource, Transform.ItemEdit.run] using
          RegionIso.singletonCutCongr bodyIso⟩⟩
  termination_by structural formalSites
end

/-! Owning source bridge: the factor fold computes the final literal
binder-home source.  Its endpoint is not supplied by a caller and is not the
source of the original Instantiation evidence. -/
private theorem varsFactorSourceBridge
    {outer localBefore localAfter baseContext baseArguments sourceArguments
      targetArguments : List Sig}
    {baseVariables : Vars baseContext baseArguments}
    {sourceVariables : Vars baseContext sourceArguments}
    {targetVariables : Vars baseContext targetArguments}
    (prior : VarsFactor baseVariables sourceVariables)
    (factor : VarsFactor sourceVariables targetVariables)
    {pattern : OpenDiagram baseArguments}
    {formalSource : ItemSeq
      (outer ++ (localBefore ++ .rel baseArguments :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    {operation : Transform.Operation baseArguments}
    {data : operation.Data
      (factorSourceFrame outer localBefore localAfter baseArguments)}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (factorSourceFrame outer localBefore localAfter
          baseArguments).sourceKeep
        (factorSourceFrame outer localBefore localAfter
          baseArguments).selected formalSource result)
    (sites : ItemsSites operation data evidence)
    {source : ItemSeq
      (outer ++ (localBefore ++ .rel sourceArguments :: localAfter))}
    (layout : FactorItemsLayout baseVariables sourceVariables prior evidence
      sites (factorSourceFrame outer localBefore localAfter sourceArguments)
      source) :
    ∃ targetSource : ItemSeq
        (outer ++ (localBefore ++ .rel targetArguments :: localAfter)),
      FactorItemsLayout baseVariables targetVariables (.trans prior factor)
          evidence sites
          (factorSourceFrame outer localBefore localAfter targetArguments)
          targetSource ∧
        FactorItemsBridge outer localBefore localAfter factor source
          targetSource := by
  induction factor generalizing baseArguments pattern formalSource result
      operation data with
  | refl variables =>
      exact ⟨source, by simpa using layout, .refl variables source⟩
  | @permute sourceArguments targetArguments permutation variables =>
      let primitiveFrame := ArgumentPermutation.rootFrame outer localBefore
        localAfter sourceArguments targetArguments
      let nextFrame := factorSourceFrame outer localBefore localAfter
        targetArguments
      let targetHead := ArgumentPermutation.targetHead outer localBefore
        localAfter targetArguments
      have initialLayout : FactorItemsLayout baseVariables variables prior
          evidence sites primitiveFrame source := by
        exact factorItemsLayout_sourceFace sites
          (factorSourceFrame outer localBefore localAfter sourceArguments)
          primitiveFrame rfl rfl layout
      let frames : PermuteFrames _ _ _ _ _ _ := {
        current := primitiveFrame
        next := nextFrame
        targetHead := targetHead
        keepEq := rfl
        selectedEq := rfl
      }
      obtain ⟨targetSource, targetLayout, edit, ⟨editIso⟩⟩ :=
        permuteFactorItems prior permutation sites frames initialLayout
      let description : ArgumentPermutation.Permutes.Description outer := {
        sourceArguments := sourceArguments
        targetArguments := targetArguments
        before := localBefore
        after := localAfter
        permutation := permutation.value
        items := source
        itemsEdit := edit
      }
      let step : ArgumentPermutation.Permutes
          (factorBinderRegion outer localBefore localAfter source)
          description.target := .mk description
      let presentation :=
        (RegionIso.adjoinAt
          (localBefore ++ .rel targetArguments :: localAfter) .nil
          editIso).trans
          (RegionIso.adjoinAtOfItems
            (localBefore ++ .rel targetArguments :: localAfter) targetSource)
      exact ⟨targetSource, targetLayout,
        .permute permutation variables source targetSource description.target
          step ⟨presentation⟩⟩
  | @contract signature after before variables =>
      let currentFrame := factorSourceFrame outer localBefore localAfter
        (before ++ signature :: signature :: after)
      let nextFrame := factorSourceFrame outer localBefore localAfter
        (before ++ signature :: after)
      let editFrame := Argument.Duplicate.rootFrame outer localBefore
        localAfter before after signature
      let targetHead := Argument.Duplicate.targetHead outer localBefore
        localAfter before after signature
      let frames : ReverseFrames _ _ _ _ _ _ _ := {
        current := currentFrame
        next := nextFrame
        edit := editFrame
        targetHead := targetHead
        editSourceKeepEq := rfl
        editSelectedEq := rfl
        editTargetKeepEq := rfl
        targetHeadEq := rfl
      }
      obtain ⟨targetSource, targetLayout, edit, ⟨editIso⟩⟩ :=
        contractFactorItems variables prior sites frames (by
          exact factorItemsLayout_sourceFace sites
            (factorSourceFrame outer localBefore localAfter
              (before ++ signature :: signature :: after))
            currentFrame rfl rfl layout)
      let description : Argument.Duplicate.Duplicates.Description outer := {
        before := before
        after := after
        localBefore := localBefore
        localAfter := localAfter
        signature := signature
        items := targetSource
        itemsEdit := edit
      }
      let step : Argument.Duplicate.Duplicates
          (factorBinderRegion outer localBefore localAfter targetSource)
          description.target := .mk description
      let presentation :=
        (RegionIso.adjoinAt
          (localBefore ++
            .rel (before ++ signature :: signature :: after) :: localAfter) .nil
          editIso).trans
          (RegionIso.adjoinAtOfItems
            (localBefore ++
              .rel (before ++ signature :: signature :: after) :: localAfter)
            source)
      exact ⟨targetSource, targetLayout,
        .contract variables source targetSource description.target step
          ⟨presentation⟩⟩
  | @extend signature after before inserted variables =>
      let currentFrame := factorSourceFrame outer localBefore localAfter
        (before ++ after)
      let nextFrame := factorSourceFrame outer localBefore localAfter
        (before ++ signature :: after)
      let editFrame := Argument.Projection.rootFrame outer localBefore
        localAfter before after signature
      let targetHead := Argument.Projection.targetHead outer localBefore
        localAfter before after
      let frames : ReverseFrames _ _ _ _ _ _ _ := {
        current := currentFrame
        next := nextFrame
        edit := editFrame
        targetHead := targetHead
        editSourceKeepEq := rfl
        editSelectedEq := rfl
        editTargetKeepEq := rfl
        targetHeadEq := rfl
      }
      obtain ⟨targetSource, targetLayout, edit, ⟨editIso⟩⟩ :=
        extendFactorItems inserted variables prior sites frames (by
          exact factorItemsLayout_sourceFace sites
            (factorSourceFrame outer localBefore localAfter (before ++ after))
            currentFrame rfl rfl layout)
      let description : Argument.Projection.Drops.Description outer := {
        before := before
        after := after
        localBefore := localBefore
        localAfter := localAfter
        signature := signature
        items := targetSource
        itemsEdit := edit
      }
      let step : Argument.Projection.Drops
          (factorBinderRegion outer localBefore localAfter targetSource)
          description.target := .mk description
      let presentation :=
        (RegionIso.adjoinAt
          (localBefore ++ .rel (before ++ after) :: localAfter) .nil
          editIso).trans
          (RegionIso.adjoinAtOfItems
            (localBefore ++ .rel (before ++ after) :: localAfter) source)
      exact ⟨targetSource, targetLayout,
        .extend inserted variables source targetSource description.target step
          ⟨presentation⟩⟩
  | trans first second firstIH secondIH =>
      obtain ⟨middleSource, middleLayout, firstBridge⟩ :=
        firstIH prior evidence sites layout
      obtain ⟨targetSource, targetLayout, secondBridge⟩ :=
        secondIH (.trans prior first) evidence sites middleLayout
      exact ⟨targetSource, by simpa only [VarsFactor.trans] using targetLayout,
        .trans first second source middleSource targetSource firstBridge
          secondBridge⟩

private def FormalRegion
    {patternWires atomArguments common sourceWires targetWires
      originalSourceWires originalTargetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : Region originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
        shape.pattern originalFrame.sourceKeep originalFrame.selected
        source result)
    (sites : RegionSites operation data evidence)
    (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires) : Prop :=
  ∃ formalSource : Region sourceWires,
    ∃ formalResult : Region common,
      ∃ formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            (atomFormalShape atomArguments).pattern formalFrame.sourceKeep
            formalFrame.selected formalSource formalResult,
        ∃ formalSites : RegionSites (Leaf.Formal.operation [] atomArguments)
            PUnit.unit formalEvidence,
          Nonempty (RegionIso (WireEquiv.refl common)
            (EqualityNormalization.EvidenceFold.regionAt
              (atomSelectedLeaf shape) evidence sites WireRenaming.id)
            formalResult) ∧
          FactorRegionLayout (atomSelection head ports)
            (atomSelection head ports) (.refl (atomSelection head ports))
            formalEvidence formalSites formalFrame formalSource

private def FormalItems
    {patternWires atomArguments common sourceWires targetWires
      originalSourceWires originalTargetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        shape.pattern originalFrame.sourceKeep originalFrame.selected
        source result)
    (sites : ItemsSites operation data evidence)
    (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              (atomFormalShape atomArguments).pattern
              (formalFrame.append retained).sourceKeep
              (formalFrame.append retained).selected formalSource formalResult,
          ∃ formalSites : ItemsSites (Leaf.Formal.operation [] atomArguments)
              PUnit.unit formalEvidence,
            Nonempty (RegionIso (WireEquiv.refl common)
              (EqualityNormalization.EvidenceFold.itemsAt
                (atomSelectedLeaf shape) evidence sites WireRenaming.id)
              (Region.adjoinAt retained .nil formalResult)) ∧
            FactorItemsLayout (atomSelection head ports)
              (atomSelection head ports) (.refl (atomSelection head ports))
              formalEvidence formalSites (formalFrame.append retained)
              formalSource

private def FormalItem
    {patternWires atomArguments common sourceWires targetWires
      originalSourceWires originalTargetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : Item originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        shape.pattern originalFrame.sourceKeep originalFrame.selected
        source result)
    (sites : ItemSites operation data evidence)
    (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              (atomFormalShape atomArguments).pattern
              (formalFrame.append retained).sourceKeep
              (formalFrame.append retained).selected formalSource formalResult,
          ∃ formalSites : ItemsSites (Leaf.Formal.operation [] atomArguments)
              PUnit.unit formalEvidence,
            Nonempty (RegionIso (WireEquiv.refl common)
              (EqualityNormalization.EvidenceFold.itemAt
                (atomSelectedLeaf shape) evidence sites WireRenaming.id)
              (Region.adjoinAt retained .nil formalResult)) ∧
            FactorItemsLayout (atomSelection head ports)
              (atomSelection head ports) (.refl (atomSelection head ports))
              formalEvidence formalSites (formalFrame.append retained)
              formalSource

/-- Selected atoms are the only item branch that contributes retained locals
at the current region level.  Its literal witness is the generated Formal
prefix, and its endpoint is still the selected EvidenceFold leaf. -/
private theorem formalSelectedItem
    {patternWires atomArguments common sourceWires targetWires
      originalSourceWires originalTargetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    (application : Vars common patternWires)
    (siteData : operation.SiteData originalFrame data application)
    (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires) :
    FormalItem shape
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        application)
      (ItemSites.selectedAtom (pattern := shape.pattern)
        (frame := originalFrame) application siteData) formalFrame := by
  unfold FormalItem
  let retainedLocals := EqualityNormalization.locals shape.pattern
  let frame := formalFrame.append retainedLocals
  let hostItems := atomSiteHostItems shape application
  let formal : Var (common ++ retainedLocals) (.rel atomArguments) :=
    atomBodyWire shape common head
  let retainedPorts : Vars (common ++ retainedLocals) atomArguments :=
    ports.map fun wire => atomBodyWire shape common wire
  let formalSource := atomFormalPrefixSource frame hostItems formal
    retainedPorts
  let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
  let formalEvidence := atomFormalPrefixEvidence frame hostItems formal
    retainedPorts
  let formalSites := atomFormalPrefixSites frame hostItems formal retainedPorts
  let presentation :=
    (atomFormalSelectedResultIso shape application).symm
  have exactPresentation : RegionIso (WireEquiv.refl common)
      (EqualityNormalization.EvidenceFold.itemAt
        (atomSelectedLeaf shape)
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          application)
        (ItemSites.selectedAtom (pattern := shape.pattern)
          (frame := originalFrame) application siteData) WireRenaming.id)
      (Region.adjoinAt retainedLocals .nil formalResult) := by
    let mappedApplication := application.map fun wire => WireRenaming.id wire
    have mappedEq : mappedApplication = application := by
      simpa only [mappedApplication, WireRenaming.id] using
        Diagram.vars_map_id application
    have exposedEq :
        Erasure.Exposure.exposedRegion
            (atomExposureDescription shape mappedApplication)
            (atomSupportCanonical atomArguments) =
          Region.adjoinAt retainedLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (atomFormalShape atomArguments).pattern
              (.cons formal retainedPorts)) := by
      calc
        _ = Erasure.Exposure.exposedRegion
            (atomExposureDescription shape application)
            (atomSupportCanonical atomArguments) := by
              exact congrArg
                (fun mapped => Erasure.Exposure.exposedRegion
                  (atomExposureDescription shape mapped)
                  (atomSupportCanonical atomArguments)) mappedEq
        _ = _ := by
          simp only [Erasure.Exposure.exposedRegion]
          change Region.adjoinAt
            (EqualityNormalization.locals shape.pattern)
            (atomSiteHostItems shape application)
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (Erasure.Exposure.supportPattern
                (Region.singleton (atomSupportItem atomArguments))
                (atomSupportCanonical atomArguments))
              (Erasure.Exposure.applicationPorts
                (atomExposureDescription shape application))) = _
          rw [atomSupportPattern_eq]
          rw [atomExposureApplicationPorts]
          rfl
    let exposedPresentation :=
      (RegionIso.ofEq exposedEq).trans presentation
    simpa only [EqualityNormalization.EvidenceFold.itemAt,
      atomSelectedLeaf, mappedApplication, retainedLocals, hostItems,
      formal, retainedPorts, formalResult] using exposedPresentation
  exact ⟨retainedLocals, formalSource, formalResult, formalEvidence,
    formalSites, ⟨exactPresentation⟩,
    atomFormalPrefixFactorLayout shape hostItems formalFrame⟩

/-! Package one ordinary Formal item as a one-element segment.  The helper is
used only by item branches whose retained partition is empty. -/
private theorem formalSingleItemEmptyRetained
    {baseContext atomArguments common sourceWires targetWires : List Sig}
    (base : Vars baseContext (atomSupportWires atomArguments))
    {frame : Transform.Frame (atomSupportWires atomArguments) common
      sourceWires targetWires}
    {itemSource : Item sourceWires} {itemResult endpoint : Region common}
    (itemEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        itemSource itemResult)
    (itemSites : ItemSites (Leaf.Formal.operation [] atomArguments)
      PUnit.unit itemEvidence)
    (itemLayout : FactorItemLayout base base (.refl base) itemEvidence
      itemSites frame itemSource)
    (presentation : RegionIso (WireEquiv.refl common) endpoint itemResult) :
    ∃ formalSource : ItemSeq (sourceWires ++ []),
      ∃ formalResult : Region (common ++ []),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              (atomFormalShape atomArguments).pattern
              (frame.append []).sourceKeep (frame.append []).selected
              formalSource formalResult,
          ∃ formalSites : ItemsSites
              (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalEvidence,
            Nonempty (RegionIso (WireEquiv.refl common) endpoint
              (Region.adjoinAt [] .nil formalResult)) ∧
            FactorItemsLayout base base (.refl base) formalEvidence
              formalSites (frame.append []) formalSource := by
  let tailEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (atomFormalShape atomArguments).pattern frame.sourceKeep frame.selected
        (.nil : ItemSeq sourceWires) (Region.blank common) := .nil
  let baseEvidence :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
      itemEvidence tailEvidence
  let baseSites : ItemsSites (Leaf.Formal.operation [] atomArguments)
      PUnit.unit baseEvidence := .cons itemSites (.nil tailEvidence)
  let basePresentation := presentation.trans
    (RegionIso.conjoinBlank itemResult).symm
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      ⟨formalIso⟩, mapLayout⟩ :=
    formalItemsEmptyRetained baseEvidence baseSites basePresentation
  have baseLayout : FactorItemsLayout base base (.refl base) baseEvidence
      baseSites frame (.cons itemSource .nil) := by
    unfold FactorItemsLayout
    refine ⟨itemSource, .nil, rfl, itemLayout, ?_⟩
    unfold FactorItemsLayout
    rfl
  exact ⟨formalSource, formalResult, formalEvidence, formalSites,
    ⟨formalIso⟩, mapLayout base baseLayout⟩

mutual
  /-- Every authoritative region site tree has one generated Formal
  presentation under the inherited shared frame. -/
  private theorem formalRegion
      {patternWires atomArguments common sourceWires targetWires
        originalSourceWires originalTargetWires : List Sig}
      {head : Var patternWires (.rel atomArguments)}
      {ports : Vars patternWires atomArguments}
      {tail : ItemSeq patternWires}
      (shape : PatternShape
        (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
      {originalFrame : Transform.Frame patternWires common
        originalSourceWires originalTargetWires}
      {operation : Transform.Operation patternWires}
      {data : operation.Data originalFrame}
      {source : Region originalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          shape.pattern originalFrame.sourceKeep originalFrame.selected
          source result)
      (sites : RegionSites operation data evidence)
      (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires) :
      FormalRegion shape evidence sites formalFrame :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        obtain ⟨retained, childSource, childFormalResult,
            childFormalEvidence, childFormalSites, ⟨childIso⟩,
            childLayout⟩ :=
          formalItems shape childEvidence childSites
            (formalFrame.append locals)
        unfold FormalRegion
        let combinedRetained := locals ++ retained
        let commonRename := Region.adjoinMaterialWire common locals retained
        let sourceRename := Region.adjoinMaterialWire sourceWires locals retained
        let combinedFrame := formalFrame.append combinedRetained
        have keepCommutes : ∀ {signature}
            (wire : Var ((common ++ locals) ++ retained) signature),
            sourceRename
                (((formalFrame.append locals).append retained).sourceKeep wire) =
              combinedFrame.sourceKeep (commonRename wire) := by
          intro signature wire
          apply Var.appendCases (left := common ++ locals) (right := retained)
            (motive := fun wire => sourceRename
                (((formalFrame.append locals).append retained).sourceKeep wire) =
              combinedFrame.sourceKeep (commonRename wire))
          · intro inheritedSignature inherited
            apply Var.appendCases (left := common) (right := locals)
              (motive := fun inherited => sourceRename
                  (((formalFrame.append locals).append retained).sourceKeep
                    (inherited.appendLeft retained)) =
                combinedFrame.sourceKeep
                  (commonRename (inherited.appendLeft retained)))
            · intro commonSignature commonWire
              simp [sourceRename, commonRename, combinedFrame,
                combinedRetained, Transform.Frame.append,
                WireRenaming.appendRight, Region.adjoinMaterialWire]
            · intro localSignature localWire
              simp [sourceRename, commonRename, combinedFrame,
                combinedRetained, Transform.Frame.append,
                WireRenaming.appendRight, Region.adjoinMaterialWire]
          · intro retainedSignature retainedWire
            simp [sourceRename, commonRename, combinedFrame,
              combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
        have selectedCommutes :
            sourceRename
                (((formalFrame.append locals).append retained).selected) =
              combinedFrame.selected := by
          simp [sourceRename, combinedFrame, combinedRetained,
            Transform.Frame.append, Region.adjoinMaterialWire]
        obtain ⟨mappedSource, mappedResult, mappedEvidence,
            mappedSites, mappedSourceEq, ⟨mappedResultIso⟩,
            mapLayout⟩ :=
          formalItemsReindex childFormalEvidence childFormalSites
            commonRename sourceRename keepCommutes selectedCommutes
        let formalSource : Region sourceWires :=
          .mk combinedRetained mappedSource
        let formalResult : Region common :=
          Region.adjoinAt combinedRetained .nil mappedResult
        let formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
              (atomFormalShape atomArguments).pattern formalFrame.sourceKeep
              formalFrame.selected formalSource formalResult := by
          apply _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
          exact mappedEvidence
        let formalSites : RegionSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalEvidence := by
          apply RegionSites.mk
          exact mappedSites
        let lifted := RegionIso.adjoinAt locals .nil childIso
        let flattened :=
          (RegionIso.adjoinAtAssoc locals .nil retained .nil
            childFormalResult).symm
        let mappedUnderHost := RegionIso.adjoinAt combinedRetained .nil
          mappedResultIso
        have presentation : RegionIso (WireEquiv.refl common)
            (EqualityNormalization.EvidenceFold.regionAt
              (atomSelectedLeaf shape) evidence
              (.mk childSites) WireRenaming.id)
            formalResult := by
          unfold EqualityNormalization.EvidenceFold.regionAt
          simp_wf
          have renameEq :
              (WireRenaming.id : WireRenaming common common).appendRight locals =
                (WireRenaming.id : WireRenaming (common ++ locals)
                  (common ++ locals)) := by
            apply WireRenaming.ext
            intro signature wire
            exact WireRenaming.appendRight_id_apply locals wire
          rw [renameEq]
          let chained := (lifted.trans flattened).trans mappedUnderHost
          have ambientEq :
              ((WireEquiv.refl common).trans
                (WireEquiv.refl common).symm).trans
                  (WireEquiv.refl common) = WireEquiv.refl common := by
            apply WireEquiv.ext
            intro signature wire
            rfl
          simpa only [formalResult, combinedRetained, List.append_assoc,
            commonRename, Region.extendHostItems, ItemSeq.renameWires,
            ItemSeq.append_nil, ItemSeq.nil_append] using
              chained.castAmbient ambientEq
        exact ⟨formalSource, formalResult, formalEvidence,
          formalSites, ⟨presentation⟩, by
            unfold FactorRegionLayout
            exact ⟨mappedSource, rfl,
              mapLayout (atomSelection head ports) childLayout⟩⟩
  termination_by 3 * sizeOf sites

  /-- Item-sequence accumulation synthesizes and concatenates exactly the
  retained partitions contributed by its selected leaves. -/
  private theorem formalItems
      {patternWires atomArguments common sourceWires targetWires
        originalSourceWires originalTargetWires : List Sig}
      {head : Var patternWires (.rel atomArguments)}
      {ports : Vars patternWires atomArguments}
      {tail : ItemSeq patternWires}
      (shape : PatternShape
        (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
      {originalFrame : Transform.Frame patternWires common
        originalSourceWires originalTargetWires}
      {operation : Transform.Operation patternWires}
      {data : operation.Data originalFrame}
      {source : ItemSeq originalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          shape.pattern originalFrame.sourceKeep originalFrame.selected
          source result)
      (sites : ItemsSites operation data evidence)
      (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires) :
      FormalItems shape evidence sites formalFrame :=
    match sites with
    | .nil nilEvidence => by
        unfold FormalItems
        let formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              (atomFormalShape atomArguments).pattern formalFrame.sourceKeep
              formalFrame.selected (.nil : ItemSeq sourceWires)
              (Region.blank common) := .nil
        let formalSites : ItemsSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalEvidence := .nil formalEvidence
        obtain ⟨formalSource, formalResult, mappedEvidence,
            mappedSites, ⟨presentation⟩, mapLayout⟩ :=
          formalItemsEmptyRetained formalEvidence formalSites
            (RegionIso.refl (Region.blank common))
        exact ⟨[], formalSource, formalResult, mappedEvidence,
          mappedSites, ⟨by
            simpa only [EqualityNormalization.EvidenceFold.itemsAt] using
              presentation⟩, mapLayout (atomSelection head ports) (by
                unfold FactorItemsLayout
                rfl)⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item originalTail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        obtain ⟨itemRetained, itemSource, itemFormalResult,
            itemFormalEvidence, itemFormalSites, ⟨itemIso⟩,
            itemLayout⟩ :=
          formalItem shape itemEvidence itemSites formalFrame
        obtain ⟨tailRetained, tailSource, tailFormalResult,
            tailFormalEvidence, tailFormalSites, ⟨tailIso⟩,
            tailLayout⟩ :=
          formalItems shape tailEvidence tailSites formalFrame
        unfold FormalItems
        let combinedFrame := formalFrame.append
          (itemRetained ++ tailRetained)
        let itemCommonRename := Region.conjoinLeftWire common itemRetained
          tailRetained
        let tailCommonRename := Region.conjoinRightWire common itemRetained
          tailRetained
        let itemSourceRename := Region.conjoinLeftWire sourceWires itemRetained
          tailRetained
        let tailSourceRename := Region.conjoinRightWire sourceWires itemRetained
          tailRetained
        have itemKeepCommutes : ∀ {signature}
            (wire : Var (common ++ itemRetained) signature),
            itemSourceRename
                ((formalFrame.append itemRetained).sourceKeep wire) =
              combinedFrame.sourceKeep (itemCommonRename wire) := by
          intro signature wire
          apply Var.appendCases (left := common) (right := itemRetained)
            (motive := fun wire => itemSourceRename
                ((formalFrame.append itemRetained).sourceKeep wire) =
              combinedFrame.sourceKeep (itemCommonRename wire))
          · intro inheritedSignature inherited
            simp [combinedFrame, itemSourceRename, itemCommonRename,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.conjoinLeftWire]
          · intro localSignature localWire
            simp [combinedFrame, itemSourceRename, itemCommonRename,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.conjoinLeftWire]
        have itemSelectedCommutes :
            itemSourceRename (formalFrame.append itemRetained).selected =
              combinedFrame.selected := by
          simp [combinedFrame, itemSourceRename, Transform.Frame.append,
            Region.conjoinLeftWire]
        have tailKeepCommutes : ∀ {signature}
            (wire : Var (common ++ tailRetained) signature),
            tailSourceRename
                ((formalFrame.append tailRetained).sourceKeep wire) =
              combinedFrame.sourceKeep (tailCommonRename wire) := by
          intro signature wire
          apply Var.appendCases (left := common) (right := tailRetained)
            (motive := fun wire => tailSourceRename
                ((formalFrame.append tailRetained).sourceKeep wire) =
              combinedFrame.sourceKeep (tailCommonRename wire))
          · intro inheritedSignature inherited
            simp [combinedFrame, tailSourceRename, tailCommonRename,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.conjoinRightWire]
          · intro localSignature localWire
            simp [combinedFrame, tailSourceRename, tailCommonRename,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.conjoinRightWire]
        have tailSelectedCommutes :
            tailSourceRename (formalFrame.append tailRetained).selected =
              combinedFrame.selected := by
          simp [combinedFrame, tailSourceRename, Transform.Frame.append,
            Region.conjoinRightWire]
        obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
            mappedItemSites, mappedItemSourceEq,
            ⟨mappedItemIso⟩, mapItemLayout⟩ :=
          formalItemsReindex itemFormalEvidence itemFormalSites
            itemCommonRename itemSourceRename itemKeepCommutes
            itemSelectedCommutes
        obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
            mappedTailSites, mappedTailSourceEq,
            ⟨mappedTailIso⟩, mapTailLayout⟩ :=
          formalItemsReindex tailFormalEvidence tailFormalSites
            tailCommonRename tailSourceRename tailKeepCommutes
            tailSelectedCommutes
        obtain ⟨combinedResult, combinedEvidence, combinedSites,
            ⟨combinedIso⟩, combineLayout⟩ :=
          formalItemsAppend mappedItemEvidence mappedItemSites
            mappedTailEvidence mappedTailSites
        let endpointMerged := RegionIso.conjoinCongr itemIso tailIso |>.trans
          (RegionIso.conjoinAdjoinAt itemRetained tailRetained
            itemFormalResult tailFormalResult)
        let mappedChildren := RegionIso.conjoinCongr mappedItemIso mappedTailIso
        let mappedUnderHost := RegionIso.adjoinAt
          (itemRetained ++ tailRetained) .nil mappedChildren
        let combinedUnderHost := RegionIso.adjoinAt
          (itemRetained ++ tailRetained) .nil combinedIso
        have presentation : RegionIso (WireEquiv.refl common)
            (EqualityNormalization.EvidenceFold.itemsAt
              (atomSelectedLeaf shape) evidence (.cons itemSites tailSites)
              WireRenaming.id)
            (Region.adjoinAt (itemRetained ++ tailRetained) .nil
              combinedResult) := by
          simpa only [EqualityNormalization.EvidenceFold.itemsAt,
            Region.renameWires_id] using
              ((endpointMerged.trans mappedUnderHost).trans
                combinedUnderHost)
        exact ⟨itemRetained ++ tailRetained,
          mappedItemSource.append mappedTailSource, combinedResult,
          combinedEvidence, combinedSites, ⟨presentation⟩, by
            exact combineLayout (atomSelection head ports)
              (mapItemLayout (atomSelection head ports) itemLayout)
              (mapTailLayout (atomSelection head ports) tailLayout)⟩
  termination_by 3 * sizeOf sites + 2

  /-- Each individual item becomes a literal Formal segment; only a selected
  atom contributes a nonempty retained partition. -/
  private theorem formalItem
      {patternWires atomArguments common sourceWires targetWires
        originalSourceWires originalTargetWires : List Sig}
      {head : Var patternWires (.rel atomArguments)}
      {ports : Vars patternWires atomArguments}
      {tail : ItemSeq patternWires}
      (shape : PatternShape
        (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
      {originalFrame : Transform.Frame patternWires common
        originalSourceWires originalTargetWires}
      {operation : Transform.Operation patternWires}
      {data : operation.Data originalFrame}
      {source : Item originalSourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          shape.pattern originalFrame.sourceKeep originalFrame.selected
          source result)
      (sites : ItemSites operation data evidence)
      (formalFrame : Transform.Frame (atomSupportWires atomArguments) common
        sourceWires targetWires) :
      FormalItem shape evidence sites formalFrame :=
    match sites with
    | .atom atomHead atomPorts => by
        unfold FormalItem
        refine ⟨[], ?_⟩
        let formalItemEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := formalFrame.sourceKeep)
            (selected := formalFrame.selected) atomHead atomPorts
        let formalItemSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalItemEvidence := ItemSites.atom
            (pattern := (atomFormalShape atomArguments).pattern)
            (frame := formalFrame) atomHead atomPorts
        simpa only [EqualityNormalization.EvidenceFold.itemAt,
          WireRenaming.id, Diagram.vars_map_id] using
            formalSingleItemEmptyRetained (atomSelection head ports)
              formalItemEvidence formalItemSites (by
                unfold FactorItemLayout
                rfl)
              (RegionIso.refl (Region.singleton (.atom atomHead atomPorts)))
    | .selectedAtom application siteData => by
        have selected :=
          formalSelectedItem shape application siteData formalFrame
        unfold FormalItem at selected ⊢
        simpa only [EqualityNormalization.EvidenceFold.itemAt] using selected
    | .identity signature arity identityPorts => by
        unfold FormalItem
        refine ⟨[], ?_⟩
        let formalItemEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := (atomFormalShape atomArguments).pattern)
            (retain := formalFrame.sourceKeep)
            (selected := formalFrame.selected) signature arity identityPorts
        let formalItemSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalItemEvidence := ItemSites.identity
            (pattern := (atomFormalShape atomArguments).pattern)
            (frame := formalFrame) signature arity identityPorts
        simpa only [EqualityNormalization.EvidenceFold.itemAt,
          WireRenaming.id] using
            formalSingleItemEmptyRetained (atomSelection head ports)
              formalItemEvidence formalItemSites (by
                unfold FactorItemLayout
                rfl) (RegionIso.refl
                (Region.singleton (.identity signature arity identityPorts)))
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        unfold FormalItem
        obtain ⟨childSource, childFormalResult, childFormalEvidence,
            childFormalSites, ⟨childIso⟩, childLayout⟩ :=
          formalRegion shape childEvidence childSites formalFrame
        let formalItemEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childFormalEvidence
        let formalItemSites : ItemSites
            (Leaf.Formal.operation [] atomArguments) PUnit.unit
              formalItemEvidence := .cut childFormalSites
        have basePresentation : RegionIso (WireEquiv.refl common)
            (EqualityNormalization.EvidenceFold.itemAt
              (atomSelectedLeaf shape) evidence (.cut childSites)
              WireRenaming.id)
            (Region.singleton (.cut childFormalResult)) := by
          simpa only [EqualityNormalization.EvidenceFold.itemAt] using
            RegionIso.singletonCutCongr childIso
        refine ⟨[], ?_⟩
        simpa only [EqualityNormalization.EvidenceFold.itemAt] using
          formalSingleItemEmptyRetained (atomSelection head ports)
            formalItemEvidence formalItemSites (by
              unfold FactorItemLayout
              exact ⟨childSource, rfl, childLayout⟩) basePresentation
  termination_by 3 * sizeOf sites + 1
end

private theorem atomSelection_factor
    (head : Var patternWires (.rel atomArguments))
    (ports : Vars patternWires atomArguments) :
    VarsFactor (atomSelection head ports)
      (Erasure.Exposure.identityBoundary patternWires) :=
  VarsFactor.factorSelection (atomSelection head ports)

/-! The atom compiler owns the entire originating-site assembly seam: it
first synthesizes a literal Formal presentation from the authoritative site
tree, then folds the induced argument factor to the pattern boundary.  The
factor endpoint is computed by the fold and is never supplied by a caller. -/
private theorem atomHeadFactorBridge
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {head : Var patternWires (.rel atomArguments)}
    {ports : Vars patternWires atomArguments}
    {tail : ItemSeq patternWires}
    (shape : PatternShape
      (Region.ofItems (.cons (.atom head ports) tail)) patternWires)
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        shape.pattern originalFrame.sourceKeep originalFrame.selected
        source result)
    (sites : ItemsSites operation data evidence) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ ([] ++
            .rel (atomSupportWires atomArguments) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          Nonempty (RegionIso (WireEquiv.refl common)
                (EqualityNormalization.EvidenceFold.itemsAt
                  (atomSelectedLeaf shape) evidence sites WireRenaming.id)
                (Region.adjoinAt retained .nil formalResult)) ∧
              ∃ targetSource : ItemSeq
                  (common ++ ([] ++ .rel patternWires :: retained)),
                FactorItemsBridge common [] retained
                  (atomSelection_factor head ports) formalSource targetSource :=
  by
    let initialFrame := factorInitialFrame common
      (atomSupportWires atomArguments)
    obtain ⟨retained, rawSource, rawResult, rawEvidence, rawSites,
        ⟨presentation⟩, rawLayout⟩ :=
      formalItems shape evidence sites initialFrame
    let commonRename : WireRenaming (common ++ retained)
        (common ++ retained) := WireRenaming.id
    let sourceRename := Region.adjoinMaterialWire common
      [.rel (atomSupportWires atomArguments)] retained
    let mappedFrame := factorSourceFrame common [] retained
      (atomSupportWires atomArguments)
    have keepCommutes : ∀ {signature}
        (wire : Var (common ++ retained) signature),
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire) := by
      intro signature wire
      apply Var.appendCases (left := common) (right := retained)
        (motive := fun wire =>
          sourceRename ((initialFrame.append retained).sourceKeep wire) =
            mappedFrame.sourceKeep (commonRename wire))
      · intro inheritedSignature inherited
        apply Var.eq_of_index_eq
        apply Fin.ext
        simp [sourceRename, commonRename, initialFrame, mappedFrame,
          factorInitialFrame, factorSourceFrame, Transform.Frame.append,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          WireRenaming.id, Region.adjoinMaterialWire,
          Var.appendMap_left, Var.index_appendLeft]
      · intro retainedSignature retainedWire
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [show retainedWire =
          Var.appendRight ([] : List Sig) retainedWire by rfl]
        simp [sourceRename, commonRename, initialFrame, mappedFrame,
          factorInitialFrame, factorSourceFrame, Transform.Frame.append,
          Transform.Frame.replace, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          WireRenaming.id, Region.adjoinMaterialWire,
          Var.appendMap_right, Var.index_appendRight]
        rfl
    have selectedCommutes :
        sourceRename (initialFrame.append retained).selected =
          mappedFrame.selected := by
      apply Var.eq_of_index_eq
      apply Fin.ext
      simp [sourceRename, initialFrame, mappedFrame, factorInitialFrame,
        factorSourceFrame, Transform.Frame.append, Transform.Frame.replace,
        Transform.Frame.insertedHead, Region.adjoinMaterialWire,
        Var.appendLeft, Var.appendRight, Var.index,
        Var.index_appendRight]
    obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
        _formalSourceEq, ⟨formalResultIso⟩, mapLayout⟩ :=
      formalItemsReindex rawEvidence rawSites commonRename sourceRename
        keepCommutes selectedCommutes
    have formalLayout : FactorItemsLayout (atomSelection head ports)
        (atomSelection head ports) (.refl (atomSelection head ports))
        formalEvidence formalSites mappedFrame formalSource :=
      mapLayout (atomSelection head ports) rawLayout
    obtain ⟨targetSource, _targetLayout, bridge⟩ :=
      varsFactorSourceBridge (.refl (atomSelection head ports))
        (atomSelection_factor head ports) formalEvidence formalSites
        formalLayout
    have finalPresentation : RegionIso (WireEquiv.refl common)
        (EqualityNormalization.EvidenceFold.itemsAt
          (atomSelectedLeaf shape) evidence sites WireRenaming.id)
        (Region.adjoinAt retained .nil formalResult) := by
      have normalizedResultIso : RegionIso
          (WireEquiv.refl (common ++ retained)) rawResult formalResult := by
        simpa only [commonRename, Region.renameWires_id,
          List.nil_append] using formalResultIso
      exact presentation.trans
        (RegionIso.adjoinAt retained .nil normalizedResultIso)
    exact ⟨retained, formalSource, formalResult,
      ⟨finalPresentation⟩, targetSource, bridge⟩

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
