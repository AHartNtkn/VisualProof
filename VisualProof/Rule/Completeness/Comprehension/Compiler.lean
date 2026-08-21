import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Rule.Completeness.Erasure.Exposure

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Compiler


/-- Compile one complete selected-application layer through formal
application. Boundary and equality compilation prepare the authoritative
instantiation endpoint to the exact all-sites transform endpoint; this theorem
owns the mandatory primitive at the comprehension binder's home occurrence. -/
theorem itemsFormal
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
theorem itemsIdentity
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

private theorem Vars.countIndex_appendLeft_zero
    (variables : Vars source signatures) (added : List Sig)
    (index : Nat) (beyond : source.length ≤ index) :
    (variables.map fun wire => wire.appendLeft added).countIndex index = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      have different : head.index.val ≠ index := by
        have bound := head.index.isLt
        omega
      simp only [Vars.map, Vars.countIndex, Var.index_appendLeft]
      rw [if_neg different, induction]

private theorem Vars.countIndex_appendRight
    (variables : Vars source signatures) (addedBefore : List Sig)
    (index : Nat) :
    (variables.map fun wire => Var.appendRight addedBefore wire).countIndex
        (addedBefore.length + index) =
      variables.countIndex index := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, Var.index_appendRight]
      split <;> rename_i equality
      · have sourceEquality : head.index.val = index := by omega
        simp [sourceEquality, induction]
      · have sourceDifferent : head.index.val ≠ index := by
          intro sourceEquality
          exact equality (by omega)
        simp [sourceDifferent, induction]

private theorem equalityItems_incidencePaths_length
    (left right : Vars wires signatures)
    (wireIndex itemIndex : Nat) :
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      left right).incidencePaths wireIndex itemIndex).length =
      left.countIndex wireIndex + right.countIndex wireIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [
            _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
            ItemSeq.incidencePaths, Item.incidencePaths,
            _root_.VisualProof.Rule.Comprehension.Instantiation.equalityPorts,
            Vars.countIndex, List.length_append, List.length_replicate]
          rw [induction rightTail]
          by_cases leftEqual : leftHead.index.val = wireIndex <;>
            by_cases rightEqual : rightHead.index.val = wireIndex <;>
            simp [List.ofFn_succ, List.ofFn_zero, leftEqual, rightEqual] <;>
            omega

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

/-- Instantiation is canonical for every valid open pattern and every actual
port vector. The bound pattern externals are rooted by the exact equality
block together with the pattern's external-two-ended invariant. -/
private theorem instantiate_canonical
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).Canonical := by
  let embed : WireRenaming pattern.external
      (targetWires ++ pattern.external) :=
    ⟨fun wire => Var.appendRight targetWires wire⟩
  let body := pattern.body.renameWires embed
  let left := ports.map (fun wire => wire.appendLeft pattern.external)
  let right := pattern.boundaryWire.map
    (fun wire => Var.appendRight targetWires wire)
  let equalityItems :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems left right
  have bodyCanonical : body.Canonical :=
    (Region.Canonical.renameWires_iff pattern.body embed).mpr
      pattern.canonical
  have equalityChildren : equalityItems.ChildrenCanonical :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_childrenCanonical
      left right
  have joinedCanonical :
      (body.conjoin (Region.ofItems equalityItems)).Canonical :=
    Region.Canonical.conjoinRightItems body equalityItems bodyCanonical
      equalityChildren
  unfold _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
  rw [_root_.VisualProof.Rule.Comprehension.Instantiation.Equalities_eq_ofItems]
  change (Region.adjoinAt pattern.external .nil
    (body.conjoin (Region.ofItems equalityItems))).Canonical
  apply Region.Canonical.adjoinAt_of_material_roots pattern.external .nil
    (body.conjoin (Region.ofItems equalityItems)) True.intro joinedCanonical
  intro externalIndex
  let external := Var.ofIndex externalIndex
  let embedded := Var.appendRight targetWires external
  have embeddedIndex : embedded.index.val =
      targetWires.length + externalIndex.val := by
    simp [embedded, external]
  cases bodyEq : pattern.body with
  | mk bodyLocals bodyItems =>
      let firstItems :=
        (bodyItems.renameWires (embed.appendRight bodyLocals)).renameWires
        (Region.conjoinLeftWire (targetWires ++ pattern.external)
          bodyLocals [])
      let appendNil : WireRenaming (targetWires ++ pattern.external)
          ((targetWires ++ pattern.external) ++ []) :=
        ⟨fun wire => wire.appendLeft []⟩
      let rightItems := (equalityItems.renameWires appendNil).renameWires
        (Region.conjoinRightWire (targetWires ++ pattern.external)
          bodyLocals [])
      rw [← embeddedIndex]
      simp only [body, bodyEq, Region.renameWires]
      simp only [Region.conjoin, Region.ofItems, Region.incidencePaths]
      change RegionPath.RootedTwo
        ((firstItems.append rightItems).incidencePaths
          embedded.index.val 0)
      rw [ItemSeq.incidencePaths_append]
      simp only [Nat.zero_add]
      have bodyPathsEq :
          (bodyItems.renameWires
            (embed.appendRight bodyLocals)).incidencePaths
              embedded.index.val 0 =
            bodyItems.incidencePaths external.index.val 0 := by
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · have bound := external.index.isLt
          simp only [List.length_append]
          omega
        · have bound := embedded.index.isLt
          simp only [List.length_append]
          omega
        · intro signature wire
          apply Var.appendCases (left := pattern.external)
            (right := bodyLocals)
            (motive := fun wire =>
              ((embed.appendRight bodyLocals) wire).index.val =
                    embedded.index.val ↔
                wire.index.val = external.index.val)
          · intro inheritedSignature inherited
            simp only [WireRenaming.appendRight, Var.appendMap_left,
              Var.index_appendLeft, embed, Var.index_appendRight,
              embedded, external]
            omega
          · intro localSignature localWire
            have externalBound := external.index.isLt
            have localBound := localWire.index.isLt
            simp only [WireRenaming.appendRight, Var.appendMap_right,
              Var.index_appendRight]
            omega
      have firstPathsEq :
          firstItems.incidencePaths embedded.index.val 0 =
            (bodyItems.renameWires
              (embed.appendRight bodyLocals)).incidencePaths
                embedded.index.val 0 := by
        have renamed := ItemSeq.incidencePaths_renameWires_adjoinHost
          (addedLocals := [])
          (bodyItems.renameWires (embed.appendRight bodyLocals))
          (embedded.appendLeft bodyLocals) 0
        simpa [firstItems, Region.adjoinHostWire] using renamed
      obtain ⟨boundaryPosition, boundaryMaps⟩ :=
        pattern.boundarySurjective externalIndex
      have rightGetIndex : (right.get boundaryPosition).index.val =
          embedded.index.val := by
        simp [right, Vars.get_map, embedded, external, boundaryMaps]
      have baseRightMem :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_right_mem_nil
          left right boundaryPosition firstItems.length
      rw [rightGetIndex] at baseRightMem
      have rightPathsEq :
          rightItems.incidencePaths embedded.index.val firstItems.length =
            equalityItems.incidencePaths embedded.index.val
              firstItems.length := by
        simp only [rightItems, ItemSeq.renameWires_comp]
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · exact embedded.index.isLt
        · simpa [body, Region.locals] using
            (embedded.appendLeft bodyLocals).index.isLt
        · intro signature wire
          simp [WireRenaming.comp, appendNil, Region.conjoinRightWire]
      have rightMem : [] ∈
          rightItems.incidencePaths embedded.index.val firstItems.length := by
        rw [rightPathsEq]
        exact baseRightMem
      constructor
      · simp only [List.length_append]
        rw [firstPathsEq, bodyPathsEq, rightPathsEq,
          equalityItems_incidencePaths_length]
        have leftZero : left.countIndex embedded.index.val = 0 := by
          simp only [left, embeddedIndex]
          exact Vars.countIndex_appendLeft_zero ports pattern.external
            (targetWires.length + externalIndex.val) (by omega)
        have rightCount : right.countIndex embedded.index.val =
            pattern.boundaryWire.countIndex external.index.val := by
          simp only [right, embeddedIndex, external]
          simpa [external] using
            Vars.countIndex_appendRight pattern.boundaryWire targetWires
              externalIndex.val
        rw [leftZero, rightCount]
        have twoEnded :
            2 ≤ pattern.boundaryWire.countIndex external.index.val +
              (bodyItems.incidencePaths external.index.val 0).length := by
          have valid := pattern.externalTwoEnded external
          rw [bodyEq] at valid
          simpa only [Region.incidencePaths] using valid
        omega
      · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
        exact List.mem_append_right _ rightMem

/-- Every actual port of an instantiation has an equality incidence. -/
private theorem instantiate_port_incidence_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val ≠ [] := by
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append]
  intro empty
  have equalityEmpty := (List.append_eq_nil_iff.mp empty).2
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
  exact (List.ne_nil_of_mem selected) (by simpa using equalityEmpty)

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
    List.length_append, equalityItems_incidencePaths_length, bodyEmpty,
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
  canonical := instantiate_canonical pattern (formalPorts arguments)
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

@[simp] private theorem formalSubstitution_there
    (head : Var targetWires signature)
    (tail : Vars targetWires arguments)
    (wire : Var arguments wireSignature) :
    formalSubstitution (.cons head tail) (.there wire) =
      formalSubstitution tail wire := rfl

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

private def exposureDescription
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    Rule.Erasure.Description targetWires where
  materialWires := arguments
  hostLocals := []
  hostItems := .nil
  material := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  wireMap := ⟨fun wire => (formalSubstitution ports wire).appendLeft []⟩

private theorem exposureDescription_source
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    (exposureDescription pattern ports).source =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports := by
  simp only [Rule.Erasure.Description.source, exposureDescription]
  rw [spliceAt_nil, instantiate_renameWires,
    formalPorts_map_substitution]

private theorem exposureDescription_applicationPorts
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    Erasure.Exposure.applicationPorts (exposureDescription pattern ports) =
      ports.map (fun wire => wire.appendLeft []) := by
  simp only [Erasure.Exposure.applicationPorts, exposureDescription]
  rw [← formalPorts_eq_exposure]
  calc
    (formalPorts arguments).map (fun wire =>
        (formalSubstitution ports wire).appendLeft []) =
      ((formalPorts arguments).map
        (fun wire => formalSubstitution ports wire)).map
          (fun wire => wire.appendLeft []) := by
            symm
            exact Diagram.vars_map_comp (formalPorts arguments)
              (formalSubstitution ports)
              ⟨fun wire => wire.appendLeft []⟩
    _ = _ := congrArg
      (fun variables => variables.map fun wire => wire.appendLeft [])
      (formalPorts_map_substitution ports)

private theorem exposureDescription_exposedRegion
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (materialCanonical :
      (exposureDescription pattern ports).material.Canonical) :
    Erasure.Exposure.exposedRegion (exposureDescription pattern ports)
        materialCanonical =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (identityBoundary pattern) ports := by
  simp only [Erasure.Exposure.exposedRegion]
  change Region.adjoinAt [] .nil
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)) materialCanonical)
      (Erasure.Exposure.applicationPorts
        (exposureDescription pattern ports))) = _
  rw [supportPattern_eq_identityBoundary pattern materialCanonical,
    exposureDescription_applicationPorts]
  rw [← instantiate_renameWires (identityBoundary pattern) ports
    (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming targetWires (targetWires ++ []))]
  have spliced := spliceAt_nil
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports)
    (WireRenaming.id : WireRenaming targetWires targetWires)
  rw [Region.renameWires_id] at spliced
  simpa only [Region.spliceAt, WireRenaming.id] using spliced

/-- One actual instantiation occurrence is bidirectionally equivalent to the
same application through the exact ordered identity-boundary normal form. -/
theorem equatesIdentityBoundary
    {boundary targetWires arguments : List Sig}
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports) source) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports)).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports)),
        Equates occurrence
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports)
          targetCanonical targetExternalTwoEnded := by
  let normalized :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports
  have normalizedCanonical : normalized.Canonical :=
    instantiate_canonical (identityBoundary pattern) ports
  have sameNonempty : ∀ {signature} (wire : Var targetWires signature),
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).incidencePaths wire.index.val ≠ [] ↔
        normalized.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [instantiate_incidence_nonempty_iff,
      instantiate_incidence_nonempty_iff]
  have replacement := occurrence.context.replaceCanonical
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports) normalized occurrence.sourceCanonical
      normalizedCanonical sameNonempty
  let targetCanonical := replacement.1
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports)) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill normalized) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill normalized) replacement.2
  refine ⟨targetCanonical, targetExternalTwoEnded, ?_⟩
  let description := exposureDescription pattern ports
  have sourceEq : description.source =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports := by
    simpa only [description] using exposureDescription_source pattern ports
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
      simpa only [sourceEq] using occurrence.host_iso
  }
  have materialCanonical : description.material.Canonical := by
    simpa only [description, exposureDescription] using
      instantiate_canonical pattern (formalPorts arguments)
  have exposedEq :
      Erasure.Exposure.exposedRegion description materialCanonical =
        normalized := by
    simpa only [description, normalized] using
      exposureDescription_exposedRegion pattern ports materialCanonical
  have exposedCanonical :
      (exposureOccurrence.context.fill
        (Erasure.Exposure.exposedRegion description
          materialCanonical)).Canonical := by
    rw [exposedEq]
    exact targetCanonical
  have exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      exposureOccurrence.interface.boundaryWire
      (exposureOccurrence.context.fill
        (Erasure.Exposure.exposedRegion description
          materialCanonical)) := by
    intro signature wire
    rw [exposedEq]
    exact targetExternalTwoEnded wire
  have equivalent := Erasure.Exposure.equatesEmptyHost description
    exposureOccurrence (by rfl) materialCanonical exposedCanonical
      exposedExternalTwoEnded
  simpa only [Equates, exposureOccurrence, exposedEq, normalized] using
    equivalent

end EqualityNormalization

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
theorem FormalPhase.compile
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
theorem IdentityPhase.compile
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

/-- Exact authoritative ArgumentPermutation inputs for one boundary order. -/
structure PermutationTarget
    {patternWires sourceArguments : List Sig}
    (body : Region patternWires)
    (shape : PatternShape body sourceArguments) where
  targetArguments : List Sig
  permutation : ArgumentPermutation.Permutation sourceArguments
    targetArguments
  outer : List Sig
  before : List Sig
  after : List Sig
  source : ItemSeq
    (outer ++ (before ++ .rel sourceArguments :: after))
  result : Region (outer ++ (before ++ after))
  authority : ItemsAuthority shape.pattern
    (ArgumentPermutation.operation sourceArguments targetArguments permutation)
    (ArgumentPermutation.rootFrame outer before after sourceArguments
      targetArguments)
    (ArgumentPermutation.targetHead outer before after targetArguments)
    source result (.mk (before ++ .rel sourceArguments :: after) source)

namespace PermutationTarget

variable {patternWires sourceArguments : List Sig}
variable {body : Region patternWires}
variable {shape : PatternShape body sourceArguments}

abbrev goal (target : PermutationTarget body shape) : Goal :=
  target.authority.goal
abbrev Output (target : PermutationTarget body shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : PermutationTarget body shape)
    (output : target.Output) : Region target.outer :=
  target.authority.staged output

private def description (target : PermutationTarget body shape)
    (output : target.Output) :
    ArgumentPermutation.Permutes.Description target.outer := {
  sourceArguments := sourceArguments
  targetArguments := target.targetArguments
  before := target.before
  after := target.after
  permutation := target.permutation
  items := target.source
  itemsEdit := output.edit
}

private theorem staged_eq_target (target : PermutationTarget body shape)
    (output : target.Output) :
    target.staged output = (target.description output).target := by
  change Region.adjoinAt
    (target.before ++ .rel target.targetArguments :: target.after)
      .nil output.endpoint =
    Region.adjoinAt
      (target.before ++ .rel target.targetArguments :: target.after)
      .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge
    (target : PermutationTarget body shape)
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
    (fun step => Step.argumentPermutation step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (Goal.preparationResult result) (target.staged_eq_target output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (Or.inr (.permute (.mk description)))

end PermutationTarget

/-- Exact authoritative ArgumentDuplicate inputs for one repeated boundary
position. -/
structure DuplicateTarget
    {patternWires before after : List Sig}
    {signature : Sig}
    (body : Region patternWires)
    (shape : PatternShape body (before ++ signature :: after)) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  authority : ItemsAuthority shape.pattern
    (Argument.Duplicate.operation before after signature)
    (Argument.Duplicate.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Duplicate.targetHead outer localBefore localAfter before after
      signature)
    source result (.mk (localBefore ++
      .rel (before ++ signature :: after) :: localAfter) source)

namespace DuplicateTarget

variable {patternWires before after : List Sig} {signature : Sig}
variable {body : Region patternWires}
variable {shape : PatternShape body (before ++ signature :: after)}

abbrev goal (target : DuplicateTarget body shape) : Goal :=
  target.authority.goal
abbrev Output (target : DuplicateTarget body shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : DuplicateTarget body shape) (output : target.Output) :
    Region target.outer := target.authority.staged output

private def description (target : DuplicateTarget body shape)
    (output : target.Output) :
    Argument.Duplicate.Duplicates.Description target.outer := {
  before := before
  after := after
  localBefore := target.localBefore
  localAfter := target.localAfter
  signature := signature
  items := target.source
  itemsEdit := output.edit
}

private theorem staged_eq_target (target : DuplicateTarget body shape)
    (output : target.Output) :
    target.staged output = (target.description output).target := by
  change Region.adjoinAt (target.localBefore ++
    .rel (before ++ signature :: signature :: after) :: target.localAfter)
      .nil output.endpoint =
    Region.adjoinAt (target.localBefore ++
      .rel (before ++ signature :: signature :: after) :: target.localAfter)
      .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge (target : DuplicateTarget body shape)
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
    (fun step => Step.argumentDuplicate step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (Goal.preparationResult result) (target.staged_eq_target output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (Or.inr (.duplicate (.mk description)))

end DuplicateTarget

/-- Exact authoritative ArgumentProjection inputs for one omitted boundary
position. The compiler fixes the directed local phase to extension. -/
structure ProjectionTarget
    {patternWires before after : List Sig}
    {signature : Sig}
    (body : Region patternWires)
    (shape : PatternShape body (before ++ signature :: after)) where
  outer : List Sig
  localBefore : List Sig
  localAfter : List Sig
  source : ItemSeq (outer ++ (localBefore ++
    .rel (before ++ signature :: after) :: localAfter))
  result : Region (outer ++ (localBefore ++ localAfter))
  authority : ItemsAuthority shape.pattern
    (Argument.Projection.operation before after signature)
    (Argument.Projection.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Projection.targetHead outer localBefore localAfter before after)
    source result (.mk (localBefore ++
      .rel (before ++ signature :: after) :: localAfter) source)

namespace ProjectionTarget

variable {patternWires before after : List Sig} {signature : Sig}
variable {body : Region patternWires}
variable {shape : PatternShape body (before ++ signature :: after)}

abbrev goal (target : ProjectionTarget body shape) : Goal :=
  target.authority.goal
abbrev Output (target : ProjectionTarget body shape) : Type :=
  ItemsAuthority.Output target.authority
def staged (target : ProjectionTarget body shape) (output : target.Output) :
    Region target.outer := target.authority.staged output

private def dropsDescription (target : ProjectionTarget body shape)
    (output : target.Output) : Argument.Projection.Drops.Description
      target.outer := {
  before := before
  after := after
  localBefore := target.localBefore
  localAfter := target.localAfter
  signature := signature
  items := target.source
  itemsEdit := output.edit
}

private def description (target : ProjectionTarget body shape)
    (output : target.Output) : Argument.Projection.Local.Description
      target.outer :=
  .extend (target.dropsDescription output)

private theorem staged_eq_source (target : ProjectionTarget body shape)
    (output : target.Output) :
    target.staged output = (target.description output).source := by
  change Region.adjoinAt
    (target.localBefore ++ .rel (before ++ after) :: target.localAfter)
      .nil output.endpoint =
    Region.adjoinAt
      (target.localBefore ++ .rel (before ++ after) :: target.localAfter)
      .nil output.edit.run
  rw [output.run_eq]

private noncomputable def discharge (target : ProjectionTarget body shape)
    (output : target.Output)
    (result : (Goal.preparation target.goal (target.staged output)
      (target.authority.stagedCanonical output)
      (target.authority.stagedExternalTwoEnded output)).Result) :
    target.authority.request.Discharge (target.staged output) := by
  let description := target.description output
  exact dischargeAtAuthoritativeEdit
    (goal := target.goal)
    (staged := target.staged output)
    (rawPrepared := description.source)
    (rawPending := description.target)
    (fun step => Step.argumentProjection step)
    (target.authority.stagedCanonical output)
    (target.authority.stagedExternalTwoEnded output)
    (Goal.preparationResult result) (target.staged_eq_source output)
    (by exact target.authority.request.pendingCanonical)
    (by exact target.authority.request.pendingExternalTwoEnded)
    (RegionIso.refl _) (.mk description)

end ProjectionTarget

mutual
  /-- Type-valued compiler evidence indexed by one existing region. -/
  inductive RegionPlan :
      {wires : List Sig} → Region wires → Goal → Type 1
    | mk
        {outer locals : List Sig}
        {items : ItemSeq (outer ++ locals)}
        {goal : Goal}
        (boundary : BoundaryPlan (.mk locals items) goal) :
        RegionPlan (.mk locals items) goal

  /-- Boundary normalization retains the exact existing region syntax and
  recurses only at the endpoint returned by the authoritative edit fold. -/
  inductive BoundaryPlan :
      {wires : List Sig} → Region wires → Goal → Type 1
    | arity
        {wires : List Sig} {body : Region wires} {goal : Goal}
        (plan : ArityPlan body goal) : BoundaryPlan body goal
    | permutation
        {wires sourceArguments : List Sig}
        {body : Region wires}
        {shape : PatternShape body sourceArguments}
        (target : PermutationTarget body shape)
        (child : ∀ output : target.Output,
          BoundaryPlan body (Goal.preparation target.goal
            (target.staged output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        BoundaryPlan body target.goal
    | duplicate
        {wires before after : List Sig} {signature : Sig}
        {body : Region wires}
        {shape : PatternShape body (before ++ signature :: after)}
        (target : DuplicateTarget body shape)
        (child : ∀ output : target.Output,
          BoundaryPlan body (Goal.preparation target.goal
            (target.staged output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        BoundaryPlan body target.goal
    | projection
        {wires before after : List Sig} {signature : Sig}
        {body : Region wires}
        {shape : PatternShape body (before ++ signature :: after)}
        (target : ProjectionTarget body shape)
        (child : ∀ output : target.Output,
          BoundaryPlan body (Goal.preparation target.goal
            (target.staged output)
            (target.authority.stagedCanonical output)
            (target.authority.stagedExternalTwoEnded output))) :
        BoundaryPlan body target.goal

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
  def regionResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : RegionPlan body goal) : goal.Result :=
    match plan with
    | .mk boundary => boundaryResult boundary
  termination_by structural plan

  /-- Interpret boundary phases through their authoritative all-sites folds. -/
  def boundaryResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : BoundaryPlan body goal) : goal.Result :=
    match plan with
    | .arity arity => arityResult arity
    | .permutation target child =>
        Compiler.items
          (operation := ArgumentPermutation.operation _ _ target.permutation)
          (frame := ArgumentPermutation.rootFrame target.outer target.before
            target.after _ target.targetArguments)
          (ArgumentPermutation.targetHead target.outer target.before
            target.after target.targetArguments)
          target.authority.evidence
          target.authority.sites target.authority.request {
            close := fun (output : target.Output) =>
              target.discharge output (boundaryResult (child output))
          }
    | .duplicate target child =>
        Compiler.items
          (operation := Argument.Duplicate.operation _ _ _)
          (frame := Argument.Duplicate.rootFrame target.outer
            target.localBefore target.localAfter _ _ _)
          (Argument.Duplicate.targetHead target.outer target.localBefore
            target.localAfter _ _ _)
          target.authority.evidence target.authority.sites
          target.authority.request {
            close := fun (output : target.Output) =>
              target.discharge output (boundaryResult (child output))
          }
    | .projection target child =>
        Compiler.items
          (operation := Argument.Projection.operation _ _ _)
          (frame := Argument.Projection.rootFrame target.outer
            target.localBefore target.localAfter _ _ _)
          (Argument.Projection.targetHead target.outer target.localBefore
            target.localAfter _ _)
          target.authority.evidence target.authority.sites
          target.authority.request {
            close := fun (output : target.Output) =>
              target.discharge output (boundaryResult (child output))
          }
  termination_by structural plan

  /-- Interpret arity phases through their authoritative all-sites folds. -/
  def arityResult
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
  def itemsResult
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
  def itemResult
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
    (plan : RegionPlan pattern.body goal) : goal.Result := by
  exact regionResult plan

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
