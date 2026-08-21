import VisualProof.Rule.Completeness.Comprehension.Telescope

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

/-- Evidence for one primitive at a fixed local-rule family. It contains the
exact staged and raw endpoints, validity, presentation isomorphisms, and
preparation, but deliberately contains neither a `Step` injection nor a
compiled result. -/
structure PrimitivePhase (localRule : LocalRule) (goal : Goal) where
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
private theorem compilePrimitive
    {localRule : LocalRule}
    {goal : Goal}
    (inject : ∀ {stepBoundary : List Sig}
      {stepSource stepTarget : OpenDiagram stepBoundary},
      Contextual localRule stepSource stepTarget →
        Step stepSource stepTarget)
    (phase : PrimitivePhase localRule goal) : goal.Result := by
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
  exact (Telescope.Request.Discharge.primitive branch phase.stagedIso).compile

/-- Fixed CutShape local family. -/
abbrev CutLocal : LocalRule :=
  fun before after => symmetric Content.Cut.Local before after

/-- Fixed ParallelShape local family. -/
abbrev ParallelLocal : LocalRule :=
  fun before after => symmetric Content.Parallel.Local before after

/-- Fixed Arity local family. -/
abbrev ArityLocal : LocalRule :=
  fun before after => symmetric Arity.Local before after

/-- Exact evidence for one CutShape phase. -/
abbrev CutPhase (goal : Goal) := PrimitivePhase CutLocal goal

/-- Exact evidence for one ParallelShape phase. -/
abbrev ParallelPhase (goal : Goal) := PrimitivePhase ParallelLocal goal

/-- Exact evidence for one Arity phase. -/
abbrev ArityPhase (goal : Goal) := PrimitivePhase ArityLocal goal

/-- Cut phases always inject the fixed CutShape primitive. -/
theorem CutPhase.compile (phase : CutPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.cutShape step) phase

/-- Parallel phases always inject the fixed ParallelShape primitive. -/
theorem ParallelPhase.compile (phase : ParallelPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.parallelShape step) phase

/-- Arity phases always inject the fixed Arity primitive. -/
theorem ArityPhase.compile (phase : ArityPhase goal) : goal.Result := by
  exact compilePrimitive (fun step => Step.arity step) phase

/-- A cut continuation can use the exact child result only to construct
CutShape evidence for its fixed target request. -/
structure CutPlan (source target : Goal) where
  phase : source.Result → CutPhase target

/-- A cons continuation can use both exact child results only to construct
ParallelShape evidence for its fixed target request. -/
structure ParallelPlan (head tail target : Goal) where
  phase : head.Result → tail.Result → ParallelPhase target

/-- One exact Arity continuation step. -/
structure ArityStep (source target : Goal) where
  phase : source.Result → ArityPhase target

/-- A finite zero-or-more chain of fixed Arity phases between exact goals. -/
inductive ArityPlan : Goal → Goal → Type
  | nil (goal : Goal) : ArityPlan goal goal
  | cons {source middle target : Goal}
      (head : ArityStep source middle)
      (tail : ArityPlan middle target) : ArityPlan source target

/-- Interpret every Arity phase in sequence; the zero case preserves the
same exact request index. -/
def ArityPlan.compile
    (plan : ArityPlan source target)
    (result : source.Result) : target.Result :=
  match plan with
  | .nil _ => result
  | .cons head tail =>
      tail.compile ((head.phase result).compile)

mutual
  /-- Type-valued compiler evidence indexed by an existing region. -/
  inductive RegionPlan :
      {wires : List Sig} → Region wires → Goal → Type
    | mk
        {outer locals : List Sig}
        {items : ItemSeq (outer ++ locals)}
        {source target : Goal}
        (itemsPlan : ItemsPlan items source)
        (arityPlan : ArityPlan source target) :
        RegionPlan (.mk locals items) target

  /-- Type-valued compiler evidence indexed by an existing item sequence. -/
  inductive ItemsPlan :
      {wires : List Sig} → ItemSeq wires → Goal → Type
    | nil {wires : List Sig} (phase : Compiler.NilPhase wires) :
        ItemsPlan (.nil : ItemSeq wires) (nilGoal phase)
    | cons
        {wires : List Sig}
        {head : Item wires} {tail : ItemSeq wires}
        {headGoal tailGoal target : Goal}
        (headPlan : ItemPlan head headGoal)
        (tailPlan : ItemsPlan tail tailGoal)
        (parallel : ParallelPlan headGoal tailGoal target) :
        ItemsPlan (.cons head tail) target

  /-- Type-valued compiler evidence indexed by an existing item. Leaf
  constructors carry only their exact production phases. -/
  inductive ItemPlan : {wires : List Sig} → Item wires → Goal → Type
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
        {wires : List Sig} {body : Region wires}
        {childGoal target : Goal}
        (child : RegionPlan body childGoal)
        (cutPlan : CutPlan childGoal target) :
        ItemPlan (.cut body) target
end

mutual
  /-- Interpret an exact region plan. Structural callbacks produce evidence;
  this fold alone converts every phase into a compiler result. -/
  def regionResult
      {wires : List Sig} {body : Region wires} {goal : Goal}
      (plan : RegionPlan body goal) : goal.Result :=
    match plan with
    | .mk itemsPlan arityPlan =>
        arityPlan.compile (itemsResult itemsPlan)
  termination_by structural plan

  /-- Interpret an exact item-sequence plan. Nil is fixed to Ends and cons is
  fixed to ParallelShape. -/
  def itemsResult
      {wires : List Sig} {bodyItems : ItemSeq wires} {goal : Goal}
      (plan : ItemsPlan bodyItems goal) : goal.Result :=
    match plan with
    | .nil phase => phase.compile
    | .cons headPlan tailPlan parallel =>
        (parallel.phase (itemResult headPlan)
          (itemsResult tailPlan)).compile
  termination_by structural plan

  /-- Interpret an exact item plan. Every constructor fixes its primitive
  family and no annotation can supply a compiled result. -/
  def itemResult
      {wires : List Sig} {bodyItem : Item wires} {goal : Goal}
      (plan : ItemPlan bodyItem goal) : goal.Result :=
    match plan with
    | .atom _ phase => phase.compile
    | .identity _ phase => phase.compile
    | .cut child cutPlan =>
        (cutPlan.phase (regionResult child)).compile
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
