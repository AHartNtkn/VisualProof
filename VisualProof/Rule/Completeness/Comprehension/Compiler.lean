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

/-- Task-5 supplies only the structural goals for regions, item sequences,
and cuts. Atom and identity goals remain fixed to the exact leaf phase data
above and therefore cannot replace the final primitive discharge. -/
structure Motive where
  region : ∀ {wires : List Sig}, Region wires → Prop
  items : ∀ {wires : List Sig}, ItemSeq wires → Prop
  cut : ∀ {wires : List Sig}, Region wires → Prop

/-- The compiler goal for one existing item constructor. -/
def ItemGoal (motive : Motive) :
    ∀ {wires : List Sig}, Item wires → Prop
  | _, .atom head ports =>
      ∀ (shape : FormalShape head ports) (phase : FormalPhase shape),
        phase.request.Result
  | _, .identity signature arity ports =>
      ∀ (shape : IdentityShape signature arity ports)
        (phase : IdentityPhase shape), phase.request.Result
  | _, .cut body => motive.cut body

/-- Structural constructor handlers scheduled for Task 5. No leaf handler is
present: the fold below owns both leaf calls. -/
structure Handlers (motive : Motive) where
  region : ∀ {outer : List Sig} (locals : List Sig)
    (items : ItemSeq (outer ++ locals)),
    motive.items items → motive.region (.mk locals items)
  nil : ∀ {wires : List Sig}, motive.items (.nil : ItemSeq wires)
  cons : ∀ {wires : List Sig} (head : Item wires) (tail : ItemSeq wires),
    ItemGoal motive head → motive.items tail →
      motive.items (.cons head tail)
  cut : ∀ {wires : List Sig} (body : Region wires),
    motive.region body → motive.cut body

mutual
  /-- Compile an existing region with fixed leaf phases and caller-supplied
  structural handlers. -/
  def region (handlers : Handlers motive) (body : Region wires) :
      motive.region body :=
    match body with
    | .mk locals bodyItems =>
        handlers.region locals bodyItems (itemSeq handlers bodyItems)

  /-- Compile an existing item sequence with fixed leaf phases and
  caller-supplied structural handlers. -/
  def itemSeq (handlers : Handlers motive) (bodyItems : ItemSeq wires) :
      motive.items bodyItems :=
    match bodyItems with
    | .nil => handlers.nil
    | .cons head tail =>
        handlers.cons head tail (item handlers head) (itemSeq handlers tail)

  /-- Compile one existing item. Atom and identity branches immediately call
  the production leaf phases; only cut delegates to a structural handler. -/
  def item (handlers : Handlers motive) (bodyItem : Item wires) :
      ItemGoal motive bodyItem :=
    match bodyItem with
    | .atom _ _ => fun _ phase => phase.compile
    | .identity _ _ _ => fun _ phase => phase.compile
    | .cut body => handlers.cut body (region handlers body)
end

/-- Production entry over the current `OpenDiagram`/`Region` syntax. Task 5
can fill the structural handler algebra without restating either leaf
contract. -/
theorem compile (handlers : Handlers motive)
    (pattern : OpenDiagram arguments) : motive.region pattern.body := by
  exact region handlers pattern.body

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
