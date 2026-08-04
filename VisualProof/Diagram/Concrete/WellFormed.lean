import VisualProof.Diagram.Concrete.Core

namespace VisualProof.Diagram

namespace ConcreteDiagram

def RootIsSheet (d : ConcreteDiagram) : Prop :=
  d.regions d.root = .sheet

instance (d : ConcreteDiagram) : Decidable (RootIsSheet d) := by
  unfold RootIsSheet
  infer_instance

def OnlyRootIsSheet (d : ConcreteDiagram) : Prop :=
  forall region : Fin d.regionCount,
    d.regions region = .sheet -> region = d.root

instance (d : ConcreteDiagram) : Decidable (OnlyRootIsSheet d) := by
  unfold OnlyRootIsSheet
  infer_instance

def AllRegionsReachRoot (d : ConcreteDiagram) : Prop :=
  forall region : Fin d.regionCount, d.ReachesRoot region

instance (d : ConcreteDiagram) : Decidable (AllRegionsReachRoot d) := by
  unfold AllRegionsReachRoot
  infer_instance

def AtomBindersAreBubbles (d : ConcreteDiagram) : Prop :=
  forall node : Fin d.nodeCount,
    match d.nodes node with
    | .atom _ binder =>
        exists parent arity, d.regions binder = .bubble parent arity
    | _ => True

instance (d : ConcreteDiagram) : Decidable (AtomBindersAreBubbles d) := by
  unfold AtomBindersAreBubbles
  apply @Nat.decidableForallFin _ _ (fun node => ?_)
  cases hnode : d.nodes node with
  | term => exact isTrue trivial
  | atom _ binder =>
      cases hbinder : d.regions binder with
      | sheet =>
          exact isFalse (by
            rintro ⟨parent, arity, h⟩
            simp [hbinder] at h)
      | cut _ =>
          exact isFalse (by
            rintro ⟨parent, arity, h⟩
            simp [hbinder] at h)
      | bubble parent arity => exact isTrue ⟨parent, arity, hbinder⟩
  | named => exact isTrue trivial

def AtomBindersEnclose (d : ConcreteDiagram) : Prop :=
  forall node : Fin d.nodeCount,
    match d.nodes node with
    | .atom region binder => d.Encloses binder region
    | _ => True

instance (d : ConcreteDiagram) : Decidable (AtomBindersEnclose d) := by
  unfold AtomBindersEnclose
  apply @Nat.decidableForallFin _ _ (fun node => ?_)
  cases hnode : d.nodes node with
  | term => exact isTrue trivial
  | atom region binder => exact inferInstance
  | named => exact isTrue trivial

def NamedReferencesResolve (signature : List Nat)
    (d : ConcreteDiagram) : Prop :=
  forall node : Fin d.nodeCount,
    match d.nodes node with
    | .named _ definition arity => signature[definition]? = some arity
    | _ => True

instance (signature : List Nat) (d : ConcreteDiagram) :
    Decidable (NamedReferencesResolve signature d) := by
  unfold NamedReferencesResolve
  apply @Nat.decidableForallFin _ _ (fun node => ?_)
  cases hnode : d.nodes node with
  | term => exact isTrue trivial
  | atom => exact isTrue trivial
  | named _ definition arity => exact inferInstance

def EndpointsAreValid (d : ConcreteDiagram) : Prop :=
  forall wire : Fin d.wireCount,
    forall endpoint : CEndpoint d.nodeCount,
      endpoint ∈ (d.wires wire).endpoints ->
        d.RequiresPort endpoint.node endpoint.port

instance (d : ConcreteDiagram) : Decidable (EndpointsAreValid d) := by
  unfold EndpointsAreValid
  infer_instance

def EndpointsAreNodup (d : ConcreteDiagram) : Prop :=
  forall wire : Fin d.wireCount, (d.wires wire).endpoints.Nodup

instance (d : ConcreteDiagram) : Decidable (EndpointsAreNodup d) := by
  unfold EndpointsAreNodup
  infer_instance

def WireEndpointsAreDisjoint (d : ConcreteDiagram) : Prop :=
  forall wire₁ wire₂ : Fin d.wireCount,
    wire₁ != wire₂ ->
      forall endpoint : CEndpoint d.nodeCount,
        endpoint ∈ (d.wires wire₁).endpoints ->
          not (d.EndpointOccurs wire₂ endpoint)

instance (d : ConcreteDiagram) : Decidable (WireEndpointsAreDisjoint d) := by
  unfold WireEndpointsAreDisjoint
  infer_instance

def RequiredPortsAreCovered (d : ConcreteDiagram) : Prop :=
  forall node : Fin d.nodeCount,
    match d.nodes node with
    | .term _ freePorts _ =>
        (exists wire, d.EndpointOccurs wire ⟨node, .output⟩) /\
          forall index : Fin freePorts,
            exists wire, d.EndpointOccurs wire ⟨node, .free index⟩
    | .atom _ binder =>
        match d.regions binder with
        | .bubble _ arity =>
            forall index : Fin arity,
              exists wire, d.EndpointOccurs wire ⟨node, .arg index⟩
        | _ => True
    | .named _ _ arity =>
        forall index : Fin arity,
          exists wire, d.EndpointOccurs wire ⟨node, .arg index⟩

instance (d : ConcreteDiagram) : Decidable (RequiredPortsAreCovered d) := by
  unfold RequiredPortsAreCovered
  apply @Nat.decidableForallFin _ _ (fun node => ?_)
  cases hnode : d.nodes node with
  | term _ freePorts _ =>
      let outputCovered : Decidable
          (exists wire, d.EndpointOccurs wire ⟨node, .output⟩) :=
        @Nat.decidableExistsFin _ _ (fun wire => inferInstance)
      let freePortsCovered : Decidable
          (forall index : Fin freePorts,
            exists wire, d.EndpointOccurs wire ⟨node, .free index⟩) :=
        @Nat.decidableForallFin _ _ (fun index =>
          @Nat.decidableExistsFin _ _ (fun wire => inferInstance))
      exact @instDecidableAnd _ _ outputCovered freePortsCovered
  | atom _ binder =>
      simp only
      cases hbinder : d.regions binder with
      | sheet =>
          simp only
          exact isTrue trivial
      | cut _ =>
          simp only
          exact isTrue trivial
      | bubble _ arity =>
          simp only
          exact @Nat.decidableForallFin _ _ (fun index =>
            @Nat.decidableExistsFin _ _ (fun wire => inferInstance))
  | named _ _ arity =>
      exact @Nat.decidableForallFin _ _ (fun index =>
        @Nat.decidableExistsFin _ _ (fun wire => inferInstance))

def WireScopesEnclose (d : ConcreteDiagram) : Prop :=
  forall wire : Fin d.wireCount,
    forall endpoint : CEndpoint d.nodeCount,
      d.EndpointOccurs wire endpoint ->
        d.Encloses (d.wires wire).scope (d.nodes endpoint.node).region

instance (d : ConcreteDiagram) : Decidable (WireScopesEnclose d) := by
  unfold WireScopesEnclose
  apply @Nat.decidableForallFin _ _ (fun wire => ?_)
  exact @List.decidableBAll _
    (fun endpoint : CEndpoint d.nodeCount =>
      d.Encloses (d.wires wire).scope (d.nodes endpoint.node).region)
    (fun endpoint => inferInstance) (d.wires wire).endpoints

structure WellFormed (d : ConcreteDiagram) (signature : List Nat) : Prop where
  root_is_sheet : RootIsSheet d
  only_root_is_sheet : OnlyRootIsSheet d
  all_regions_reach_root : AllRegionsReachRoot d
  atom_binders_are_bubbles : AtomBindersAreBubbles d
  atom_binders_enclose : AtomBindersEnclose d
  named_references_resolve : NamedReferencesResolve signature d
  endpoints_are_valid : EndpointsAreValid d
  endpoints_are_nodup : EndpointsAreNodup d
  wire_endpoints_are_disjoint : WireEndpointsAreDisjoint d
  required_ports_are_covered : RequiredPortsAreCovered d
  wire_scopes_enclose : WireScopesEnclose d

end ConcreteDiagram

abbrev CheckedDiagram (signature : List Nat) :=
  { d : ConcreteDiagram // d.WellFormed signature }

namespace OpenConcreteDiagram

structure WellFormed (d : OpenConcreteDiagram) (signature : List Nat) : Prop where
  diagram_well_formed : d.diagram.WellFormed signature
  boundary_is_root_scoped : forall wire, wire ∈ d.boundary ->
    (d.diagram.wires wire).scope = d.diagram.root

end OpenConcreteDiagram

inductive WFError
  | rootNotSheet
  | secondSheet
  | parentDoesNotReachRoot
  | binderNotBubble
  | binderDoesNotEnclose
  | namedReferenceDoesNotResolve
  | invalidEndpoint
  | duplicateEndpoint
  | endpointOnTwoWires
  | missingRequiredPort
  | wireScopeDoesNotEnclose
  deriving DecidableEq

def checkWellFormed (signature : List Nat) (d : ConcreteDiagram) :
    Except WFError (CheckedDiagram signature) :=
  if hroot : d.RootIsSheet then
    if honlyRoot : d.OnlyRootIsSheet then
      if hreach : d.AllRegionsReachRoot then
        if hbubbles : d.AtomBindersAreBubbles then
          if henclose : d.AtomBindersEnclose then
            if hresolve : d.NamedReferencesResolve signature then
              if hvalid : d.EndpointsAreValid then
                if hnodup : d.EndpointsAreNodup then
                  if hdisjoint : d.WireEndpointsAreDisjoint then
                    if hcovered : d.RequiredPortsAreCovered then
                      if hscopes : d.WireScopesEnclose then
                        .ok ⟨d, {
                            root_is_sheet := hroot
                            only_root_is_sheet := honlyRoot
                            all_regions_reach_root := hreach
                            atom_binders_are_bubbles := hbubbles
                            atom_binders_enclose := henclose
                            named_references_resolve := hresolve
                            endpoints_are_valid := hvalid
                            endpoints_are_nodup := hnodup
                            wire_endpoints_are_disjoint := hdisjoint
                            required_ports_are_covered := hcovered
                            wire_scopes_enclose := hscopes
                          }⟩
                      else .error .wireScopeDoesNotEnclose
                    else .error .missingRequiredPort
                  else .error .endpointOnTwoWires
                else .error .duplicateEndpoint
              else .error .invalidEndpoint
            else .error .namedReferenceDoesNotResolve
          else .error .binderDoesNotEnclose
        else .error .binderNotBubble
      else .error .parentDoesNotReachRoot
    else .error .secondSheet
  else .error .rootNotSheet

theorem checkWellFormed_preserves_input
    (hcheck : checkWellFormed signature d = .ok checked) :
    checked.val = d := by
  unfold checkWellFormed at hcheck
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  split at hcheck <;> try contradiction
  · cases hcheck
    rfl
  all_goals contradiction

theorem checkWellFormed_complete
    (h : d.WellFormed signature) :
    checkWellFormed signature d = .ok ⟨d, h⟩ := by
  unfold checkWellFormed
  simp only [dif_pos h.root_is_sheet, dif_pos h.only_root_is_sheet,
    dif_pos h.all_regions_reach_root, dif_pos h.atom_binders_are_bubbles,
    dif_pos h.atom_binders_enclose, dif_pos h.named_references_resolve,
    dif_pos h.endpoints_are_valid, dif_pos h.endpoints_are_nodup,
    dif_pos h.wire_endpoints_are_disjoint,
    dif_pos h.required_ports_are_covered, dif_pos h.wire_scopes_enclose]

theorem checkWellFormed_iff :
    (exists checked, checkWellFormed signature d = .ok checked /\
      checked.val = d) <->
      d.WellFormed signature := by
  constructor
  · rintro ⟨checked, _, rfl⟩
    exact checked.property
  · intro h
    exact ⟨⟨d, h⟩, checkWellFormed_complete h, rfl⟩

end VisualProof.Diagram
