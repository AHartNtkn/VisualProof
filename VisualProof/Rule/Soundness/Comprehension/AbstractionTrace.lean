import VisualProof.Rule.Comprehension

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace AbstractionRawTrace

abbrev Domains (input : CheckedDiagram signature)
    (occurrences : List (AbstractionOccurrence input)) :=
  abstractionDomains input occurrences

def bubble
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    Fin (Domains input occurrences).regions.count.succ :=
  Fin.last (Domains input occurrences).regions.count

def diagram
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    ConcreteDiagram where
  regionCount := (Domains input occurrences).regions.count + 1
  nodeCount := (Domains input occurrences).nodes.count + occurrences.length
  wireCount := (Domains input occurrences).wires.count
  root := trace.rootBase.castSucc
  regions := Fin.lastCases
    (.bubble trace.parentBase.castSucc comprehension.val.boundary.length)
    trace.regions
  nodes := Fin.addCases trace.nodes fun index =>
    .atom (trace.atomOwners index) trace.bubble
  wires := trace.wires

theorem raw_eq_diagram
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    raw = trace.diagram :=
  trace.raw_eq

@[simp] theorem raw_regionCount
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    raw.regionCount = (Domains input occurrences).regions.count + 1 := by
  rw [trace.raw_eq_diagram]
  rfl

@[simp] theorem raw_nodeCount
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    raw.nodeCount = (Domains input occurrences).nodes.count + occurrences.length := by
  rw [trace.raw_eq_diagram]
  rfl

@[simp] theorem raw_wireCount
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    raw.wireCount = (Domains input occurrences).wires.count := by
  rw [trace.raw_eq_diagram]
  rfl

@[simp] theorem diagram_root
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    trace.diagram.root = trace.rootBase.castSucc := rfl

theorem root_origin
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    (Domains input occurrences).regions.origin trace.rootBase = input.val.root :=
  ((Domains input occurrences).regions.index?_eq_some_iff input.val.root
    trace.rootBase).1
    trace.root_result

theorem parent_origin
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    (Domains input occurrences).regions.origin trace.parentBase =
      wrap.val.anchor :=
  ((Domains input occurrences).regions.index?_eq_some_iff wrap.val.anchor
    trace.parentBase).1
    trace.parent_result

theorem region_result
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin (Domains input occurrences).regions.count) :
    abstractRegion? input wrap occurrences (Domains input occurrences)
        trace.bubble ((Domains input occurrences).regions.origin region) =
      some (trace.regions region) := by
  exact sequenceFin_sound trace.regions_result region

theorem node_result
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin (Domains input occurrences).nodes.count) :
    abstractNode? input wrap occurrences (Domains input occurrences)
        trace.bubble ((Domains input occurrences).nodes.origin node) =
      some (trace.nodes node) := by
  exact sequenceFin_sound trace.nodes_result node

theorem atomOwner_result
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (index : Fin occurrences.length) :
    (let anchor := (occurrences.get index).selection.val.anchor
      if anchor = wrap.val.anchor then some trace.bubble
      else (Domains input occurrences).regions.index? anchor |>.map
        Fin.castSucc) =
        some (trace.atomOwners index) := by
  exact sequenceFin_sound trace.atomOwners_result index

theorem wire_result
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin (Domains input occurrences).wires.count) :
    (do
      let scopeBase ← (Domains input occurrences).regions.index?
        (input.val.wires ((Domains input occurrences).wires.origin wire)).scope
      pure {
        scope := scopeBase.castSucc
        endpoints := abstractFrameEndpoints input occurrences
            (Domains input occurrences) wire ++
          abstractAtomEndpoints input occurrences (Domains input occurrences) wire
      }) = some (trace.wires wire) := by
  exact sequenceFin_sound trace.wires_result wire

@[simp] theorem diagram_survivorRegion
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin (Domains input occurrences).regions.count) :
    trace.diagram.regions region.castSucc = trace.regions region := by
  simp [diagram]

@[simp] theorem diagram_bubble
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    trace.diagram.regions trace.bubble =
      .bubble trace.parentBase.castSucc comprehension.val.boundary.length := by
  simp [diagram, bubble]

@[simp] theorem diagram_survivorNode
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin (Domains input occurrences).nodes.count) :
    trace.diagram.nodes (Fin.castAdd occurrences.length node) =
      trace.nodes node := by
  simp [diagram]

@[simp] theorem diagram_atom
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (index : Fin occurrences.length) :
    trace.diagram.nodes
        (Fin.natAdd (Domains input occurrences).nodes.count index) =
      .atom (trace.atomOwners index) trace.bubble := by
  simp [diagram, bubble]

@[simp] theorem diagram_wire
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (wire : Fin (Domains input occurrences).wires.count) :
    trace.diagram.wires wire = trace.wires wire := rfl

end AbstractionRawTrace

end VisualProof.Rule
