import VisualProof.Rule.Relation
import VisualProof.Rule.WirePrimitive.Transform

namespace VisualProof.Rule.WirePrimitive

open Theory
open Diagram

namespace ArgumentPermutation

/-- A typed reordering of argument tuples, with syntax and value actions kept
in lockstep. The inverse data makes non-bijective maps unrepresentable. -/
structure Permutation (source target : List Sig) where
  mapVars : ∀ {context}, Vars context source → Vars context target
  unmapVars : ∀ {context}, Vars context target → Vars context source
  mapValues : ∀ (model : Model), Values model source → Values model target
  unmapValues : ∀ (model : Model), Values model target → Values model source
  map_unmap_vars : ∀ {context} (values : Vars context target),
    mapVars (unmapVars values) = values
  unmap_map_vars : ∀ {context} (values : Vars context source),
    unmapVars (mapVars values) = values
  map_unmap_values : ∀ (model : Model) (values : Values model target),
    mapValues model (unmapValues model values) = values
  unmap_map_values : ∀ (model : Model) (values : Values model source),
    unmapValues model (mapValues model values) = values
  evaluate_map : ∀ {context} (model : Model)
    (variables : Vars context source) (env : Values model context),
    evaluateVars (mapVars variables) env =
      mapValues model (evaluateVars variables env)
  evaluate_unmap : ∀ {context} (model : Model)
    (variables : Vars context target) (env : Values model context),
    evaluateVars (unmapVars variables) env =
      unmapValues model (evaluateVars variables env)

def Permutation.symm (permutation : Permutation source target) :
    Permutation target source where
  mapVars := permutation.unmapVars
  unmapVars := permutation.mapVars
  mapValues := permutation.unmapValues
  unmapValues := permutation.mapValues
  map_unmap_vars := permutation.unmap_map_vars
  unmap_map_vars := permutation.map_unmap_vars
  map_unmap_values := permutation.unmap_map_values
  unmap_map_values := permutation.map_unmap_values
  evaluate_map := permutation.evaluate_unmap
  evaluate_unmap := permutation.evaluate_map

def operation (sourceArguments targetArguments : List Sig)
    (permutation : Permutation sourceArguments targetArguments) :
    Transform.Operation sourceArguments where
  Data := fun {_ _ targetWires} _ =>
    Var targetWires (.rel targetArguments)
  appendData := fun _ targetHead locals => targetHead.appendLeft locals
  SiteData := fun _ _ _ => PUnit
  site := fun frame targetHead ports _ =>
    Region.singleton (.atom targetHead
      (permutation.mapVars
        (ports.map fun wire => frame.targetKeep wire)))
  pin := fun _ targetHead => Transform.unaryPin targetHead

def rootFrame (outer before after sourceArguments targetArguments : List Sig) :=
  Transform.Frame.replace outer before after [.rel targetArguments]
    sourceArguments

def targetHead (outer before after targetArguments : List Sig) :
    Var (outer ++ (before ++ .rel targetArguments :: after))
      (.rel targetArguments) :=
  Transform.Frame.insertedHead outer before after (.rel targetArguments)

structure Permutes.Description (outer : List Sig) where
  sourceArguments : List Sig
  targetArguments : List Sig
  before : List Sig
  after : List Sig
  permutation : Permutation sourceArguments targetArguments
  items : ItemSeq (outer ++ (before ++ .rel sourceArguments :: after))
  itemsEdit : Transform.ItemsEdit
    (operation sourceArguments targetArguments permutation)
    (rootFrame outer before after sourceArguments targetArguments)
    (targetHead outer before after targetArguments) items

def Permutes.Description.source (description : Permutes.Description outer) :
    Region outer :=
  .mk (description.before ++
    .rel description.sourceArguments :: description.after) description.items

def Permutes.Description.target (description : Permutes.Description outer) :
    Region outer :=
  Region.adjoinAt
    (description.before ++ .rel description.targetArguments :: description.after)
    .nil description.itemsEdit.run

inductive Permutes : Region outer → Region outer → Prop
  | mk (description : Permutes.Description outer) :
      Permutes description.source description.target

inductive Local : LocalRule
  | permute (step : Permutes before after) : Local before after

end ArgumentPermutation

def ArgumentPermutation : Rule :=
  Contextual fun before after =>
    symmetric ArgumentPermutation.Local before after

theorem ArgumentPermutation.iso
    (sourceIso : OpenDiagramIso source source')
    (step : ArgumentPermutation source target)
    (targetIso : OpenDiagramIso target target') :
    ArgumentPermutation source' target' :=
  Contextual.iso sourceIso step targetIso

end VisualProof.Rule.WirePrimitive
