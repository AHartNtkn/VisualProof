import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Diagram

def OpenDiagram.asRelation
    (model : Model)
    (pattern : OpenDiagram arity) :
    Relation model.Carrier arity :=
  fun args => denoteOpen model pattern args

end VisualProof.Diagram

namespace VisualProof.Rule

open Theory
open Diagram

namespace Comprehension

inductive Image (targetRels : RelCtx) : Nat → Type
  | variable
      (relation : RelVar targetRels arity) :
      Image targetRels arity
  | diagram
      (pattern : OpenDiagram arity) :
      Image targetRels arity

abbrev Mapping (sourceRels targetRels : RelCtx) :=
  {arity : Nat} →
    RelVar sourceRels arity →
    Image targetRels arity

def Image.weaken
    (head : Nat)
    {arity : Nat} :
    Image targetRels arity →
      Image (head :: targetRels) arity
  | .variable relation =>
      .variable
        (RelationRenaming.weaken head relation)
  | .diagram pattern =>
      .diagram pattern

def Mapping.lift
    (mapping : Mapping sourceRels targetRels)
    (head : Nat) :
    Mapping (head :: sourceRels) (head :: targetRels) :=
  fun {arity} relation =>
    match relation with
    | ⟨index, hasArity⟩ =>
        Fin.cases
          (motive := fun i =>
            (head :: sourceRels).get i = arity →
              Image (head :: targetRels) arity)
          (fun equality =>
            .variable ⟨0, equality⟩)
          (fun tailIndex equality =>
            Image.weaken head
              (mapping
                (⟨tailIndex, equality⟩ :
                  RelVar sourceRels arity)))
          index hasArity

def Mapping.instantiateHead
    (pattern : OpenDiagram relationArity) :
    Mapping (relationArity :: rels) rels :=
  fun {arity} relation =>
    match relation with
    | ⟨index, hasArity⟩ =>
        Fin.cases
          (motive := fun i =>
            (relationArity :: rels).get i = arity →
              Image rels arity)
          (fun equality =>
            .diagram (pattern.castArity equality))
          (fun tailIndex equality =>
            .variable
              (⟨tailIndex, equality⟩ :
                RelVar rels arity))
          index hasArity

def singleton
    (item : Item wires rels) :
    Region wires rels :=
  .mk 0 (.cons item .nil)

namespace Instantiation

mutual
  inductive RegionResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      Region wires sourceRels →
      Region wires targetRels →
      Prop
    | mk
        {mapping : Mapping sourceRels targetRels}
        {localWires : Nat}
        {items : ItemSeq (wires + localWires) sourceRels}
        {result : Region (wires + localWires) targetRels}
        (items_result :
          ItemsResult mapping items result) :
        RegionResult mapping
          (.mk localWires items)
          (Region.adjoinAt localWires .nil result)

  inductive ItemsResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      ItemSeq wires sourceRels →
      Region wires targetRels →
      Prop
    | nil
        {mapping : Mapping sourceRels targetRels} :
        ItemsResult mapping .nil Region.blank
    | cons
        {mapping : Mapping sourceRels targetRels}
        {item : Item wires sourceRels}
        {tail : ItemSeq wires sourceRels}
        {itemResult tailResult : Region wires targetRels}
        (item_result :
          ItemResult mapping item itemResult)
        (tail_result :
          ItemsResult mapping tail tailResult) :
        ItemsResult mapping
          (.cons item tail)
          (itemResult.conjoin tailResult)

  inductive ItemResult :
      {sourceRels targetRels : RelCtx} →
      Mapping sourceRels targetRels →
      {wires : Nat} →
      Item wires sourceRels →
      Region wires targetRels →
      Prop
    | atomVariable
        {mapping : Mapping sourceRels targetRels}
        {arity : Nat}
        {relation : RelVar sourceRels arity}
        {arguments : Fin arity → Fin wires}
        (mapped : RelVar targetRels arity)
        (image :
          mapping relation = Image.variable mapped) :
        ItemResult mapping
          (.atom relation arguments)
          (singleton (.atom mapped arguments))

    | atomDiagram
        {mapping : Mapping sourceRels targetRels}
        {arity : Nat}
        {relation : RelVar sourceRels arity}
        {arguments : Fin arity → Fin wires}
        (pattern : OpenDiagram arity)
        (image :
          mapping relation = Image.diagram pattern)
        (assignment :
          BoundaryAssignment pattern (Fin wires))
        (arguments_eq :
          assignment.args = arguments) :
        ItemResult mapping
          (.atom relation arguments)
          ((pattern.substituteBoundary assignment).renameRelations
            RelationRenaming.empty)

    | identity
        {mapping : Mapping sourceRels targetRels}
        (arity : Nat)
        (arguments : Fin arity → Fin wires) :
        ItemResult mapping
          (.identity arity arguments)
          (singleton (.identity arity arguments))

    | cut
        {mapping : Mapping sourceRels targetRels}
        {body : Region wires sourceRels}
        {result : Region wires targetRels}
        (body_result :
          RegionResult mapping body result) :
        ItemResult mapping
          (.cut body)
          (singleton (.cut result))

    | bubble
        {mapping : Mapping sourceRels targetRels}
        (arity : Nat)
        {body : Region wires (arity :: sourceRels)}
        {result : Region wires (arity :: targetRels)}
        (body_result :
          RegionResult (mapping.lift arity) body result) :
        ItemResult mapping
          (.bubble arity body)
          (singleton (.bubble arity result))
end

end Instantiation

def Instantiates
    (pattern : OpenDiagram relationArity)
    (quantified : Region wires (relationArity :: rels))
    (specialized : Region wires rels) :
    Prop :=
  Instantiation.RegionResult
    (Mapping.instantiateHead pattern)
    quantified specialized

inductive Local : LocalRule
  | comprehend
      (hostLocal : Nat)
      (hostItems : ItemSeq (wires + hostLocal) rels)
      (relationArity : Nat)
      (pattern : OpenDiagram relationArity)
      (body : Region materialWires (relationArity :: materialRels))
      (specialized : Region materialWires materialRels)
      (instantiates : Instantiates pattern body specialized)
      (wireMap : Fin materialWires → Fin (wires + hostLocal))
      (relationMap : RelationRenaming materialRels rels) :
      Local
        (Region.spliceAt hostLocal hostItems specialized wireMap relationMap)
        (Region.spliceAt hostLocal hostItems
          (singleton (.bubble relationArity body)) wireMap relationMap)

end Comprehension

def Comprehension : Rule :=
  Contextual fun specialized quantified =>
    Comprehension.Local specialized quantified

theorem Comprehension.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Comprehension source target)
    (targetIso : OpenDiagramIso target target') :
    Comprehension source' target' := by
  exact Contextual.iso sourceIso step targetIso

end VisualProof.Rule
