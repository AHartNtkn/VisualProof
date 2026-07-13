import VisualProof.Diagram.Boundary

namespace VisualProof.Diagram

open VisualProof
open Theory

abbrev RelationRenaming (source target : RelCtx) :=
  {arity : Nat} -> RelVar source arity -> RelVar target arity

def extendWireRenaming (rho : Fin source -> Fin target) (localWires : Nat) :
    Fin (source + localWires) -> Fin (target + localWires) :=
  Fin.addCases
    (fun i => Fin.castAdd localWires (rho i))
    (fun i => Fin.natAdd target i)

theorem extendWireRenaming_id (localWires : Nat) :
    extendWireRenaming (source := source) id localWires = id := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [extendWireRenaming]

theorem extendWireRenaming_comp
    (rho : Fin source -> Fin middle) (tau : Fin middle -> Fin target)
    (localWires : Nat) :
    extendWireRenaming tau localWires ∘ extendWireRenaming rho localWires =
      extendWireRenaming (tau ∘ rho) localWires := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [extendWireRenaming]

def RelationRenaming.lift (rho : RelationRenaming source target)
    (head : Nat) : RelationRenaming (head :: source) (head :: target) :=
  fun {arity} relation =>
    match relation with
    | ⟨index, hasArity⟩ =>
      Fin.cases
        (motive := fun i =>
          (head :: source).get i = arity -> RelVar (head :: target) arity)
        (fun h => ⟨0, h⟩)
        (fun i h =>
          let renamed := rho (arity := arity) (⟨i, h⟩ : RelVar source arity)
          ⟨renamed.index.succ, renamed.hasArity⟩)
        index hasArity

theorem RelationRenaming.lift_id
    (relation : RelVar (head :: source) arity) :
    RelationRenaming.lift (fun r => r) head relation = relation := by
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun _ => ?_) index <;> intro hasArity <;> rfl

theorem RelationRenaming.lift_comp
    (rho : RelationRenaming source middle)
    (tau : RelationRenaming middle target)
    (relation : RelVar (head :: source) arity) :
    RelationRenaming.lift tau head (RelationRenaming.lift rho head relation) =
      RelationRenaming.lift (fun r => tau (rho r)) head relation := by
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun _ => ?_) index <;> intro hasArity <;> rfl

theorem RelationRenaming.lift_id_fun (head : Nat) :
    (RelationRenaming.lift (source := source) (fun r => r) head :
      RelationRenaming (head :: source) (head :: source)) =
      (fun {_} r => r) := by
  apply @funext
  intro arity
  funext relation
  exact RelationRenaming.lift_id relation

theorem RelationRenaming.lift_comp_fun
    (rho : RelationRenaming source middle)
    (tau : RelationRenaming middle target) (head : Nat) :
    ((fun {arity} (r : RelVar (head :: source) arity) =>
      RelationRenaming.lift tau head (RelationRenaming.lift rho head r)) :
      RelationRenaming (head :: source) (head :: target)) =
      (RelationRenaming.lift (fun r => tau (rho r)) head :
        RelationRenaming (head :: source) (head :: target)) := by
  apply @funext
  intro arity
  funext relation
  exact RelationRenaming.lift_comp rho tau relation

mutual
  def Region.renameWires (rho : Fin source -> Fin target) :
      Region signature source rels -> Region signature target rels
    | .mk localWires items =>
        .mk localWires (items.renameWires (extendWireRenaming rho localWires))

  def Item.renameWires (rho : Fin source -> Fin target) :
      Item signature source rels -> Item signature target rels
    | .equation output term => .equation (rho output) (term.mapFree rho)
    | .atom relation arguments => .atom relation (rho ∘ arguments)
    | .named relation arguments => .named relation (rho ∘ arguments)
    | .cut body => .cut (body.renameWires rho)
    | .bubble arity body => .bubble arity (body.renameWires rho)

  def ItemSeq.renameWires (rho : Fin source -> Fin target) :
      ItemSeq signature source rels -> ItemSeq signature target rels
    | .nil => .nil
    | .cons item tail => .cons (item.renameWires rho) (tail.renameWires rho)
end

mutual
  def Region.renameRelations (rho : RelationRenaming source target) :
      Region signature wires source -> Region signature wires target
    | .mk localWires items => .mk localWires (items.renameRelations rho)

  def Item.renameRelations (rho : RelationRenaming source target) :
      Item signature wires source -> Item signature wires target
    | .equation output term => .equation output term
    | .atom relation arguments => .atom (rho relation) arguments
    | .named relation arguments => .named relation arguments
    | .cut body => .cut (body.renameRelations rho)
    | .bubble arity body =>
        .bubble arity (body.renameRelations (RelationRenaming.lift rho arity))

  def ItemSeq.renameRelations (rho : RelationRenaming source target) :
      ItemSeq signature wires source -> ItemSeq signature wires target
    | .nil => .nil
    | .cons item tail =>
        .cons (item.renameRelations rho) (tail.renameRelations rho)
end

theorem Region.renameWires_id (region : Region signature wires rels) :
    region.renameWires id = region := by
  apply Region.rec
    (motive_1 := fun _ _ region => region.renameWires id = region)
    (motive_2 := fun _ _ item => item.renameWires id = item)
    (motive_3 := fun _ _ items => items.renameWires id = items)
  · intro _ _ localWires items ih
    simp only [Region.renameWires, extendWireRenaming_id]
    exact congrArg (Region.mk localWires) ih
  · intro _ _ output term
    simp [Item.renameWires, Lambda.Term.mapFree_id]
  · intro _ _ _ relation arguments
    simp [Item.renameWires, Function.comp_def]
  · intro _ _ _ relation arguments
    simp [Item.renameWires, Function.comp_def]
  · intro _ _ body ih
    exact congrArg Item.cut ih
  · intro _ _ arity body ih
    exact congrArg (Item.bubble arity) ih
  · intro _ _
    rfl
  · intro _ _ item tail ihItem ihTail
    simp only [ItemSeq.renameWires]
    rw [ihItem, ihTail]

theorem Item.renameWires_id (item : Item signature wires rels) :
    item.renameWires id = item := by
  have h := Region.renameWires_id
    (Region.mk 0 (ItemSeq.cons item ItemSeq.nil))
  simp only [Region.renameWires, extendWireRenaming_id,
    ItemSeq.renameWires] at h
  have hseq : ItemSeq.cons (item.renameWires id) ItemSeq.nil =
      ItemSeq.cons item ItemSeq.nil := eq_of_heq (Region.mk.inj h).2
  exact (ItemSeq.cons.inj hseq).1

theorem ItemSeq.renameWires_id (items : ItemSeq signature wires rels) :
    items.renameWires id = items := by
  have h := Region.renameWires_id (Region.mk 0 items)
  simp only [Region.renameWires, extendWireRenaming_id] at h
  exact eq_of_heq (Region.mk.inj h).2

mutual
  theorem Region.renameWires_comp (region : Region signature source rels)
      (rho : Fin source -> Fin middle) (tau : Fin middle -> Fin target) :
      (region.renameWires rho).renameWires tau =
        region.renameWires (tau ∘ rho) := by
    cases region with
    | mk localWires items =>
        simp only [Region.renameWires]
        apply congrArg (Region.mk localWires)
        calc
          _ = items.renameWires
                (extendWireRenaming tau localWires ∘
                  extendWireRenaming rho localWires) :=
            ItemSeq.renameWires_comp items _ _
          _ = _ := congrArg (fun f => items.renameWires f)
            (extendWireRenaming_comp rho tau localWires)

  theorem Item.renameWires_comp (item : Item signature source rels)
      (rho : Fin source -> Fin middle) (tau : Fin middle -> Fin target) :
      (item.renameWires rho).renameWires tau =
        item.renameWires (tau ∘ rho) := by
    cases item with
    | equation output term =>
        simp [Item.renameWires, Lambda.Term.mapFree_comp, Function.comp_def]
    | atom relation arguments => rfl
    | named relation arguments => rfl
    | cut body =>
        exact congrArg Item.cut (Region.renameWires_comp body rho tau)
    | bubble arity body =>
        exact congrArg (Item.bubble arity)
          (Region.renameWires_comp body rho tau)

  theorem ItemSeq.renameWires_comp (items : ItemSeq signature source rels)
      (rho : Fin source -> Fin middle) (tau : Fin middle -> Fin target) :
      (items.renameWires rho).renameWires tau =
        items.renameWires (tau ∘ rho) := by
    cases items with
    | nil => rfl
    | cons item tail =>
        simp only [ItemSeq.renameWires]
        rw [Item.renameWires_comp, ItemSeq.renameWires_comp]
end

theorem Region.renameRelations_id (region : Region signature wires rels) :
    region.renameRelations (fun r => r) = region := by
  apply Region.rec
    (motive_1 := fun _ _ region =>
      region.renameRelations (fun r => r) = region)
    (motive_2 := fun _ _ item =>
      item.renameRelations (fun r => r) = item)
    (motive_3 := fun _ _ items =>
      items.renameRelations (fun r => r) = items)
  · intro _ _ localWires items ih
    exact congrArg (Region.mk localWires) ih
  · intro _ _ output term
    rfl
  · intro _ _ _ relation arguments
    rfl
  · intro _ _ _ relation arguments
    rfl
  · intro _ _ body ih
    exact congrArg Item.cut ih
  · intro _ _ arity body ih
    simp only [Item.renameRelations]
    rw [RelationRenaming.lift_id_fun]
    exact congrArg (Item.bubble arity) ih
  · intro _ _
    rfl
  · intro _ _ item tail ihItem ihTail
    simp only [ItemSeq.renameRelations]
    rw [ihItem, ihTail]

theorem Item.renameRelations_id (item : Item signature wires rels) :
    item.renameRelations (fun r => r) = item := by
  have h := Region.renameRelations_id
    (Region.mk 0 (ItemSeq.cons item ItemSeq.nil))
  simp only [Region.renameRelations, ItemSeq.renameRelations] at h
  have hseq : ItemSeq.cons (item.renameRelations (fun r => r)) ItemSeq.nil =
      ItemSeq.cons item ItemSeq.nil := eq_of_heq (Region.mk.inj h).2
  exact (ItemSeq.cons.inj hseq).1

theorem ItemSeq.renameRelations_id (items : ItemSeq signature wires rels) :
    items.renameRelations (fun r => r) = items := by
  have h := Region.renameRelations_id (Region.mk 0 items)
  simp only [Region.renameRelations] at h
  exact eq_of_heq (Region.mk.inj h).2

theorem Region.renameRelations_comp (region : Region signature wires source)
    (rho : RelationRenaming source middle)
    (tau : RelationRenaming middle target) :
    (region.renameRelations rho).renameRelations tau =
      region.renameRelations (fun r => tau (rho r)) := by
  apply Region.rec
    (motive_1 := fun _ rels region =>
      forall {middle target} (rho : RelationRenaming rels middle)
        (tau : RelationRenaming middle target),
        (region.renameRelations rho).renameRelations tau =
          region.renameRelations (fun r => tau (rho r)))
    (motive_2 := fun _ rels item =>
      forall {middle target} (rho : RelationRenaming rels middle)
        (tau : RelationRenaming middle target),
        (item.renameRelations rho).renameRelations tau =
          item.renameRelations (fun r => tau (rho r)))
    (motive_3 := fun _ rels items =>
      forall {middle target} (rho : RelationRenaming rels middle)
        (tau : RelationRenaming middle target),
        (items.renameRelations rho).renameRelations tau =
          items.renameRelations (fun r => tau (rho r)))
  · intro _ _ localWires items ih _ _ rho tau
    exact congrArg (Region.mk localWires) (ih rho tau)
  · intro _ _ output term _ _ rho tau
    rfl
  · intro _ _ _ relation arguments _ _ rho tau
    rfl
  · intro _ _ _ relation arguments _ _ rho tau
    rfl
  · intro _ _ body ih _ _ rho tau
    exact congrArg Item.cut (ih rho tau)
  · intro _ _ arity body ih _ _ rho tau
    simp only [Item.renameRelations]
    rw [ih (RelationRenaming.lift rho arity)
      (RelationRenaming.lift tau arity)]
    rw [RelationRenaming.lift_comp_fun]
  · intro _ _ _ _ rho tau
    rfl
  · intro _ _ item tail ihItem ihTail _ _ rho tau
    simp only [ItemSeq.renameRelations]
    rw [ihItem rho tau, ihTail rho tau]

theorem Item.renameRelations_comp (item : Item signature wires source)
    (rho : RelationRenaming source middle)
    (tau : RelationRenaming middle target) :
    (item.renameRelations rho).renameRelations tau =
      item.renameRelations (fun r => tau (rho r)) := by
  have h := Region.renameRelations_comp
    (Region.mk 0 (ItemSeq.cons item ItemSeq.nil)) rho tau
  simp only [Region.renameRelations, ItemSeq.renameRelations] at h
  have hseq := eq_of_heq (Region.mk.inj h).2
  exact (ItemSeq.cons.inj hseq).1

theorem ItemSeq.renameRelations_comp (items : ItemSeq signature wires source)
    (rho : RelationRenaming source middle)
    (tau : RelationRenaming middle target) :
    (items.renameRelations rho).renameRelations tau =
      items.renameRelations (fun r => tau (rho r)) := by
  have h := Region.renameRelations_comp (Region.mk 0 items) rho tau
  simp only [Region.renameRelations] at h
  exact eq_of_heq (Region.mk.inj h).2

def BoundaryAssignment.map (assignment : BoundaryAssignment d D)
    (f : D -> E) : BoundaryAssignment d E where
  args := f ∘ assignment.args
  classes := f ∘ assignment.classes
  agrees := fun i => congrArg f (assignment.agrees i)

theorem BoundaryAssignment.map_id (assignment : BoundaryAssignment d D) :
    assignment.map id = assignment := by
  cases assignment
  rfl

theorem BoundaryAssignment.map_comp (assignment : BoundaryAssignment d D)
    (f : D -> E) (g : E -> F) :
    (assignment.map f).map g = assignment.map (g ∘ f) := by
  cases assignment
  rfl

def OpenDiagram.identityBoundaryAssignment (d : OpenDiagram signature arity) :
    BoundaryAssignment d (Fin d.externalClasses) where
  args := d.boundary
  classes := id
  agrees := fun _ => rfl

def OpenDiagram.substituteBoundary (d : OpenDiagram signature arity)
    (assignment : BoundaryAssignment d (Fin wires)) :
    Region signature wires [] :=
  d.body.renameWires assignment.classes

theorem OpenDiagram.substituteBoundary_id (d : OpenDiagram signature arity) :
    d.substituteBoundary d.identityBoundaryAssignment = d.body := by
  exact Region.renameWires_id d.body

theorem OpenDiagram.substituteBoundary_comp
    (d : OpenDiagram signature arity)
    (assignment : BoundaryAssignment d (Fin source))
    (rho : Fin source -> Fin target) :
    (d.substituteBoundary assignment).renameWires rho =
      d.substituteBoundary (assignment.map rho) := by
  exact Region.renameWires_comp d.body assignment.classes rho

end VisualProof.Diagram
