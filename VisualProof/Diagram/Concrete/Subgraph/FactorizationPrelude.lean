import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof.FactorizationInternal

/-- Preserve an index while mapping a list. -/
def mappedIndex
    (map : α → β) (values : List α) :
    Fin values.length → Fin (values.map map).length :=
  fun index => ⟨index.val, by simp⟩

theorem indexOf?_map_injective
    [DecidableEq α] [DecidableEq β]
    (map : α → β) (injective : Function.Injective map)
    (values : List α) (value : α) :
    Data.Finite.indexOf? (values.map map) (map value) =
      (Data.Finite.indexOf? values value).map
        (mappedIndex map values) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases same : value = head
      · subst value
        simp [Data.Finite.indexOf?, mappedIndex]
      · have mappedDifferent : map value ≠ map head :=
          fun mappedSame => same (injective mappedSame)
        simp only [List.map_cons, Data.Finite.indexOf?, same,
          mappedDifferent, ↓reduceIte, induction, Option.map_map]
        apply Option.map_congr
        intro index
        intro _
        apply Fin.ext
        rfl

theorem denseIndex_map_injective
    [DecidableEq α] [DecidableEq β]
    (map : α → β) (injective : Function.Injective map)
    (values : List α) (value : α) (member : value ∈ values) :
    DenseList.index (values.map map) (map value)
        (List.mem_map.mpr ⟨value, member, rfl⟩) =
      mappedIndex map values (DenseList.index values value member) := by
  obtain ⟨sourceIndex, sourceEquation⟩ :=
    Data.Finite.indexOf?_complete member
  have mappedEquation :
      Data.Finite.indexOf? (values.map map) (map value) =
        some (mappedIndex map values sourceIndex) := by
    rw [indexOf?_map_injective map injective, sourceEquation]
    rfl
  unfold DenseList.index
  apply Fin.ext
  rw [Option.get_of_eq_some _ mappedEquation,
    Option.get_of_eq_some _ sourceEquation]

theorem denseIndex_val_of_list_eq
    [DecidableEq α]
    {left right : List α} (same : left = right)
    (value : α) (leftMember : value ∈ left)
    (rightMember : value ∈ right) :
    (DenseList.index left value leftMember).val =
      (DenseList.index right value rightMember).val := by
  subst right
  rfl

/-- Cast only the signature index of a visible variable. -/
def castVisibleVar
    (equality : sourceSig = targetSig)
    (value : Var ctx sourceSig) :
    Var ctx targetSig :=
  equality ▸ value

theorem visibleOrigin_cast
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId}
    (value : Var
      (ids.map fun id => (diagram.wires id).sig) sourceSig)
    (equality : sourceSig = targetSig) :
    ConcreteElaboration.WireContext.origin diagram ids
        (castVisibleVar equality value) =
      ConcreteElaboration.WireContext.origin diagram ids value := by
  cases equality
  rfl

theorem packed_castVisibleVar
    (value : Var ctx sourceSig)
    (equality : sourceSig = targetSig) :
    (⟨sourceSig, value⟩ : PackedVar ctx) =
      ⟨targetSig, castVisibleVar equality value⟩ := by
  cases equality
  rfl

end VisualProof.FactorizationInternal
