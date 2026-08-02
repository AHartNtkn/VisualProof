import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawOriginFacts

namespace VisualProof

namespace MonolithicWireQuantifier

open ConcreteWireQuantifier

section RawRegionTraceData

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

/-- A data-bearing ordered spine of checked relation-join steps.  It is
separate from the proposition that certifies those steps form a semantic
trace, so nil/snoc shape remains available to proof inversion. -/
inductive RelationJoinSnocSteps : Type
  | nil
  | snoc (prior : RelationJoinSnocSteps)
      (step : RelationJoinStep source dying content)

namespace RelationJoinSnocSteps

def toList : RelationJoinSnocSteps (source := source) (dying := dying)
    (content := content) → List (RelationJoinStep source dying content)
  | .nil => []
  | .snoc prior step => prior.toList ++ [step]

def ofList (steps : List (RelationJoinStep source dying content)) :
    RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content) :=
  steps.foldl (fun prior step => .snoc prior step) .nil

private theorem toList_foldl
    (prior : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content))
    (steps : List (RelationJoinStep source dying content)) :
    (steps.foldl (fun prior step => .snoc prior step) prior).toList =
      prior.toList ++ steps := by
  induction steps generalizing prior with
  | nil => simp
  | cons step remaining induction =>
      simp only [List.foldl]
      rw [induction]
      simp only [toList, List.append_assoc, List.singleton_append]

/-- The spine conversion is a purely structural representation change. -/
theorem toList_ofList
    (steps : List (RelationJoinStep source dying content)) :
    (ofList steps).toList = steps := by
  simpa [ofList] using toList_foldl
    (.nil : RelationJoinSnocSteps (source := source) (dying := dying)
      (content := content)) steps

/-- Appending a last construction step extends the data spine by exactly one
visible snoc. -/
theorem ofList_append_singleton
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content) :
    ofList (steps ++ [step]) = .snoc (ofList steps) step := by
  simp only [ofList, List.foldl_append, List.foldl_cons, List.foldl_nil]

end RelationJoinSnocSteps

end RawRegionTraceData

end MonolithicWireQuantifier

end VisualProof
