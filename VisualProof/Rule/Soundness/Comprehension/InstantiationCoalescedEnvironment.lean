import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceRegion

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The canonical valuation of an attachment-quotient class, obtained from
its certified representative in the retained frame. -/
noncomputable def quotientFrameValue
    (input : Splice.Input signature)
    (frameValue : Fin input.frame.val.wireCount → D) :
    input.wireQuotient.Carrier → D :=
  frameValue ∘ input.wireQuotient.origin

/-- A frame valuation that is constant on attachment classes factors through
the executor's exact wire quotient. -/
theorem quotientFrameValue_quotientWire
    (input : Splice.Input signature)
    (frameValue : Fin input.frame.val.wireCount → D)
    (constant : ∀ {left right},
      input.quotientWire left = input.quotientWire right →
        frameValue left = frameValue right)
    (wire : Fin input.frame.val.wireCount) :
    quotientFrameValue input frameValue (input.quotientWire wire) =
      frameValue wire := by
  unfold quotientFrameValue
  exact constant
    (input.quotientWire_wireQuotient_origin (input.quotientWire wire))

/-- Denotation of the inserted comprehension is exactly the semantic
certificate making the retained-frame valuation factor through every wire
coalescence performed by the splice input. -/
theorem quotientFrameValue_quotientWire_of_pattern_denotes
    (input : Splice.Input signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (frameValue : Fin input.frame.val.wireCount → model.Carrier)
    (args : Fin input.pattern.val.boundary.length → model.Carrier)
    (realizes : ∀ position,
      frameValue (input.attachment position) = args position)
    (denotes : input.pattern.denote model named args)
    (wire : Fin input.frame.val.wireCount) :
    quotientFrameValue input frameValue (input.quotientWire wire) =
      frameValue wire := by
  apply quotientFrameValue_quotientWire input frameValue
  intro left right sameClass
  exact input.quotientWire_value_eq_of_pattern_denotes model named frameValue
    args realizes denotes sameClass

/-- Function-level form of `quotientFrameValue_quotientWire_of_pattern_denotes`.
It preserves all original wire positions, including repeated ordered aliases. -/
theorem quotientFrameValue_comp_quotientWire_of_pattern_denotes
    (input : Splice.Input signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (frameValue : Fin input.frame.val.wireCount → model.Carrier)
    (args : Fin input.pattern.val.boundary.length → model.Carrier)
    (realizes : ∀ position,
      frameValue (input.attachment position) = args position)
    (denotes : input.pattern.denote model named args) :
    quotientFrameValue input frameValue ∘ input.quotientWire = frameValue := by
  funext wire
  exact quotientFrameValue_quotientWire_of_pattern_denotes input model named
    frameValue args realizes denotes wire

/-- A concrete boundary assignment already contains all alias equalities
needed by the attachment quotient; denotation of the pattern body is not
needed for this narrower conclusion. -/
theorem quotientWire_value_eq_of_boundaryAssignment
    (input : Splice.Input signature)
    (frameValue : Fin input.frame.val.wireCount → D)
    (assignment : BoundaryAssignment input.pattern.elaborate D)
    (realizes : ∀ position,
      frameValue (input.attachment position) = assignment.args position)
    {left right : Fin input.frame.val.wireCount}
    (sameClass : input.quotientWire left = input.quotientWire right) :
    frameValue left = frameValue right := by
  have aliasConsistent : AliasConsistent input.pattern.elaborate
      assignment.args :=
    (boundaryAssignment_iff_aliasConsistent input.pattern.elaborate
      assignment.args).mp ⟨assignment, rfl⟩
  have contains : ∀ edge ∈ input.attachmentEdges,
      frameValue edge.1 = frameValue edge.2 := by
    intro edge member
    obtain ⟨leftPosition, rightPosition, boundaryEq, rfl⟩ :=
      (input.mem_attachmentEdges_iff edge).mp member
    have classEq : input.pattern.elaborate.boundary leftPosition =
        input.pattern.elaborate.boundary rightPosition := by
      change input.pattern.val.boundaryClass leftPosition =
        input.pattern.val.boundaryClass rightPosition
      exact (input.pattern.val.boundaryClass_eq_iff
        leftPosition rightPosition).2 boundaryEq
    calc
      frameValue (input.attachment leftPosition) =
          assignment.args leftPosition := realizes leftPosition
      _ = assignment.args rightPosition :=
        aliasConsistent leftPosition rightPosition classEq
      _ = frameValue (input.attachment rightPosition) :=
        (realizes rightPosition).symm
  apply VisualProof.Data.Finite.FinitePartition.least
    (relation := fun first second => frameValue first = frameValue second)
    (fun _ => rfl) (fun equality => equality.symm)
    (fun firstSecond secondThird => firstSecond.trans secondThird) contains
  exact (input.quotientWire_eq_iff left right).mp sameClass

end InstantiationSemantic

end VisualProof.Rule
