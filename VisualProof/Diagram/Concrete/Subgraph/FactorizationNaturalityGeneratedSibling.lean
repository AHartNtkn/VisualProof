import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalityLocal

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

/--
The complete recursive receipt for a source sibling suffix that lies outside
the insertion path. Each constructor retains the source and generated body
compiler receipts for one child; the two suffix compiler equations and the
semantic transport are folds over this same value.
-/
inductive GeneratedOutsideChildrenProvenance
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceFuel targetFuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram) :
    List base.val.RegionId →
    ItemSeq definitions sourceContext.sigs →
    ItemSeq definitions targetContext.sigs →
    Prop where
  | nil :
      GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
        sourceContext targetContext [] .nil .nil
  | cons
      (child : base.val.RegionId)
      (tail : List base.val.RegionId)
      (childOutside : ¬base.val.Encloses child site)
      (childAbove :
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child))
      (sourceBody : Region definitions sourceContext.sigs)
      (targetBody : Region definitions targetContext.sigs)
      (sourceTail : ItemSeq definitions sourceContext.sigs)
      (targetTail : ItemSeq definitions targetContext.sigs)
      (sourceBodyCompiled :
        ConcreteElaboration.compileRegion? definitions base.val sourceFuel
            child sourceContext =
          some sourceBody)
      (targetBodyCompiled :
        ConcreteElaboration.compileRegion? definitions attachment.diagram
            targetFuel (attachment.hostRegion child) targetContext =
          some targetBody)
      (rest :
        GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
          sourceContext targetContext tail sourceTail targetTail) :
      GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
        sourceContext targetContext (child :: tail)
        (.cons (.cut sourceBody) sourceTail)
        (.cons (.cut targetBody) targetTail)

namespace GeneratedOutsideChildrenProvenance

/--
Construct the recursive suffix receipt from the accepted source compilation.
`generateHead` is the insertion owner's direct source-to-target construction
for one outside child; no target suffix compiler traversal occurs here.
-/
theorem generate
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    (generateHead :
      ∀ (child : base.val.RegionId)
        (_childOutside : ¬base.val.Encloses child site)
        (_childAbove :
          ConcreteElaboration.ContextAbove attachment.diagram targetContext
            (attachment.hostRegion child))
        (sourceBody : Region definitions sourceContext.sigs),
        ConcreteElaboration.compileRegion? definitions base.val sourceFuel
            child sourceContext =
          some sourceBody →
        ∃ targetBody : Region definitions targetContext.sigs,
          ConcreteElaboration.compileRegion? definitions attachment.diagram
              targetFuel (attachment.hostRegion child) targetContext =
            some targetBody) :
    ∀ (children : List base.val.RegionId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      (∀ child, child ∈ children →
        ¬base.val.Encloses child site) →
      (∀ child, child ∈ children →
        ConcreteElaboration.ContextAbove attachment.diagram targetContext
          (attachment.hostRegion child)) →
      ConcreteElaboration.compileChildrenWith? definitions base.val
          (ConcreteElaboration.compileRegion? definitions base.val sourceFuel)
          sourceContext children =
        some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
          sourceContext targetContext children sourceItems targetItems := by
  intro children
  induction children with
  | nil =>
      intro sourceItems outside above sourceCompiled
      have sourceExact : sourceItems = .nil :=
        (Option.some.inj sourceCompiled).symm
      subst sourceItems
      exact ⟨.nil, .nil⟩
  | cons child tail induction =>
      intro sourceItems outside above sourceCompiled
      obtain ⟨sourceHead, sourceTail, sourceHeadCompiled,
          sourceTailCompiled, sourceItemsShape⟩ :=
        compileChildren_cons_components definitions base.val
          (ConcreteElaboration.compileRegion? definitions base.val sourceFuel)
          sourceContext child tail sourceItems sourceCompiled
      subst sourceItems
      obtain ⟨targetHead, targetHeadCompiled⟩ :=
        generateHead child (outside child (by simp)) (above child (by simp))
          sourceHead sourceHeadCompiled
      obtain ⟨targetTail, rest⟩ :=
        induction
          (by
            intro candidate member
            exact outside candidate (by simp [member]))
          (by
            intro candidate member
            exact above candidate (by simp [member]))
          sourceTailCompiled
      exact
        ⟨.cons (.cut targetHead) targetTail,
          .cons child tail (outside child (by simp))
            (above child (by simp)) sourceHead targetHead sourceTail
            targetTail sourceHeadCompiled targetHeadCompiled rest⟩

/-- The source suffix equation is a fold over the recursive receipt. -/
theorem sourceGenerated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {children : List base.val.RegionId}
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    {targetItems : ItemSeq definitions targetContext.sigs}
    (provenance :
      GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
        sourceContext targetContext children sourceItems targetItems) :
    ConcreteElaboration.compileChildrenWith? definitions base.val
        (ConcreteElaboration.compileRegion? definitions base.val sourceFuel)
        sourceContext children =
      some sourceItems := by
  induction provenance with
  | nil => rfl
  | cons child tail childOutside childAbove sourceBody targetBody sourceTail targetTail
      sourceBodyCompiled targetBodyCompiled rest induction =>
      simp [ConcreteElaboration.compileChildrenWith?, sourceBodyCompiled,
        induction]

/-- The generated suffix equation is a fold over the recursive receipt. -/
theorem targetGenerated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    {compiled : InsertionCompilation fragmentCompiled attachment}
    {sourceFuel targetFuel : Nat}
    {sourceContext : ConcreteElaboration.WireContext base.val}
    {targetContext :
      ConcreteElaboration.WireContext attachment.diagram}
    {children : List base.val.RegionId}
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    {targetItems : ItemSeq definitions targetContext.sigs}
    (provenance :
      GeneratedOutsideChildrenProvenance compiled sourceFuel targetFuel
        sourceContext targetContext children sourceItems targetItems) :
    ConcreteElaboration.compileChildrenWith? definitions attachment.diagram
        (ConcreteElaboration.compileRegion? definitions attachment.diagram
          targetFuel)
        targetContext (children.map attachment.hostRegion) =
      some targetItems := by
  induction provenance with
  | nil => rfl
  | cons child tail childOutside childAbove sourceBody targetBody sourceTail targetTail
      sourceBodyCompiled targetBodyCompiled rest induction =>
      simp [ConcreteElaboration.compileChildrenWith?, targetBodyCompiled,
        induction]

end GeneratedOutsideChildrenProvenance

end NaturalityInternal
end InsertionCompilation
end VisualProof
