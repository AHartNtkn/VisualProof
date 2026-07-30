import VisualProof.Diagram.Concrete.Subgraph.Factorization
import VisualProof.Diagram.ContextOuter

namespace VisualProof

theorem DiagramContext.liftOuter_bindContextFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    DiagramContext.liftOuter
        (bindContextFor diagram outerIds localIds inner) value =
      DiagramContext.liftOuter inner
        (ConcreteElaboration.appendRightVar diagram localIds value) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.liftOuter,
        ConcreteElaboration.appendRightVar] using
        induction
          (.bind (diagram.wires head).sig inner)

theorem DiagramContext.preservesOuter_bindContextFor
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (region : diagram.RegionId)
    (inner : DiagramContext definitions holeCtx
      (context.extend region).sigs)
    (pre : PreModel)
    (values : ConcreteElaboration.WireValues pre
      ((diagram.wiresAt region).map fun wire =>
        (diagram.wires wire).sig))
    (fixed : Env pre context.sigs)
    (descendant : Env pre holeCtx)
    (preserves :
      DiagramContext.PreservesOuter inner
        (ConcreteElaboration.extendEnvironment diagram context region
          values fixed)
        descendant) :
    DiagramContext.PreservesOuter
      (bindContextFor diagram context.ids (diagram.wiresAt region) inner)
      fixed descendant := by
  unfold DiagramContext.PreservesOuter at preserves ⊢
  funext sig
  funext value
  change
    descendant sig
        (DiagramContext.liftOuter
          (bindContextFor diagram context.ids
            (diagram.wiresAt region) inner) value) =
      fixed sig value
  rw [DiagramContext.liftOuter_bindContextFor]
  calc
    descendant sig
        (DiagramContext.liftOuter inner
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value)) =
      ConcreteElaboration.extendEnvironment diagram context region values
          fixed sig
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value) := by
        exact congrFun (congrFun preserves sig)
          (ConcreteElaboration.appendRightVar diagram
            (diagram.wiresAt region) value)
    _ = fixed sig value :=
      ConcreteElaboration.extendEnvironment_appendRightVar diagram context
        region values fixed value

/-- Binding a fixed ordered local-wire prefix preserves the inner context exactly. -/
theorem bindContextFor_injective
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId) :
    Function.Injective
      (bindContextFor (definitions := definitions) diagram outerIds
        localIds :
        DiagramContext definitions holeCtx
            ((localIds ++ outerIds).map fun wire =>
              (diagram.wires wire).sig) →
          DiagramContext definitions holeCtx
            (outerIds.map fun wire => (diagram.wires wire).sig)) := by
  induction localIds with
  | nil =>
      intro left right same
      exact same
  | cons head tail induction =>
      intro left right same
      have boundSame := induction same
      injection boundSame

/-- Transformation-neutral paired contexts immediately inside two frame binders. -/
structure RegionFrame.PairedInner
    {definitions : List (List Sig)}
    {sourceDiagram targetDiagram : ConcreteDiagram definitions.length}
    (sourceRegion : sourceDiagram.RegionId)
    (targetRegion : targetDiagram.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext sourceDiagram)
    (targetOuter : ConcreteElaboration.WireContext targetDiagram)
    (sourceFrame : RegionFrame definitions sourceDiagram sourceOuter)
    (targetFrame : RegionFrame definitions targetDiagram targetOuter) where
  sourceInner :
    DiagramContext definitions sourceFrame.visible.sigs
      (sourceOuter.extend sourceRegion).sigs
  targetInner :
    DiagramContext definitions targetFrame.visible.sigs
      (targetOuter.extend targetRegion).sigs
  sourceDecomposition :
    sourceFrame.context =
      bindContextFor sourceDiagram sourceOuter.ids
        (sourceDiagram.wiresAt sourceRegion) sourceInner
  targetDecomposition :
    targetFrame.context =
      bindContextFor targetDiagram targetOuter.ids
        (targetDiagram.wiresAt targetRegion) targetInner

theorem siblingFrame_visible
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (selected : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      {frame : RegionFrame definitions diagram outer},
      compileSiblingFrame? definitions diagram fuel outer selected nested
          leading children =
        some frame →
      frame.visible = nested.visible := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame compiled
      simp [compileSiblingFrame?] at compiled
  | cons child tail induction =>
      intro frame compiled
      unfold compileSiblingFrame? at compiled
      by_cases same : child = selected
      · simp only [same, ↓reduceDIte] at compiled
        obtain ⟨suffix, suffixCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp compiled
        exact
          (congrArg RegionFrame.visible
            (Option.some.inj frameEquation)).symm
      · simp only [same, ↓reduceDIte] at compiled
        obtain ⟨body, bodyCompiled, recursive⟩ :=
          Option.bind_eq_some_iff.mp compiled
        exact induction
          (leading.append (.cons (.cut body) .nil)) recursive

end VisualProof
