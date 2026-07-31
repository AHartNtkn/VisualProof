import VisualProof.Diagram.Concrete.ElaborationTransport
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsOperations

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteElaboration

private def contextEmbeddingVisible
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount) :
    (sourceIds : List source.WireId) →
    (targetIds : List target.WireId) →
    (mapWire : source.WireId → target.WireId) →
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig) →
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds) →
    WireRenaming
      (sourceIds.map fun wire => (source.wires wire).sig)
      (targetIds.map fun wire => (target.wires wire).sig)
  | [], _, _, _, _ => fun value => nomatch value
  | head :: tail, targetIds, mapWire, signature, visible =>
      fun value =>
        match value with
        | .here =>
            InsertionCompilation.NaturalityInternal.castVar
              (signature head (by simp))
              (InsertionCompilation.NaturalityInternal.varForMember target
                targetIds (mapWire head) (visible head (by simp)))
        | .there rest =>
            contextEmbeddingVisible source target tail targetIds mapWire
              (fun wire member => signature wire
                (List.mem_cons_of_mem head member))
              (fun wire member => visible wire
                (List.mem_cons_of_mem head member)) rest

private theorem contextEmbeddingVisible_origin
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (sourceIds : List source.WireId)
    (targetIds : List target.WireId)
    (mapWire : source.WireId → target.WireId)
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig)
    (visible : ∀ wire, wire ∈ sourceIds → mapWire wire ∈ targetIds)
    {sig : Sig}
    (value : Var (sourceIds.map fun wire => (source.wires wire).sig) sig) :
    WireContext.origin target targetIds
        (contextEmbeddingVisible source target sourceIds targetIds mapWire
          signature visible value) =
      mapWire (WireContext.origin source sourceIds value) := by
  induction sourceIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          unfold contextEmbeddingVisible
          change
            WireContext.origin target targetIds
                (InsertionCompilation.NaturalityInternal.castVar
                  (signature head (by simp))
                  (InsertionCompilation.NaturalityInternal.varForMember target
                    targetIds (mapWire head) (visible head (by simp)))) =
              mapWire head
          rw [InsertionCompilation.NaturalityInternal.origin_castVar,
            InsertionCompilation.NaturalityInternal.varForMember_origin]
      | there rest =>
          exact induction
            (fun wire member => signature wire
              (List.mem_cons_of_mem head member))
            (fun wire member => visible wire
              (List.mem_cons_of_mem head member)) rest

/-- Context-local correspondence used above an argument replacement.  The
wire action is intentionally constrained only on the visible source ids:
arity replacement has no signature-preserving action on removed wires. -/
structure ArgumentResult.RetainedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceContext : WireContext source.val)
    (targetContext : WireContext result.checked.val) where
  wireMap : source.val.WireId → result.checked.val.WireId
  ids_exact : targetContext.ids = sourceContext.ids.map wireMap
  signature_exact :
    ∀ sourceWire, sourceWire ∈ sourceContext.ids →
      (result.checked.val.wires (wireMap sourceWire)).sig =
        (source.val.wires sourceWire).sig

namespace ArgumentResult.RetainedContext

/-- Corresponding visible contexts have definitionally ordered equal
signature lists, even though their concrete wire identifiers differ. -/
theorem sigs_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext) :
    targetContext.sigs = sourceContext.sigs := by
  unfold WireContext.sigs
  rw [context.ids_exact, List.map_map]
  apply List.map_congr_left
  intro sourceWire member
  exact context.signature_exact sourceWire member

/-- Rename typed variables from a source visible context to its retained
target context. -/
def wireRenaming
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  contextEmbeddingVisible source.val result.checked.val sourceContext.ids
    targetContext.ids context.wireMap context.signature_exact (by
      intro sourceWire member
      rw [context.ids_exact]
      exact List.mem_map.mpr ⟨sourceWire, member, rfl⟩)

/-- The retained-context renaming acts on concrete origins by the recorded
wire map. -/
theorem wireRenaming_origin
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    WireContext.origin result.checked.val targetContext.ids
        (context.wireRenaming value) =
      context.wireMap
        (WireContext.origin source.val sourceContext.ids value) := by
  exact contextEmbeddingVisible_origin source.val result.checked.val
    sourceContext.ids targetContext.ids context.wireMap
    context.signature_exact (by
      intro sourceWire member
      rw [context.ids_exact]
      exact List.mem_map.mpr ⟨sourceWire, member, rfl⟩) value

end ArgumentResult.RetainedContext

end ConcreteWirePrimitive
end VisualProof
