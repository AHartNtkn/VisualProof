import VisualProof.Refinement.Implementation.IterationExtractionRegionContext
import VisualProof.Refinement.Implementation.IterationExtractionRegionLocal

namespace VisualProof.Refinement.Implementation.IterationExtraction

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

theorem extractionCompileNode_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (membership : ∀ wire,
      input.val.fragmentWireOrigin selection layout wire ∈ hostContext ↔
        wire ∈ fragmentContext)
    (hostNodup : hostContext.Nodup)
    {fragmentRels hostRels : RelCtx}
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
    (relationMap : RelationRenaming fragmentRels hostRels)
    (node : Fin layout.nodeCount)
    (bindersRelated : ∀ region binder arity
      (fragmentRelation : RelVar fragmentRels arity),
      (input.val.extractDiagramRaw selection layout).nodes node =
          .atom region binder →
      fragmentBinders binder = some ⟨arity, fragmentRelation⟩ →
      hostBinders (extractionBinderOrigin input selection layout binder) =
        some ⟨arity, relationMap fragmentRelation⟩)
    (fragmentItem : Item fragmentContext.length fragmentRels)
    (hostItem : Item hostContext.length hostRels)
    (fragmentCompiled : Concrete.Elaboration.compileNode?
      (input.val.extractDiagramRaw selection layout) fragmentContext
      fragmentBinders node = some fragmentItem)
    (hostCompiled : Concrete.Elaboration.compileNode? input.val hostContext
      hostBinders (selection.selectedNodes.get node) = some hostItem) :
    ItemIso (FiniteEquiv.refl (Fin hostContext.length)) hostRels hostItem
      ((fragmentItem.renameRelations relationMap).renameWires
        (extractionContextIndexMapOfMembership input selection layout
          fragmentContext hostContext membership)) := by
  let wireMap := extractionContextIndexMapOfMembership input selection layout
    fragmentContext hostContext membership
  have bindersMap : ∀ region binder,
      (input.val.extractDiagramRaw selection layout).nodes node =
          .atom region binder →
      hostBinders (extractionBinderOrigin input selection layout binder) =
        (fragmentBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩ := by
    intro region binder nodeEq
    cases relationEq : fragmentBinders binder with
    | none =>
        have impossible := fragmentCompiled
        unfold Concrete.Elaboration.compileNode? at impossible
        rw [nodeEq] at impossible
        simp [relationEq] at impossible
    | some relation =>
        rcases relation with ⟨arity, relation⟩
        simpa using bindersRelated region binder arity relation nodeEq relationEq
  have mapped := Concrete.Elaboration.compileNode?_map
    fragmentContext hostContext fragmentBinders hostBinders node
    (selection.selectedNodes.get node)
    (extractionRegionOrigin input selection layout)
    (extractionBinderOrigin input selection layout) wireMap relationMap
    (by
      have shape := extractionNode_shape input selection layout node
      rw [Concrete.Diagram.extractDiagramRaw_node] at shape
      cases nodeEq : (input.val.extractDiagramRaw selection layout).nodes node <;>
        rw [Concrete.Diagram.extractDiagramRaw_node] at nodeEq <;>
        rw [nodeEq] at shape <;> exact shape)
    (extractionResolvePort_mapOfMembership input selection layout
      fragmentContext hostContext membership hostNodup node)
    bindersMap
  rw [fragmentCompiled, hostCompiled] at mapped
  have itemEq : hostItem =
      (fragmentItem.renameWires wireMap).renameRelations relationMap := by
    exact Option.some.inj mapped
  rw [itemEq, Item.renameWires_renameRelations]
  exact ItemIso.refl _

end VisualProof.Refinement.Implementation.IterationExtraction
