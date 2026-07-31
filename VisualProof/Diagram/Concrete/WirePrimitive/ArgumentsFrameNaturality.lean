import VisualProof.Diagram.Concrete.ElaborationTransport
import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport
import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsOperations

namespace VisualProof
namespace ConcreteWirePrimitive

open ConcreteElaboration
open ConcreteWireQuantifier

/-- Total carrier used by compiler contexts.  Its removed-wire branch is
unobservable: retained-context receipts prove every visible id takes the
canonical retained-image branch. -/
def ArgumentResult.contextWireMap
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId) : result.checked.val.WireId :=
  if retained : sourceWire ∉ result.sourceRemovedWires then
    result.retainedWireImage sourceWire retained
  else
    result.targetWire

theorem ArgumentResult.contextWireMap_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.contextWireMap sourceWire =
      result.retainedWireImage sourceWire retained := by
  unfold ArgumentResult.contextWireMap
  rw [dif_pos retained]

theorem ArgumentResult.contextWireMap_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires (result.contextWireMap sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [result.contextWireMap_retained sourceWire retained]
  exact result.retainedWireImage_signature sourceWire retained

/-- A wire local to a region not enclosed by the acted scope cannot be among
the localized replacement's removed wires. -/
theorem ArgumentResult.wireAt_not_below_not_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (region : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope region)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ source.val.wiresAt region) :
    sourceWire ∉ result.sourceRemovedWires := by
  intro removed
  rw [ConcreteDiagram.wiresAt, List.mem_filter] at member
  have localScope := eq_of_beq member.2
  apply notBelow
  rw [← localScope]
  exact localized.removed_enclosed sourceWire removed

/-- A wire local to a strict ancestor of a localized replacement cannot be
among the replacement's removed wires. -/
theorem ArgumentResult.wireAt_strictlyAbove_not_removed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ source.val.wiresAt outer) :
    sourceWire ∉ result.sourceRemovedWires := by
  apply result.wireAt_not_below_not_removed localized outer
  intro actedEnclosesOuter
  have same := factor_encloses_antisymm definitions source.val
    source.property outerEncloses actedEnclosesOuter
  exact strict same
  exact member

/-- Every incidence of a retained source node is reproduced on the
canonical target node and wire images. -/
theorem ArgumentResult.retainedNode_forwardIncident
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (node : source.val.NodeId)
    (nodeRetained : node ∉ argumentSiteNodes result.sites)
    (port : CPort)
    (sourceWire : source.val.WireId)
    (incident :
      (⟨node, port⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires sourceWire).endpoints) :
    (⟨result.retainedNodeImage node nodeRetained, port⟩ :
        CEndpoint result.checked.val.nodeCount) ∈
      (result.checked.val.wires
        (result.contextWireMap sourceWire)).endpoints := by
  have required := ConcreteDiagram.incident_port_required definitions
    source.val source.property sourceWire ⟨node, port⟩ incident
  have sourceOwner := ConcreteDiagram.endpointOwner?_eq_of_incident
    definitions source.val source.property node port required sourceWire
    incident
  have sourceWireRetained := result.ownerOfRetainedNode_not_removed node
    nodeRetained port sourceWire sourceOwner
  have targetOwner := result.retainedNodeImage_endpointOwner node
    nodeRetained port required sourceWire sourceOwner
  rw [result.contextWireMap_retained sourceWire sourceWireRetained]
  exact ConcreteDiagram.endpointOwner?_incident result.checked.val
    ⟨result.retainedNodeImage node nodeRetained, port⟩
    (result.retainedWireImage sourceWire sourceWireRetained) targetOwner

/-- At any region not enclosed by the acted scope, ordered local wire
identifiers are exactly the canonical images of the source identifiers. -/
theorem ArgumentResult.wiresAt_contextWireMap_not_below
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope outer) :
    result.checked.val.wiresAt (result.regionImage outer) =
      (source.val.wiresAt outer).map result.contextWireMap := by
  rw [result.wiresAt_decomposition outer]
  have retainedFilter :
      (source.val.wiresAt outer).filter
          (fun sourceWire =>
            decide (sourceWire ∉ result.sourceRemovedWires)) =
        source.val.wiresAt outer := by
    apply List.filter_eq_self.mpr
    intro sourceWire member
    exact decide_eq_true
      (result.wireAt_not_below_not_removed localized outer notBelow
        sourceWire member)
  have headEmpty :
      (Data.Finite.allFin 1).filter (fun _head =>
          retainedRegion source (source.val.wires wire).scope ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro _head _member accepted
    apply notBelow
    have same : (source.val.wires wire).scope = outer := by
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact eq_of_beq accepted
    exact same ▸ ConcreteDiagram.encloses_refl source.val _
  have localEmpty :
      (Data.Finite.allFin result.spec.localCount).filter (fun fresh =>
          retainedRegion source (result.spec.localScope fresh) ==
            retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _member accepted
    have localExact : result.spec.localScope fresh = outer := by
      apply (Internal.noRegionRemovalEquiv source).injective
      rw [← retainedRegion_eq_noRegionRemovalEquiv,
        ← retainedRegion_eq_noRegionRemovalEquiv]
      exact eq_of_beq accepted
    have actedEnclosesOuter :
        source.val.Encloses (source.val.wires wire).scope outer := by
      rw [← localExact]
      exact localized.local_enclosed fresh
    exact notBelow actedEnclosesOuter
  rw [headEmpty, localEmpty]
  simp only [List.map_nil, List.append_nil]
  have baseSources := batchRemovalCandidate_wiresAt_sources
    result.plan.removal outer
  rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
  change
    ((replacementBase result.plan).wiresAt
        (retainedRegion source outer)).map
          (Internal.sourceRetainedWire source result.sourceRemovedWires) =
      (source.val.wiresAt outer).filter
        (fun sourceWire =>
          decide (sourceWire ∉ result.sourceRemovedWires)) at baseSources
  rw [retainedFilter] at baseSources
  calc
    _ = ((replacementBase result.plan).wiresAt
          (retainedRegion source outer)).map (fun retained =>
            result.contextWireMap
              (Internal.sourceRetainedWire source
                result.sourceRemovedWires retained)) := by
        apply List.map_congr_left
        intro retained _member
        have sourceRetained :
            Internal.sourceRetainedWire source result.sourceRemovedWires
                retained ∉ result.sourceRemovedWires := by
          have member := List.get_mem
            (Internal.retainedWires source result.sourceRemovedWires) retained
          exact of_decide_eq_true (List.mem_filter.mp member).2
        rw [result.contextWireMap_retained _ sourceRetained]
        unfold ArgumentResult.retainedWireImage
        apply congrArg (Internal.checkedWire result.generated)
        exact congrArg (Fin.castAdd (1 + result.spec.localCount))
          (Internal.retainedWireIndex_sourceRetainedWire source
            result.sourceRemovedWires retained).symm
    _ = (((replacementBase result.plan).wiresAt
          (retainedRegion source outer)).map
            (Internal.sourceRetainedWire source
              result.sourceRemovedWires)).map result.contextWireMap := by
        rw [List.map_map]
        apply List.map_congr_left
        intro retained _member
        rfl
    _ = _ := by rw [baseSources]

/-- At a strict ancestor of the acted scope, ordered local wire identifiers
are exactly the canonical images of the source identifiers. -/
theorem ArgumentResult.wiresAt_contextWireMap_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    result.checked.val.wiresAt (result.regionImage outer) =
      (source.val.wiresAt outer).map result.contextWireMap := by
  apply result.wiresAt_contextWireMap_not_below localized outer
  intro actedEnclosesOuter
  have same := factor_encloses_antisymm definitions source.val
    source.property outerEncloses actedEnclosesOuter
  exact strict same

private def contextEmbeddingMapped
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (mapWire : source.WireId → target.WireId) :
    (sourceIds : List source.WireId) →
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig) →
    WireRenaming
      (sourceIds.map fun sourceWire => (source.wires sourceWire).sig)
      ((sourceIds.map mapWire).map fun targetWire =>
        (target.wires targetWire).sig)
  | [], _ => fun value => nomatch value
  | head :: tail, signature => fun value =>
      match value with
      | .here =>
          InsertionCompilation.NaturalityInternal.castVar
            (signature head (by simp)) .here
      | .there rest =>
          .there (contextEmbeddingMapped source target mapWire tail
            (fun wire member => signature wire
              (List.mem_cons_of_mem head member)) rest)

private def consSigsExact
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail) :
    leftHead :: leftTail = rightHead :: rightTail := by
  cases headExact
  cases tailExact
  rfl

private theorem cast_consSigsExact_here
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail) :
    consSigsExact headExact tailExact ▸
        (headExact ▸
          (Var.here : Var (leftHead :: leftTail) leftHead)) =
      (Var.here : Var (rightHead :: rightTail) rightHead) := by
  cases headExact
  cases tailExact
  rfl

private theorem cast_consSigsExact_there
    {leftHead rightHead : Sig}
    {leftTail rightTail : List Sig}
    (headExact : leftHead = rightHead)
    (tailExact : leftTail = rightTail)
    {sig : Sig}
    (value : Var leftTail sig) :
    consSigsExact headExact tailExact ▸
        (Var.there value : Var (leftHead :: leftTail) sig) =
      Var.there (tailExact ▸ value) := by
  cases headExact
  cases tailExact
  rfl

private theorem cast_symm_cast
    (same : source = target)
    (value : Var source sig) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem cast_cast_symm
    (same : source = target)
    (value : Var target sig) :
    same ▸ (same.symm ▸ value) = value := by
  cases same
  rfl

private theorem cast_trans_region
    {left middle right : List Sig}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (body : Region definitions left) :
    middleRight ▸ (leftMiddle ▸ body) =
      leftMiddle.trans middleRight ▸ body := by
  cases leftMiddle
  cases middleRight
  rfl

private def mappedContextSigsExact
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (mapWire : source.WireId → target.WireId) :
    (sourceIds : List source.WireId) →
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig) →
    (sourceIds.map mapWire).map (fun targetWire =>
        (target.wires targetWire).sig) =
      sourceIds.map fun sourceWire => (source.wires sourceWire).sig
  | [], _ => rfl
  | head :: tail, signature =>
      consSigsExact (signature head (by simp))
        (mappedContextSigsExact source target mapWire tail
          (fun wire member => signature wire
            (List.mem_cons_of_mem head member)))

private theorem contextEmbeddingMapped_origin
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (mapWire : source.WireId → target.WireId)
    (sourceIds : List source.WireId)
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig)
    {sig : Sig}
    (value : Var
      (sourceIds.map fun sourceWire => (source.wires sourceWire).sig) sig) :
    WireContext.origin target (sourceIds.map mapWire)
        (contextEmbeddingMapped source target mapWire sourceIds signature
          value) =
      mapWire (WireContext.origin source sourceIds value) := by
  induction sourceIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          simp only [contextEmbeddingMapped, WireContext.origin]
          exact InsertionCompilation.NaturalityInternal.origin_castVar
            target (mapWire head :: tail.map mapWire)
              (signature head (by simp)) .here
      | there rest =>
          exact induction
            (fun wire member => signature wire
              (List.mem_cons_of_mem head member)) rest

private theorem contextEmbeddingMapped_reindex_identity
    (source : ConcreteDiagram sourceCount)
    (target : ConcreteDiagram targetCount)
    (mapWire : source.WireId → target.WireId)
    (sourceIds : List source.WireId)
    (signature : ∀ wire, wire ∈ sourceIds →
      (target.wires (mapWire wire)).sig = (source.wires wire).sig) :
    (fun {sig} (value : Var
        (sourceIds.map fun sourceWire => (source.wires sourceWire).sig) sig) =>
      mappedContextSigsExact source target mapWire sourceIds signature ▸
        contextEmbeddingMapped source target mapWire sourceIds signature
          value) =
      (fun {_} value => value) := by
  funext sig value
  induction sourceIds with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          exact cast_consSigsExact_here
            (signature head (by simp))
            (mappedContextSigsExact source target mapWire tail
              (fun wire member => signature wire
                (List.mem_cons_of_mem head member)))
      | there rest =>
          simp only [contextEmbeddingMapped]
          change
            consSigsExact (signature head (by simp))
                (mappedContextSigsExact source target mapWire tail
                  (fun wire member => signature wire
                    (List.mem_cons_of_mem head member))) ▸
              (Var.there
                (contextEmbeddingMapped source target mapWire tail
                  (fun wire member => signature wire
                    (List.mem_cons_of_mem head member)) rest)) =
              Var.there rest
          rw [cast_consSigsExact_there
            (signature head (by simp))
            (mappedContextSigsExact source target mapWire tail
              (fun wire member => signature wire
                (List.mem_cons_of_mem head member)))]
          exact congrArg Var.there (induction
            (fun wire member => signature wire
              (List.mem_cons_of_mem head member)) rest)

private theorem Vars.rename_eq_of_pointwise
    (rho : WireRenaming context context)
    (pointwise : ∀ {signature : Sig} (value : Var context signature),
      rho value = value) :
    ∀ values : Vars context arguments, values.rename rho = values
  | .nil => rfl
  | .cons head tail => by
      simp only [Vars.rename]
      rw [pointwise head, Vars.rename_eq_of_pointwise rho pointwise tail]

mutual

private theorem Region.renameWires_eq_of_pointwise
    (rho : WireRenaming context context)
    (pointwise : ∀ {signature : Sig} (value : Var context signature),
      rho value = value) :
    ∀ body : Region definitions context, body.renameWires rho = body
  | .mk items => by
      exact congrArg Region.mk
        (ItemSeq.renameWires_eq_of_pointwise rho pointwise items)

private theorem Item.renameWires_eq_of_pointwise
    (rho : WireRenaming context context)
    (pointwise : ∀ {signature : Sig} (value : Var context signature),
      rho value = value) :
    ∀ item : Item definitions context, item.renameWires rho = item
  | .atom head arguments => by
      simp only [Item.renameWires]
      rw [pointwise head,
        Vars.rename_eq_of_pointwise rho pointwise arguments]
  | .named definition arguments => by
      simp only [Item.renameWires]
      rw [Vars.rename_eq_of_pointwise rho pointwise arguments]
  | .identity signature ports atLeastTwo => by
      simp only [Item.renameWires]
      have portsExact : ports.map (rho (sig := signature)) = ports := by
        calc
          ports.map (rho (sig := signature)) =
              ports.map (fun value => value) := by
            apply List.map_congr_left
            intro value _member
            exact pointwise value
          _ = ports := by simp
      simp [portsExact]
  | .cut body => by
      exact congrArg Item.cut
        (Region.renameWires_eq_of_pointwise rho pointwise body)
  | .bind signature body => by
      apply congrArg (Item.bind signature)
      apply Region.renameWires_eq_of_pointwise
      intro _ value
      cases value with
      | here => rfl
      | there outer =>
          exact congrArg Var.there (pointwise outer)

private theorem ItemSeq.renameWires_eq_of_pointwise
    (rho : WireRenaming context context)
    (pointwise : ∀ {signature : Sig} (value : Var context signature),
      rho value = value) :
    ∀ items : ItemSeq definitions context, items.renameWires rho = items
  | .nil => rfl
  | .cons head tail => by
      simp only [ItemSeq.renameWires]
      rw [Item.renameWires_eq_of_pointwise rho pointwise head,
        ItemSeq.renameWires_eq_of_pointwise rho pointwise tail]

end

private theorem ItemSeq.renameWires_reindex_identity
    (rho : WireRenaming source target)
    (same : target = source)
    (pointwise : ∀ {signature : Sig} (value : Var source signature),
      same ▸ rho value = value)
    (items : ItemSeq definitions source) :
    same ▸ items.renameWires rho = items := by
  cases same
  exact ItemSeq.renameWires_eq_of_pointwise rho pointwise items

/-- Context-local correspondence used above an argument replacement.  The
wire action is intentionally constrained only on the visible source ids:
arity replacement has no signature-preserving action on removed wires. -/
structure ArgumentResult.RetainedContext
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (sourceContext : WireContext source.val)
    (targetContext : WireContext result.checked.val) where
  source_retained :
    ∀ sourceWire, sourceWire ∈ sourceContext.ids →
      sourceWire ∉ result.sourceRemovedWires
  ids_exact :
    targetContext.ids = sourceContext.ids.map result.contextWireMap

namespace ArgumentResult.RetainedContext

/-- Empty root contexts correspond before the compiler descends through any
region. -/
def empty
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    result.RetainedContext (WireContext.empty source.val)
      (WireContext.empty result.checked.val) :=
  { ids_exact := rfl
    source_retained := by
      intro sourceWire member
      simp [WireContext.empty] at member }

theorem signature_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (sourceWire : source.val.WireId)
    (member : sourceWire ∈ sourceContext.ids) :
    (result.checked.val.wires (result.contextWireMap sourceWire)).sig =
      (source.val.wires sourceWire).sig :=
  result.contextWireMap_signature sourceWire
    (context.source_retained sourceWire member)

/-- Descending through any region not enclosed by the acted scope extends
both compiler contexts by corresponding ordered local-wire blocks. -/
def extendNotBelow
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope outer) :
    result.RetainedContext (sourceContext.extend outer)
      (targetContext.extend (result.regionImage outer)) :=
  { source_retained := by
      intro sourceWire member
      simp only [WireContext.extend, List.mem_append] at member
      rcases member with localMember | previous
      · exact result.wireAt_not_below_not_removed localized outer
          notBelow sourceWire localMember
      · exact context.source_retained sourceWire previous
    ids_exact := by
      unfold WireContext.extend
      rw [result.wiresAt_contextWireMap_not_below localized outer
        notBelow, context.ids_exact, List.map_append] }

/-- Descending through a strict ancestor extends both compiler contexts by
the corresponding ordered local-wire blocks. -/
def extendStrictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (localized : result.ScopeLocalization)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    result.RetainedContext (sourceContext.extend outer)
      (targetContext.extend (result.regionImage outer)) := by
  apply context.extendNotBelow localized outer
  intro actedEnclosesOuter
  have same := factor_encloses_antisymm definitions source.val
    source.property outerEncloses actedEnclosesOuter
  exact strict same

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

/-- The ordered local signature block is shared at every region not enclosed
by the acted scope. -/
theorem localSigs_exact_not_below
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    (localized : result.ScopeLocalization)
    (region : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope region) :
    (result.checked.val.wiresAt (result.regionImage region)).map
        (fun targetWire => (result.checked.val.wires targetWire).sig) =
      (source.val.wiresAt region).map
        (fun sourceWire => (source.val.wires sourceWire).sig) := by
  rw [result.wiresAt_contextWireMap_not_below localized region notBelow,
    List.map_map]
  apply List.map_congr_left
  intro sourceWire member
  exact result.contextWireMap_signature sourceWire
    (result.wireAt_not_below_not_removed localized region notBelow
      sourceWire member)

/-- Exact core equality survives discharge of the corresponding ordered local
signature blocks. -/
theorem finishRegion_reindexed_not_below
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (localized : result.ScopeLocalization)
    (region : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope region)
    (sourceCore : Region definitions (sourceContext.extend region).sigs)
    (targetCore : Region definitions
      (targetContext.extend (result.regionImage region)).sigs)
    (coreExact :
      (context.extendNotBelow localized region notBelow).sigs_exact ▸
          targetCore =
        sourceCore) :
    context.sigs_exact ▸
        ConcreteElaboration.finishRegion result.checked.val targetContext
          (result.regionImage region) targetCore =
      ConcreteElaboration.finishRegion source.val sourceContext region
        sourceCore := by
  rw [ConcreteElaboration.finishRegion_eq_signatures,
    ConcreteElaboration.finishRegion_eq_signatures]
  apply ConcreteElaboration.finishRegionSignatures_reindex
    context.sigs_exact
    (localSigs_exact_not_below (result := result) localized region notBelow)
  let targetExtend :=
    ConcreteElaboration.WireContext.sigs_extend targetContext
      (result.regionImage region)
  let sourceExtend :=
    ConcreteElaboration.WireContext.sigs_extend sourceContext region
  let blockExact :=
    targetExtend.trans
      ((ConcreteElaboration.appendSignaturesExact context.sigs_exact
        (localSigs_exact_not_below (result := result) localized region
          notBelow)).trans
        sourceExtend.symm)
  have extendedProofExact :
      (context.extendNotBelow localized region notBelow).sigs_exact =
        blockExact :=
    Subsingleton.elim _ _
  rw [extendedProofExact] at coreExact
  have transported := congrArg (fun body => sourceExtend ▸ body) coreExact
  rw [cast_trans_region targetExtend
    (ConcreteElaboration.appendSignaturesExact context.sigs_exact
      (localSigs_exact_not_below (result := result) localized region
        notBelow))]
  change sourceExtend ▸ (blockExact ▸ targetCore) =
    sourceExtend ▸ sourceCore at transported
  rw [cast_trans_region blockExact sourceExtend] at transported
  have proofExact :
      targetExtend.trans
          (ConcreteElaboration.appendSignaturesExact context.sigs_exact
            (localSigs_exact_not_below (result := result) localized region
              notBelow)) =
        blockExact.trans sourceExtend :=
    Subsingleton.elim _ _
  rw [proofExact]
  exact transported

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
  fun {_} value => context.sigs_exact.symm ▸ value

/-- Reindexing the exact mapped target signature vector back to the source
vector turns retained-context renaming into positional identity. -/
theorem wireRenaming_reindex_identity
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext) :
    (fun {sig} (value : Var sourceContext.sigs sig) =>
      context.sigs_exact ▸ context.wireRenaming value) =
      (fun {_} value => value) := by
  funext sig value
  unfold wireRenaming
  exact cast_cast_symm context.sigs_exact value

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
      result.contextWireMap
        (WireContext.origin source.val sourceContext.ids value) := by
  cases sourceContext with
  | mk sourceIds =>
      cases targetContext with
      | mk targetIds =>
          have idsExact := context.ids_exact
          dsimp only at idsExact
          subst targetIds
          have positional := contextEmbeddingMapped_origin source.val
            result.checked.val result.contextWireMap sourceIds
            context.signature_exact value
          have renamingExact :
              context.wireRenaming value =
                contextEmbeddingMapped source.val result.checked.val
                  result.contextWireMap sourceIds context.signature_exact
                  value := by
            unfold wireRenaming
            have mappedExact :=
              mappedContextSigsExact source.val result.checked.val
                result.contextWireMap sourceIds context.signature_exact
            have sourceExact := context.sigs_exact
            have same : sourceExact = mappedExact := Subsingleton.elim _ _
            have reindexed := congrFun
              (congrFun
                (contextEmbeddingMapped_reindex_identity source.val
                  result.checked.val result.contextWireMap sourceIds
                  context.signature_exact) sig) value
            have mappedProofSame :
                mappedContextSigsExact source.val result.checked.val
                    result.contextWireMap sourceIds
                    context.signature_exact = mappedExact :=
              Subsingleton.elim _ _
            rw [mappedProofSame] at reindexed
            have embeddedExact :
                contextEmbeddingMapped source.val result.checked.val
                    result.contextWireMap sourceIds context.signature_exact
                    value =
                  mappedExact.symm ▸ value := by
              calc
                _ = mappedExact.symm ▸
                      (mappedExact ▸
                        contextEmbeddingMapped source.val result.checked.val
                          result.contextWireMap sourceIds
                          context.signature_exact value) :=
                    (cast_symm_cast mappedExact _).symm
                _ = _ := congrArg
                  (fun mappedValue => mappedExact.symm ▸ mappedValue)
                  reindexed
            change context.sigs_exact.symm ▸ value = _
            rw [show context.sigs_exact = mappedExact from
              Subsingleton.elim _ _]
            exact embeddedExact.symm
          rw [renamingExact]
          exact positional

/-- One retained source node compiles to the renamed target item under
corresponding visible contexts. -/
theorem compileNode_natural
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    (sourceNode : source.val.NodeId)
    (nodeRetained : sourceNode ∉ argumentSiteNodes result.sites)
    (sourceItem : Item definitions sourceContext.sigs)
    (sourceCompiled :
      ConcreteElaboration.Internal.compileNode? definitions source.val
          sourceContext sourceNode = some sourceItem) :
    ConcreteElaboration.Internal.compileNode? definitions result.checked.val
        targetContext (result.retainedNodeImage sourceNode nodeRetained) =
      some (sourceItem.renameWires context.wireRenaming) := by
  exact ConcreteElaboration.compileNode?_natural
    (leftNode := sourceNode)
    (rightNode := result.retainedNodeImage sourceNode nodeRetained)
    result.checked.property targetNodup context.wireRenaming
    result.contextWireMap context.wireRenaming_origin result.regionEquiv
    (by
      rw [result.retainedNodeImage_data sourceNode nodeRetained]
      cases source.val.nodes sourceNode <;> rfl)
    (by
      intro port sourceWire incident
      exact result.retainedNode_forwardIncident sourceNode nodeRetained port
        sourceWire incident)
    sourceCompiled

/-- No rewritten application node is local to a region not enclosed by the
acted scope. -/
theorem nodeAt_not_below_not_siteNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope region)
    (node : source.val.NodeId)
    (nodeAt : node ∈ source.val.nodesAt region) :
    node ∉ argumentSiteNodes result.sites := by
  intro removed
  obtain ⟨site, _siteMember, siteExact⟩ := List.mem_map.mp removed
  have regionExact : site.region = region := by
    rw [ConcreteDiagram.nodesAt, List.mem_filter] at nodeAt
    have localExact := eq_of_beq nodeAt.2
    rw [← siteExact, site.node_data] at localExact
    exact localExact
  apply notBelow
  rw [← regionExact]
  exact site.head_visible

/-- No replacement site is local to a region not enclosed by the acted
scope. -/
theorem siteRegion_ne_not_below
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (region : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope region)
    (site : Fin result.sites.sites.length) :
    (result.sites.sites.get site).region ≠ region := by
  intro same
  apply notBelow
  rw [← same]
  exact (result.sites.sites.get site).head_visible

/-- Pointwise ordered correspondence between retained source nodes and their
canonical checked images. -/
inductive RetainedNodeList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire) :
    List source.val.NodeId → List result.checked.val.NodeId → Type
  | nil : RetainedNodeList result [] []
  | cons
      (sourceNode : source.val.NodeId)
      (retained : sourceNode ∉ argumentSiteNodes result.sites)
      (tail : RetainedNodeList result sourceTail targetTail) :
      RetainedNodeList result (sourceNode :: sourceTail)
        (result.retainedNodeImage sourceNode retained :: targetTail)

/-- Dense replacement-base node order induces the canonical ordered
retained-node correspondence. -/
noncomputable def RetainedNodeList.ofDense
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (dense : List (replacementBase result.plan).NodeId) :
    RetainedNodeList result
      (dense.map (Internal.sourceRetainedNode source
        (argumentSiteNodes result.sites)))
      (dense.map (fun retained =>
        Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length retained))) := by
  induction dense with
  | nil => exact .nil
  | cons retained tail induction =>
      simpa [result.retainedNodeImage_sourceRetainedNode retained] using
        RetainedNodeList.cons
          (Internal.sourceRetainedNode source
            (argumentSiteNodes result.sites) retained)
          (sourceRetainedNode_not_removed result.sites retained)
          induction

/-- At any region not enclosed by the acted scope, ordered local node
identifiers are exactly the retained source nodes and their canonical checked
images. -/
noncomputable def nodesAt_not_below
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer : source.val.RegionId)
    (notBelow :
      ¬source.val.Encloses (source.val.wires wire).scope outer) :
    RetainedNodeList result (source.val.nodesAt outer)
      (result.checked.val.nodesAt (result.regionImage outer)) := by
  let dense := (replacementBase result.plan).nodesAt
    (retainedRegion source outer)
  have correspondence := RetainedNodeList.ofDense result dense
  have sourceExact :
      dense.map (Internal.sourceRetainedNode source
        (argumentSiteNodes result.sites)) = source.val.nodesAt outer := by
    have baseSources := batchRemovalCandidate_nodesAt_sources
      result.plan.removal outer
    rw [← retainedRegion_eq_noRegionRemovalEquiv] at baseSources
    change dense.map (Internal.sourceRetainedNode source
      (argumentSiteNodes result.sites)) =
        (source.val.nodesAt outer).filter
          (fun node => decide
            (node ∉ argumentSiteNodes result.sites)) at baseSources
    rw [baseSources]
    apply List.filter_eq_self.mpr
    intro node member
    exact decide_eq_true
      (nodeAt_not_below_not_siteNode result outer notBelow node member)
  have generatedEmpty :
      (Data.Finite.allFin result.sites.sites.length).filter
          (fun site =>
            retainedRegion source (result.sites.sites.get site).region ==
              retainedRegion source outer) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro site _member accepted
    have same := eq_of_beq accepted
    apply siteRegion_ne_not_below result outer notBelow site
    apply (Internal.noRegionRemovalEquiv source).injective
    rw [← retainedRegion_eq_noRegionRemovalEquiv,
      ← retainedRegion_eq_noRegionRemovalEquiv]
    exact same
  have targetExact :
      result.checked.val.nodesAt (result.regionImage outer) =
        dense.map (fun retained =>
          Internal.checkedNode result.generated
            (Fin.castAdd result.sites.sites.length retained)) := by
    rw [result.nodesAt_decomposition outer, generatedEmpty]
    simp [dense]
  rw [sourceExact] at correspondence
  rw [targetExact]
  exact correspondence

/-- At a strict ancestor of the acted scope, ordered local node identifiers
are exactly the retained source nodes and their canonical checked images. -/
noncomputable def nodesAt_strictlyAbove
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ArgumentResult source wire)
    (outer : source.val.RegionId)
    (outerEncloses :
      source.val.Encloses outer (source.val.wires wire).scope)
    (strict : outer ≠ (source.val.wires wire).scope) :
    RetainedNodeList result (source.val.nodesAt outer)
      (result.checked.val.nodesAt (result.regionImage outer)) := by
  apply nodesAt_not_below result outer
  intro actedEnclosesOuter
  have same := factor_encloses_antisymm definitions source.val
    source.property outerEncloses actedEnclosesOuter
  exact strict same

/-- Ordered retained node sequences compile by pointwise renaming. -/
theorem compileNodes_natural
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sourceNodes : List source.val.NodeId}
    {targetNodes : List result.checked.val.NodeId}
    (nodes : RetainedNodeList result sourceNodes targetNodes)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      compileNodes? definitions source.val sourceContext sourceNodes =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      compileNodes? definitions result.checked.val targetContext targetNodes =
          some targetItems ∧
        targetItems = sourceItems.renameWires context.wireRenaming := by
  induction nodes generalizing sourceItems with
  | nil =>
      simp only [compileNodes?, Option.some.injEq] at sourceCompiled ⊢
      subst sourceItems
      exact ⟨.nil, rfl, rfl⟩
  | @cons sourceTail targetTail sourceNode retained tail induction =>
      simp only [compileNodes?] at sourceCompiled ⊢
      cases sourceHeadEquation :
          ConcreteElaboration.Internal.compileNode? definitions source.val
            sourceContext sourceNode with
      | none => simp [sourceHeadEquation] at sourceCompiled
      | some sourceHead =>
          cases sourceTailEquation :
              compileNodes? definitions source.val sourceContext sourceTail with
          | none => simp [sourceHeadEquation, sourceTailEquation] at sourceCompiled
          | some sourceRest =>
              have sourceItemsExact :
                  sourceItems = .cons sourceHead sourceRest := by
                exact (Option.some.inj (by
                  simpa [sourceHeadEquation, sourceTailEquation] using
                    sourceCompiled)).symm
              subst sourceItems
              have targetHeadEquation := context.compileNode_natural
                targetNodup sourceNode retained sourceHead sourceHeadEquation
              obtain ⟨targetRest, targetTailEquation, targetRestExact⟩ :=
                induction sourceTailEquation
              refine ⟨.cons (sourceHead.renameWires context.wireRenaming)
                targetRest, ?_, ?_⟩
              · simp [targetHeadEquation, targetTailEquation]
              · simp [ItemSeq.renameWires, targetRestExact]

/-- Ordered retained node compilation is literally shared after reindexing
the exact target signature vector back to the source vector. -/
theorem compileNodes_reindexed
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {result : ArgumentResult source wire}
    {sourceContext : WireContext source.val}
    {targetContext : WireContext result.checked.val}
    (context : result.RetainedContext sourceContext targetContext)
    (targetNodup : targetContext.ids.Nodup)
    {sourceNodes : List source.val.NodeId}
    {targetNodes : List result.checked.val.NodeId}
    (nodes : RetainedNodeList result sourceNodes targetNodes)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      compileNodes? definitions source.val sourceContext sourceNodes =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      compileNodes? definitions result.checked.val targetContext targetNodes =
          some targetItems ∧
        context.sigs_exact ▸ targetItems = sourceItems := by
  obtain ⟨targetItems, targetCompiled, targetExact⟩ :=
    context.compileNodes_natural targetNodup nodes sourceCompiled
  refine ⟨targetItems, targetCompiled, ?_⟩
  rw [targetExact]
  apply ItemSeq.renameWires_reindex_identity context.wireRenaming
    context.sigs_exact
  intro _ value
  exact congrFun
    (congrFun context.wireRenaming_reindex_identity _) value

end ArgumentResult.RetainedContext

end ConcreteWirePrimitive
end VisualProof
