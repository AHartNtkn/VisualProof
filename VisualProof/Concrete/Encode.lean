import VisualProof.Concrete.Translate
import VisualProof.Concrete.State
import VisualProof.Diagram.OpenIsomorphism

namespace VisualProof.Concrete

open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace Encoding

structure Counts where
  regions : Nat
  nodes : Nat
  wires : Nat

def Counts.add (left right : Counts) : Counts where
  regions := left.regions + right.regions
  nodes := left.nodes + right.nodes
  wires := left.wires + right.wires

mutual
  def regionCounts : Region wires rels → Counts
    | .mk localWires items =>
        let nested := itemSeqCounts items
        { regions := nested.regions + 1
          nodes := nested.nodes
          wires := localWires + nested.wires }

  def itemCounts : Item wires rels → Counts
    | .atom _ _ => { regions := 0, nodes := 1, wires := 0 }
    | .identity _ _ => { regions := 0, nodes := 1, wires := 0 }
    | .cut body => regionCounts body
    | .bubble _ body => regionCounts body

  def itemSeqCounts : ItemSeq wires rels → Counts
    | .nil => { regions := 0, nodes := 0, wires := 0 }
    | .cons head tail => (itemCounts head).add (itemSeqCounts tail)
end

inductive RegionDraft
  | sheet
  | cut (parent : Nat)
  | bubble (parent arity : Nat)

inductive NodeDraft
  | atom (region binder arity : Nat) (arguments : Fin arity → Nat)
  | identity (region arity : Nat) (arguments : Fin arity → Nat)

structure Flat where
  regions : List RegionDraft
  nodes : List NodeDraft
  wireScopes : List Nat

def Flat.empty : Flat := ⟨[], [], []⟩

def Flat.append (left right : Flat) : Flat where
  regions := left.regions ++ right.regions
  nodes := left.nodes ++ right.nodes
  wireScopes := left.wireScopes ++ right.wireScopes

abbrev WireMap (arity : Nat) := Fin arity → Nat

def WireMap.extend (outer : WireMap outerCount)
    (localBase localCount : Nat) : WireMap (outerCount + localCount) :=
  Fin.addCases outer (fun localIndex => localBase + localIndex.val)

abbrev BinderMap (rels : RelCtx) :=
  ∀ arity, RelVar rels arity → Nat

def BinderMap.empty : BinderMap [] := by
  intro arity relation
  exact Fin.elim0 relation.index

def BinderMap.push (outer : BinderMap rels)
    (binder : Nat) : BinderMap (arity :: rels) := by
  intro relationArity relation
  rcases relation with ⟨index, hasArity⟩
  induction index using Fin.cases with
  | zero => exact binder
  | succ tailIndex =>
      exact outer relationArity {
        index := tailIndex
        hasArity := by simpa using hasArity
      }

mutual
  def flattenRegion
      (regionKind : RegionDraft)
      (regionBase nodeBase wireBase : Nat)
      (outerWires : WireMap outerCount)
      (binders : BinderMap rels) :
      Region outerCount rels → Flat
    | .mk localWires items =>
        let currentWires := outerWires.extend wireBase localWires
        let nested := flattenItems regionBase (regionBase + 1)
          nodeBase (wireBase + localWires) currentWires binders items
        { regions := regionKind :: nested.regions
          nodes := nested.nodes
          wireScopes := List.replicate localWires regionBase ++
            nested.wireScopes }

  def flattenItems
      (currentRegion regionBase nodeBase wireBase : Nat)
      (wires : WireMap wireCount)
      (binders : BinderMap rels) :
      ItemSeq wireCount rels → Flat
    | .nil => Flat.empty
    | .cons head tail =>
        let headFlat : Flat :=
          match head with
          | .atom relation arguments =>
              { regions := []
                nodes := [.atom currentRegion (binders _ relation)
                  _ (wires ∘ arguments)]
                wireScopes := [] }
          | .identity arity arguments =>
              { regions := []
                nodes := [.identity currentRegion arity
                  (wires ∘ arguments)]
                wireScopes := [] }
          | .cut body =>
              flattenRegion (.cut currentRegion) regionBase nodeBase wireBase
                wires binders body
          | .bubble arity body =>
              flattenRegion (.bubble currentRegion arity) regionBase nodeBase
                wireBase wires (binders.push regionBase) body
        let counts := itemCounts head
        headFlat.append (flattenItems currentRegion
          (regionBase + counts.regions) (nodeBase + counts.nodes)
          (wireBase + counts.wires) wires binders tail)
end

def flattenOpen (diagram : VisualProof.Diagram.OpenDiagram arity) : Flat :=
  let body : Flat := flattenRegion .sheet 0 0 diagram.externalClasses
    (fun external => external.val) BinderMap.empty diagram.body
  { regions := body.regions
    nodes := body.nodes
    wireScopes := List.replicate diagram.externalClasses 0 ++
      body.wireScopes }

mutual
  theorem flattenRegion_lengths
      (regionKind : RegionDraft)
      (regionBase nodeBase wireBase : Nat)
      (outerWires : WireMap outerCount)
      (binders : BinderMap rels) :
      (region : Region outerCount rels) →
      (flattenRegion regionKind regionBase nodeBase wireBase
          outerWires binders region).regions.length =
          (regionCounts region).regions ∧
        (flattenRegion regionKind regionBase nodeBase wireBase
          outerWires binders region).nodes.length =
          (regionCounts region).nodes ∧
        (flattenRegion regionKind regionBase nodeBase wireBase
          outerWires binders region).wireScopes.length =
          (regionCounts region).wires
    | .mk localWires items => by
        have nested := flattenItems_lengths regionBase (regionBase + 1)
          nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders items
        simp only [flattenRegion, regionCounts, List.length_cons,
          List.length_append, List.length_replicate]
        rcases nested with ⟨regionsLength, nodesLength, wiresLength⟩
        rw [regionsLength, nodesLength, wiresLength]
        exact ⟨by omega, by omega, by omega⟩

  theorem flattenItems_lengths
      (currentRegion regionBase nodeBase wireBase : Nat)
      (wires : WireMap wireCount)
      (binders : BinderMap rels) :
      (items : ItemSeq wireCount rels) →
      (flattenItems currentRegion regionBase nodeBase wireBase
          wires binders items).regions.length =
          (itemSeqCounts items).regions ∧
        (flattenItems currentRegion regionBase nodeBase wireBase
          wires binders items).nodes.length =
          (itemSeqCounts items).nodes ∧
        (flattenItems currentRegion regionBase nodeBase wireBase
          wires binders items).wireScopes.length =
          (itemSeqCounts items).wires
    | .nil => by
        simp [flattenItems, Flat.empty, itemSeqCounts]
    | .cons head tail => by
        have tailLengths := flattenItems_lengths currentRegion
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wires binders tail
        cases head with
        | atom relation arguments =>
            simp only [itemCounts] at tailLengths
            simp only [flattenItems, itemCounts, itemSeqCounts, Counts.add,
              Flat.append, List.length_append, List.length_nil,
              List.length_cons]
            rcases tailLengths with ⟨regionsLength, nodesLength, wiresLength⟩
            rw [regionsLength, nodesLength, wiresLength]
            exact ⟨by omega, by omega, by omega⟩
        | identity arity arguments =>
            simp only [itemCounts] at tailLengths
            simp only [flattenItems, itemCounts, itemSeqCounts, Counts.add,
              Flat.append, List.length_append, List.length_nil,
              List.length_cons]
            rcases tailLengths with ⟨regionsLength, nodesLength, wiresLength⟩
            rw [regionsLength, nodesLength, wiresLength]
            exact ⟨by omega, by omega, by omega⟩
        | cut body =>
            simp only [itemCounts] at tailLengths
            have headLengths := flattenRegion_lengths
              (.cut currentRegion) regionBase nodeBase wireBase
              wires binders body
            simp only [flattenItems, itemCounts, itemSeqCounts, Counts.add,
              Flat.append, List.length_append]
            rcases headLengths with
              ⟨headRegionsLength, headNodesLength, headWiresLength⟩
            rcases tailLengths with
              ⟨tailRegionsLength, tailNodesLength, tailWiresLength⟩
            rw [headRegionsLength, headNodesLength, headWiresLength,
              tailRegionsLength, tailNodesLength, tailWiresLength]
            exact ⟨by omega, by omega, by omega⟩
        | bubble arity body =>
            simp only [itemCounts] at tailLengths
            have headLengths := flattenRegion_lengths
              (.bubble currentRegion arity) regionBase nodeBase wireBase
              wires (binders.push regionBase) body
            simp only [flattenItems, itemCounts, itemSeqCounts, Counts.add,
              Flat.append, List.length_append]
            rcases headLengths with
              ⟨headRegionsLength, headNodesLength, headWiresLength⟩
            rcases tailLengths with
              ⟨tailRegionsLength, tailNodesLength, tailWiresLength⟩
            rw [headRegionsLength, headNodesLength, headWiresLength,
              tailRegionsLength, tailNodesLength, tailWiresLength]
            exact ⟨by omega, by omega, by omega⟩
end

theorem flattenRegion_regions_length
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (region : Region outerCount rels) :
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).regions.length =
      (regionCounts region).regions :=
  (flattenRegion_lengths regionKind regionBase nodeBase wireBase
    outerWires binders region).1

theorem flattenRegion_nodes_length
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (region : Region outerCount rels) :
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).nodes.length =
      (regionCounts region).nodes :=
  (flattenRegion_lengths regionKind regionBase nodeBase wireBase
    outerWires binders region).2.1

theorem flattenRegion_wireScopes_length
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (region : Region outerCount rels) :
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).wireScopes.length =
      (regionCounts region).wires :=
  (flattenRegion_lengths regionKind regionBase nodeBase wireBase
    outerWires binders region).2.2

theorem flattenRegion_regions_pos
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (region : Region outerCount rels) :
    0 < (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).regions.length := by
  rw [flattenRegion_regions_length]
  cases region
  simp [regionCounts]

private theorem regionCounts_regions_pos (region : Region wires rels) :
    0 < (regionCounts region).regions := by
  cases region
  simp [regionCounts]

@[simp] theorem flattenRegion_regions_get_zero
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (region : Region outerCount rels) :
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).regions.get
        ⟨0, flattenRegion_regions_pos regionKind regionBase nodeBase wireBase
          outerWires binders region⟩ = regionKind := by
  cases region
  rfl

def RegionDraft.Bounded (limit : Nat) : RegionDraft → Prop
  | .sheet => True
  | .cut parent => parent < limit
  | .bubble parent _ => parent < limit

def NodeDraft.Bounded (limit : Nat) : NodeDraft → Prop
  | .atom region binder _ _ => region < limit ∧ binder < limit
  | .identity region _ _ => region < limit

structure Flat.Bounded (flat : Flat) (limit : Nat) : Prop where
  regions : ∀ draft, draft ∈ flat.regions → draft.Bounded limit
  nodes : ∀ draft, draft ∈ flat.nodes → draft.Bounded limit
  wireScopes : ∀ scope, scope ∈ flat.wireScopes → scope < limit

theorem Flat.empty_bounded (limit : Nat) : Flat.empty.Bounded limit := by
  exact ⟨by simp [Flat.empty], by simp [Flat.empty], by simp [Flat.empty]⟩

theorem Flat.Bounded.append
    {left right : Flat}
    (leftBounded : left.Bounded limit)
    (rightBounded : right.Bounded limit) :
    (left.append right).Bounded limit := by
  exact {
    regions := by
      intro draft member
      rcases List.mem_append.mp member with member | member
      · exact leftBounded.regions draft member
      · exact rightBounded.regions draft member
    nodes := by
      intro draft member
      rcases List.mem_append.mp member with member | member
      · exact leftBounded.nodes draft member
      · exact rightBounded.nodes draft member
    wireScopes := by
      intro scope member
      rcases List.mem_append.mp member with member | member
      · exact leftBounded.wireScopes scope member
      · exact rightBounded.wireScopes scope member
  }

def BinderMap.Bounded (binders : BinderMap rels) (limit : Nat) : Prop :=
  ∀ arity (relation : RelVar rels arity), binders arity relation < limit

theorem BinderMap.empty_bounded (limit : Nat) :
    BinderMap.Bounded BinderMap.empty limit := by
  intro arity relation
  exact Fin.elim0 relation.index

theorem BinderMap.push_bounded
    {rels : RelCtx} {arity : Nat}
    (outer : BinderMap rels)
    (outerBounded : BinderMap.Bounded outer limit)
    (binderBounded : binder < limit) :
    BinderMap.Bounded (@BinderMap.push rels arity outer binder) limit := by
  intro relationArity relation
  rcases relation with ⟨index, hasArity⟩
  induction index using Fin.cases with
  | zero => exact binderBounded
  | succ tailIndex =>
      exact outerBounded relationArity {
        index := tailIndex
        hasArity := by simpa using hasArity
      }

private def flattenItem
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels) : Item wireCount rels → Flat
  | .atom relation arguments =>
      ⟨[], [.atom currentRegion (binders _ relation)
        _ (wires ∘ arguments)], []⟩
  | .identity arity arguments =>
      ⟨[], [.identity currentRegion arity (wires ∘ arguments)], []⟩
  | .cut body =>
      flattenRegion (.cut currentRegion) regionBase nodeBase wireBase
        wires binders body
  | .bubble arity body =>
      flattenRegion (.bubble currentRegion arity) regionBase nodeBase wireBase
        wires (binders.push regionBase) body

private theorem flattenItem_lengths
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels)
    (item : Item wireCount rels) :
    (flattenItem currentRegion regionBase nodeBase wireBase
      wires binders item).regions.length = (itemCounts item).regions ∧
    (flattenItem currentRegion regionBase nodeBase wireBase
      wires binders item).nodes.length = (itemCounts item).nodes ∧
    (flattenItem currentRegion regionBase nodeBase wireBase
      wires binders item).wireScopes.length = (itemCounts item).wires := by
  cases item with
  | atom relation arguments => simp [flattenItem, itemCounts]
  | identity arity arguments => simp [flattenItem, itemCounts]
  | cut body =>
      exact flattenRegion_lengths (.cut currentRegion) regionBase nodeBase
        wireBase wires binders body
  | bubble arity body =>
      exact flattenRegion_lengths (.bubble currentRegion arity) regionBase
        nodeBase wireBase wires (binders.push regionBase) body

private def RegionBoundedMotive
    (wireCount : Nat) (rels : RelCtx)
    (region : Region wireCount rels) : Prop :=
  ∀ (regionKind : RegionDraft)
    (regionBase nodeBase wireBase limit : Nat)
    (outerWires : WireMap wireCount)
    (binders : BinderMap rels),
    regionKind.Bounded limit →
    regionBase < limit →
    binders.Bounded limit →
    regionBase + (regionCounts region).regions ≤ limit →
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).Bounded limit

private def ItemBoundedMotive
    (wireCount : Nat) (rels : RelCtx)
    (item : Item wireCount rels) : Prop :=
  ∀ (currentRegion regionBase nodeBase wireBase limit : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels),
    currentRegion < limit →
    binders.Bounded limit →
    regionBase + (itemCounts item).regions ≤ limit →
    (flattenItem currentRegion regionBase nodeBase wireBase
      wires binders item).Bounded limit

private def ItemsBoundedMotive
    (wireCount : Nat) (rels : RelCtx)
    (items : ItemSeq wireCount rels) : Prop :=
  ∀ (currentRegion regionBase nodeBase wireBase limit : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels),
    currentRegion < limit →
    binders.Bounded limit →
    regionBase + (itemSeqCounts items).regions ≤ limit →
    (flattenItems currentRegion regionBase nodeBase wireBase
      wires binders items).Bounded limit

private theorem flattenItems_bounded_core
    (items : ItemSeq wireCount rels) :
    ItemsBoundedMotive wireCount rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionBoundedMotive)
      (motive_2 := ItemBoundedMotive)
      (motive_3 := ItemsBoundedMotive)
  case mk =>
      intro wires rels localWires nested nestedBounded
      intro regionKind regionBase nodeBase wireBase limit outerWires binders
        kindBounded regionBaseBounded bindersBounded segmentBounded
      have nestedResult := nestedBounded regionBase (regionBase + 1)
        nodeBase (wireBase + localWires) limit
        (outerWires.extend wireBase localWires) binders
        regionBaseBounded bindersBounded (by
          simp only [regionCounts] at segmentBounded
          omega)
      exact {
        regions := by
          intro draft member
          simp only [flattenRegion, List.mem_cons] at member
          rcases member with rfl | member
          · exact kindBounded
          · exact nestedResult.regions draft member
        nodes := nestedResult.nodes
        wireScopes := by
          intro scope member
          simp only [flattenRegion, List.mem_append,
            List.mem_replicate] at member
          rcases member with ⟨_, rfl⟩ | member
          · exact regionBaseBounded
          · exact nestedResult.wireScopes scope member
      }
  case atom =>
      intro rels arity wires relation arguments
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      exact {
        regions := by simp [flattenItem]
        nodes := by
          simp [flattenItem, NodeDraft.Bounded, currentBounded,
            bindersBounded _ relation]
        wireScopes := by simp [flattenItem]
      }
  case identity =>
      intro wires rels arity arguments
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      exact {
        regions := by simp [flattenItem]
        nodes := by simp [flattenItem, NodeDraft.Bounded, currentBounded]
        wireScopes := by simp [flattenItem]
      }
  case cut =>
      intro wires rels body bodyBounded
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      have bodyPositive : 0 < (regionCounts body).regions := by
        cases body
        simp [regionCounts]
      exact bodyBounded (.cut currentRegion) regionBase nodeBase wireBase
        limit wires binders currentBounded (by
          simp only [itemCounts] at segmentBounded
          omega) bindersBounded (by
            simp only [itemCounts] at segmentBounded
            omega)
  case bubble =>
      intro wires rels arity body bodyBounded
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      have bodyPositive : 0 < (regionCounts body).regions := by
        cases body
        simp [regionCounts]
      have regionBaseBounded : regionBase < limit := by
        simp only [itemCounts] at segmentBounded
        omega
      exact bodyBounded (.bubble currentRegion arity) regionBase nodeBase
        wireBase limit wires (binders.push regionBase) currentBounded
        regionBaseBounded
        (BinderMap.push_bounded (arity := arity) binders bindersBounded
          regionBaseBounded) (by
            simp only [itemCounts] at segmentBounded
            omega)
  case nil =>
      intro wires rels
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      exact Flat.empty_bounded limit
  case cons =>
      intro wires rels head tail headBounded tailBounded
      intro currentRegion regionBase nodeBase wireBase limit wires binders
        currentBounded bindersBounded segmentBounded
      have headResult := headBounded currentRegion regionBase nodeBase
        wireBase limit wires binders currentBounded bindersBounded (by
          simp only [itemSeqCounts, Counts.add] at segmentBounded
          omega)
      have tailResult := tailBounded currentRegion
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) limit wires binders
        currentBounded bindersBounded (by
          simp only [itemSeqCounts, Counts.add] at segmentBounded
          omega)
      cases head <;>
        exact Flat.Bounded.append headResult tailResult

theorem flattenItems_bounded
    (currentRegion regionBase nodeBase wireBase limit : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels)
    (currentBounded : currentRegion < limit)
    (bindersBounded : binders.Bounded limit)
    (items : ItemSeq wireCount rels)
    (segmentBounded : regionBase + (itemSeqCounts items).regions ≤ limit) :
    (flattenItems currentRegion regionBase nodeBase wireBase
      wires binders items).Bounded limit :=
  flattenItems_bounded_core items currentRegion regionBase nodeBase wireBase
    limit wires binders currentBounded bindersBounded segmentBounded

theorem flattenRegion_bounded
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase limit : Nat)
    (outerWires : WireMap outerCount)
    (binders : BinderMap rels)
    (kindBounded : regionKind.Bounded limit)
    (regionBaseBounded : regionBase < limit)
    (bindersBounded : binders.Bounded limit)
    (region : Region outerCount rels)
    (segmentBounded : regionBase + (regionCounts region).regions ≤ limit) :
    (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region).Bounded limit := by
  cases region with
  | mk localWires items =>
      have nestedBounded := flattenItems_bounded regionBase
        (regionBase + 1) nodeBase (wireBase + localWires) limit
        (outerWires.extend wireBase localWires) binders
        regionBaseBounded bindersBounded items (by
          simp only [regionCounts] at segmentBounded
          omega)
      exact {
        regions := by
          intro draft member
          simp only [flattenRegion, List.mem_cons] at member
          rcases member with rfl | member
          · exact kindBounded
          · exact nestedBounded.regions draft member
        nodes := nestedBounded.nodes
        wireScopes := by
          intro scope member
          simp only [flattenRegion, List.mem_append,
            List.mem_replicate] at member
          rcases member with ⟨_, rfl⟩ | member
          · exact regionBaseBounded
          · exact nestedBounded.wireScopes scope member
      }

theorem flattenOpen_bounded
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (flattenOpen diagram).Bounded (flattenOpen diagram).regions.length := by
  let body := flattenRegion .sheet 0 0 diagram.externalClasses
    (fun external => external.val) BinderMap.empty diagram.body
  have bodyBounded : body.Bounded (regionCounts diagram.body).regions := by
    apply flattenRegion_bounded .sheet 0 0 diagram.externalClasses
      (regionCounts diagram.body).regions
      (fun external => external.val) BinderMap.empty
    · trivial
    · cases diagram.body
      simp [regionCounts]
    · exact BinderMap.empty_bounded _
    · omega
  have regionsLength : body.regions.length =
      (regionCounts diagram.body).regions :=
    flattenRegion_regions_length .sheet 0 0 diagram.externalClasses
      (fun external => external.val) BinderMap.empty diagram.body
  rw [← regionsLength] at bodyBounded
  exact {
    regions := bodyBounded.regions
    nodes := bodyBounded.nodes
    wireScopes := by
      unfold flattenOpen
      intro scope member
      simp only [List.mem_append, List.mem_replicate] at member
      rcases member with ⟨_, rfl⟩ | member
      · rw [regionsLength]
        cases diagram.body
        simp [regionCounts]
      · exact bodyBounded.wireScopes scope member
  }

theorem flattenOpen_regions_pos
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    0 < (flattenOpen diagram).regions.length := by
  cases hbody : diagram.body with
  | mk localWires items =>
      simp [flattenOpen, hbody, flattenRegion]

def RegionDraft.toConcrete
    (draft : RegionDraft) (bounded : draft.Bounded limit) : CRegion limit := by
  cases draft with
  | sheet => exact .sheet
  | cut parent => exact .cut ⟨parent, bounded⟩
  | bubble parent binderArity => exact .bubble ⟨parent, bounded⟩ binderArity

def NodeDraft.toConcrete
    (draft : NodeDraft) (bounded : draft.Bounded limit) : CNode limit := by
  cases draft with
  | atom region binder arity arguments =>
      exact .atom ⟨region, bounded.1⟩ ⟨binder, bounded.2⟩
  | identity region nodeArity arguments =>
      exact .identity ⟨region, bounded⟩ nodeArity

def NodeDraft.arguments : NodeDraft → List Nat
  | .atom _ _ _ arguments => List.ofFn arguments
  | .identity _ _ arguments => List.ofFn arguments

def NodeDraft.arity : NodeDraft → Nat
  | .atom _ _ arity _ => arity
  | .identity _ arity _ => arity

def NodeDraft.argument (draft : NodeDraft) : Fin draft.arity → Nat :=
  match draft with
  | .atom _ _ _ arguments => arguments
  | .identity _ _ arguments => arguments

def NodeDraft.argument? (draft : NodeDraft) : CPort → Option Nat
  | .arg index =>
      if bound : index < draft.arity then
        some (draft.argument ⟨index, bound⟩)
      else
        none

def endpointsAtNode (nodes : List NodeDraft) (wire : Nat)
    (node : Fin nodes.length) : List (CEndpoint nodes.length) :=
  let draft := nodes.get node
  (List.ofFn fun port : Fin draft.arity =>
    if draft.argument port = wire then
      some ({ node := node, port := .arg port.val } :
        CEndpoint nodes.length)
    else none).filterMap id

def endpointsForWire (nodes : List NodeDraft) (wire : Nat) :
    List (CEndpoint nodes.length) :=
  (List.ofFn fun node : Fin nodes.length =>
    endpointsAtNode nodes wire node).flatten

def externalWire (diagram : VisualProof.Diagram.OpenDiagram arity)
    (external : Fin diagram.externalClasses) :
    Fin (flattenOpen diagram).wireScopes.length :=
  ⟨external.val, by
    unfold flattenOpen
    simp only [List.length_append, List.length_replicate]
    omega⟩

def rawDiagram (diagram : VisualProof.Diagram.OpenDiagram arity) :
    Concrete.Diagram where
  regionCount := (flattenOpen diagram).regions.length
  nodeCount := (flattenOpen diagram).nodes.length
  wireCount := (flattenOpen diagram).wireScopes.length
  root := ⟨0, flattenOpen_regions_pos diagram⟩
  regions := fun region =>
    let draft := (flattenOpen diagram).regions.get region
    draft.toConcrete ((flattenOpen_bounded diagram).regions draft
      (List.get_mem _ region))
  nodes := fun node =>
    let draft := (flattenOpen diagram).nodes.get node
    draft.toConcrete ((flattenOpen_bounded diagram).nodes draft
      (List.get_mem _ node))
  wires := fun wire => {
    scope := ⟨(flattenOpen diagram).wireScopes.get wire,
      (flattenOpen_bounded diagram).wireScopes
        ((flattenOpen diagram).wireScopes.get wire) (List.get_mem _ wire)⟩
    endpoints := endpointsForWire (flattenOpen diagram).nodes wire.val
  }

def rawOpen (diagram : VisualProof.Diagram.OpenDiagram arity) :
    Concrete.OpenDiagram where
  diagram := rawDiagram diagram
  boundary := List.ofFn fun position =>
    externalWire diagram (diagram.boundary position)

@[simp] theorem rawOpen_boundary_length
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (rawOpen diagram).boundary.length = arity := by
  simp [rawOpen]

/-- The three semantic facts not already supplied by `Flat.Bounded`.
They are stated against the exact proof-carrying concrete realization so that
the downstream well-formedness proof does not duplicate index transports. -/
structure Flat.Valid
    (diagram : VisualProof.Diagram.OpenDiagram arity) : Prop where
  region_ordered : ∀ region : Fin (rawDiagram diagram).regionCount,
    match (rawDiagram diagram).regions region with
    | .sheet => region = (rawDiagram diagram).root
    | .cut parent => parent.val < region.val
    | .bubble parent _ => parent.val < region.val
  atom_valid : ∀ node : Fin (rawDiagram diagram).nodeCount,
    match (flattenOpen diagram).nodes.get node with
    | .atom _ _ arity _ =>
        ∃ region binder parent,
          (rawDiagram diagram).nodes node = .atom region binder ∧
          (rawDiagram diagram).regions binder = .bubble parent arity ∧
          (rawDiagram diagram).Encloses binder region
    | .identity _ _ _ => True
  argument_valid : ∀ node : Fin (rawDiagram diagram).nodeCount,
    ∀ port : Fin ((flattenOpen diagram).nodes.get node).arity,
      ∃ wire : Fin (rawDiagram diagram).wireCount,
        wire.val = ((flattenOpen diagram).nodes.get node).argument port ∧
        (rawDiagram diagram).Encloses
          ((rawDiagram diagram).wires wire).scope
          ((rawDiagram diagram).nodes node).region

@[simp] theorem mem_endpointsForWire_iff
    (nodes : List NodeDraft) (wire : Nat)
    (endpoint : CEndpoint nodes.length) :
    endpoint ∈ endpointsForWire nodes wire ↔
      (nodes.get endpoint.node).argument? endpoint.port = some wire := by
  rcases endpoint with ⟨node, ⟨index⟩⟩
  constructor
  · intro member
    rw [endpointsForWire, List.mem_flatten] at member
    rcases member with ⟨values, valuesMember, endpointMember⟩
    rcases List.mem_ofFn.mp valuesMember with ⟨candidate, rfl⟩
    rw [endpointsAtNode] at endpointMember
    rw [List.mem_filterMap] at endpointMember
    rcases endpointMember with ⟨candidateEndpoint, candidateMember,
      candidateEq⟩
    simp only [id_eq] at candidateEq
    subst candidateEndpoint
    rcases List.mem_ofFn.mp candidateMember with ⟨port, hport⟩
    split at hport
    · rename_i hargument
      have endpointEq :
          ({ node := candidate, port := .arg port.val } :
              CEndpoint nodes.length) =
            { node := node, port := .arg index } := by
        simpa using hport
      have nodeEq : candidate = node := congrArg CEndpoint.node endpointEq
      subst candidate
      have indexEq : port.val = index := by
        have := congrArg CEndpoint.port endpointEq
        simp at this
        exact this
      have bound : index < (nodes.get node).arity := by omega
      simp only [NodeDraft.argument?, dif_pos bound, Option.some.injEq]
      have portEq : port = ⟨index, bound⟩ := Fin.ext indexEq
      rw [← portEq]
      exact hargument
    · contradiction
  · intro argument
    simp only [NodeDraft.argument?] at argument
    split at argument
    · rename_i bound
      simp only [Option.some.injEq] at argument
      rw [endpointsForWire, List.mem_flatten]
      refine ⟨_, List.mem_ofFn.mpr ⟨node, rfl⟩, ?_⟩
      rw [endpointsAtNode]
      rw [List.mem_filterMap]
      refine ⟨some { node := node, port := .arg index }, ?_, rfl⟩
      apply List.mem_ofFn.mpr
      have argument' :
          (nodes.get node).argument ⟨index, bound⟩ = wire := by
        exact argument
      exact ⟨⟨index, bound⟩, by rw [if_pos argument']⟩
    · contradiction

theorem endpointsAtNode_nodup
    (nodes : List NodeDraft) (wire : Nat) (node : Fin nodes.length) :
    (endpointsAtNode nodes wire node).Nodup := by
  rw [List.nodup_iff_pairwise_ne, endpointsAtNode,
    List.pairwise_filterMap, List.pairwise_iff_getElem]
  intro left right leftBound rightBound ordered
  simp only [List.length_ofFn, List.getElem_ofFn] at leftBound rightBound ⊢
  intro leftEndpoint leftEq rightEndpoint rightEq
  simp only [id_eq] at leftEq rightEq
  split at leftEq
  · split at rightEq
    · intro endpointEq
      simp only [Option.some.injEq] at leftEq rightEq
      have concreteEq := leftEq.trans (endpointEq.trans rightEq.symm)
      have portEqual := congrArg CEndpoint.port concreteEq
      simp at portEqual
      omega
    · contradiction
  · contradiction

theorem node_eq_of_mem_endpointsAtNode
    (nodes : List NodeDraft) (wire : Nat) (node : Fin nodes.length)
    (endpoint : CEndpoint nodes.length)
    (member : endpoint ∈ endpointsAtNode nodes wire node) :
    endpoint.node = node := by
  rw [endpointsAtNode, List.mem_filterMap] at member
  rcases member with ⟨candidate, candidateMember, candidateEq⟩
  simp only [id_eq] at candidateEq
  subst candidate
  rcases List.mem_ofFn.mp candidateMember with ⟨port, portEq⟩
  split at portEq
  · have endpointEq : endpoint =
        ({ node := node, port := .arg port.val } :
          CEndpoint nodes.length) := by
      simpa using portEq.symm
    exact congrArg CEndpoint.node endpointEq
  · contradiction

theorem endpointsForWire_nodup
    (nodes : List NodeDraft) (wire : Nat) :
    (endpointsForWire nodes wire).Nodup := by
  rw [List.nodup_iff_pairwise_ne, endpointsForWire,
    List.pairwise_flatten]
  constructor
  · intro values valuesMember
    rcases List.mem_ofFn.mp valuesMember with ⟨node, rfl⟩
    exact endpointsAtNode_nodup nodes wire node
  · rw [List.pairwise_iff_getElem]
    intro left right leftBound rightBound ordered
    simp only [List.length_ofFn, List.getElem_ofFn] at leftBound rightBound ⊢
    intro leftEndpoint leftMember rightEndpoint rightMember endpointEq
    have leftNode := node_eq_of_mem_endpointsAtNode nodes wire
      ⟨left, leftBound⟩ leftEndpoint leftMember
    have rightNode := node_eq_of_mem_endpointsAtNode nodes wire
      ⟨right, rightBound⟩ rightEndpoint rightMember
    have nodesEq := congrArg CEndpoint.node endpointEq
    rw [leftNode, rightNode] at nodesEq
    have valuesEq := congrArg Fin.val nodesEq
    exact (Nat.ne_of_lt ordered) valuesEq

theorem endpointsForWire_disjoint
    (nodes : List NodeDraft) {left right : Nat} (different : left ≠ right)
    (endpoint : CEndpoint nodes.length)
    (leftMember : endpoint ∈ endpointsForWire nodes left) :
    endpoint ∉ endpointsForWire nodes right := by
  intro rightMember
  have leftArgument := (mem_endpointsForWire_iff nodes left endpoint).mp
    leftMember
  have rightArgument := (mem_endpointsForWire_iff nodes right endpoint).mp
    rightMember
  exact different (Option.some.inj (leftArgument.symm.trans rightArgument))

theorem NodeDraft.toConcrete_congr
    {first second : NodeDraft} (equal : first = second)
    (bounded : first.Bounded limit) :
    first.toConcrete bounded = second.toConcrete (equal ▸ bounded) := by
  subst second
  rfl

theorem RegionDraft.toConcrete_congr
    {first second : RegionDraft} (equal : first = second)
    (bounded : first.Bounded limit) :
    first.toConcrete bounded = second.toConcrete (equal ▸ bounded) := by
  subst second
  rfl

def externalWires (diagram : VisualProof.Diagram.OpenDiagram arity) :
    List (Fin (flattenOpen diagram).wireScopes.length) :=
  List.ofFn (externalWire diagram)

@[simp] theorem externalWires_length
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (externalWires diagram).length = diagram.externalClasses := by
  simp [externalWires]

theorem externalWire_injective
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    Function.Injective (externalWire diagram) := by
  intro first second equal
  apply Fin.ext
  simpa [externalWire] using congrArg Fin.val equal

theorem externalWires_nodup
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (externalWires diagram).Nodup := by
  have externalWiresEq : externalWires diagram =
      (allFin diagram.externalClasses).map (externalWire diagram) := by
    rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
    rfl
  rw [externalWiresEq]
  exact (allFin_nodup diagram.externalClasses).map (externalWire diagram)
    (fun first second distinct equal =>
      distinct ((externalWire_injective diagram) equal))

@[simp] theorem mem_externalWires
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (wire : Fin (flattenOpen diagram).wireScopes.length) :
    wire ∈ externalWires diagram ↔
      ∃ external, wire = externalWire diagram external := by
  constructor
  · simp only [externalWires, List.mem_ofFn]
    rintro ⟨external, rfl⟩
    exact ⟨external, rfl⟩
  · rintro ⟨external, rfl⟩
    exact List.mem_ofFn.mpr ⟨external, rfl⟩

@[simp] theorem rawOpen_boundary_get
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (position : Fin (rawOpen diagram).boundary.length) :
    (rawOpen diagram).boundary.get position =
      externalWire diagram
        (diagram.boundary (Fin.cast (rawOpen_boundary_length diagram) position)) := by
  simp only [rawOpen, List.get_eq_getElem, List.getElem_ofFn]
  congr 2

@[simp] theorem mem_rawOpen_exposedWires_iff
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (wire : Fin (flattenOpen diagram).wireScopes.length) :
    wire ∈ (rawOpen diagram).exposedWires ↔
      wire ∈ externalWires diagram := by
  constructor
  · intro member
    have member :=
      (VisualProof.Concrete.OpenDiagram.mem_exposedWires
        (rawOpen diagram) wire).mp member
    rw [List.mem_iff_get] at member
    rcases member with ⟨position, equality⟩
    exact (mem_externalWires diagram wire).mpr
      ⟨diagram.boundary (Fin.cast (rawOpen_boundary_length diagram) position),
        equality.symm.trans (rawOpen_boundary_get diagram position)⟩
  · intro member
    rw [mem_externalWires] at member
    rcases member with ⟨external, rfl⟩
    obtain ⟨position, positionClass⟩ := diagram.boundary_surjective external
    apply (VisualProof.Concrete.OpenDiagram.mem_exposedWires
      (rawOpen diagram) (externalWire diagram external)).mpr
    rw [List.mem_iff_get]
    let rawPosition : Fin (rawOpen diagram).boundary.length :=
      Fin.cast (rawOpen_boundary_length diagram).symm position
    refine ⟨rawPosition, ?_⟩
    rw [rawOpen_boundary_get]
    have positionEq : Fin.cast (rawOpen_boundary_length diagram) rawPosition =
        position := by
      apply Fin.ext
      rfl
    rw [positionEq, positionClass]

private def externalRestriction
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    FiniteEquiv (Fin (externalWires diagram).length)
      (Fin (rawOpen diagram).exposedWires.length) :=
  FiniteEquiv.restrictLists
      (FiniteEquiv.refl (Fin (flattenOpen diagram).wireScopes.length))
      (externalWires diagram) (rawOpen diagram).exposedWires
      (externalWires_nodup diagram)
      (rawOpen diagram).exposedWires_nodup
      (fun wire => by
        change wire ∈ (rawOpen diagram).exposedWires ↔
          wire ∈ externalWires diagram
        exact mem_rawOpen_exposedWires_iff diagram wire)

private theorem externalRestriction_spec
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (index : Fin (externalWires diagram).length) :
    (rawOpen diagram).exposedWires.get (externalRestriction diagram index) =
      (externalWires diagram).get index := by
  unfold externalRestriction
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin (flattenOpen diagram).wireScopes.length))
    (externalWires diagram) (rawOpen diagram).exposedWires
    (externalWires_nodup diagram)
    (rawOpen diagram).exposedWires_nodup
    (fun wire => by
      change wire ∈ (rawOpen diagram).exposedWires ↔
        wire ∈ externalWires diagram
      exact mem_rawOpen_exposedWires_iff diagram wire) index

def externalEquiv (diagram : VisualProof.Diagram.OpenDiagram arity) :
    FiniteEquiv (Fin diagram.externalClasses)
      (Fin (rawOpen diagram).exposedWires.length) :=
  (FiniteEquiv.finCast (externalWires_length diagram).symm).trans
    (externalRestriction diagram)

theorem externalEquiv_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (external : Fin diagram.externalClasses) :
    (rawOpen diagram).exposedWires.get (externalEquiv diagram external) =
      externalWire diagram external := by
  unfold externalEquiv
  rw [FiniteEquiv.trans_apply]
  change (rawOpen diagram).exposedWires.get
      (externalRestriction diagram
        (FiniteEquiv.finCast (externalWires_length diagram).symm external)) = _
  rw [externalRestriction_spec]
  simp [FiniteEquiv.finCast, externalWires]

theorem externalEquiv_boundary
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (position : Fin (rawOpen diagram).boundary.length) :
    externalEquiv diagram
        (diagram.boundary (Fin.cast (rawOpen_boundary_length diagram) position)) =
      (rawOpen diagram).boundaryClass position := by
  apply Fin.ext
  have complete := VisualProof.Concrete.OpenDiagram.boundaryClass_complete
    (rawOpen diagram) position (externalEquiv diagram
      (diagram.boundary (Fin.cast (rawOpen_boundary_length diagram) position)))
  apply congrArg Fin.val
  apply complete
  rw [externalEquiv_lookup]
  exact (rawOpen_boundary_get diagram position).symm

structure NodeAtomLookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (region binder nodeArity : Nat) (arguments : Fin nodeArity → Nat) where
  concreteRegion : Fin (rawDiagram diagram).regionCount
  concreteBinder : Fin (rawDiagram diagram).regionCount
  node_eq : (rawDiagram diagram).nodes node =
    .atom concreteRegion concreteBinder
  region_val : concreteRegion.val = region
  binder_val : concreteBinder.val = binder

def rawDiagram_node_atom_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (region binder nodeArity : Nat) (arguments : Fin nodeArity → Nat)
    (draftEq : (flattenOpen diagram).nodes.get node =
      .atom region binder nodeArity arguments) :
    NodeAtomLookup diagram node region binder nodeArity arguments := by
  have atomBounded :
      (NodeDraft.atom region binder nodeArity arguments).Bounded
        (flattenOpen diagram).regions.length := by
    rw [← draftEq]
    exact (flattenOpen_bounded diagram).nodes _ (List.get_mem _ node)
  refine ⟨⟨region, atomBounded.1⟩, ⟨binder, atomBounded.2⟩, ?_, rfl, rfl⟩
  unfold rawDiagram
  dsimp only
  exact (NodeDraft.toConcrete_congr draftEq
    ((flattenOpen_bounded diagram).nodes _ (List.get_mem _ node))).trans (by
      rfl)

structure NodeIdentityLookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (region nodeArity : Nat) (arguments : Fin nodeArity → Nat) where
  concreteRegion : Fin (rawDiagram diagram).regionCount
  node_eq : (rawDiagram diagram).nodes node =
    .identity concreteRegion nodeArity
  region_val : concreteRegion.val = region

def rawDiagram_node_identity_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (region nodeArity : Nat) (arguments : Fin nodeArity → Nat)
    (draftEq : (flattenOpen diagram).nodes.get node =
      .identity region nodeArity arguments) :
    NodeIdentityLookup diagram node region nodeArity arguments := by
  have identityBounded :
      (NodeDraft.identity region nodeArity arguments).Bounded
        (flattenOpen diagram).regions.length := by
    rw [← draftEq]
    exact (flattenOpen_bounded diagram).nodes _ (List.get_mem _ node)
  refine ⟨⟨region, identityBounded⟩, ?_, rfl⟩
  unfold rawDiagram
  dsimp only
  exact (NodeDraft.toConcrete_congr draftEq
    ((flattenOpen_bounded diagram).nodes _ (List.get_mem _ node))).trans (by
      rfl)

structure RegionBubbleLookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (region : Fin (rawDiagram diagram).regionCount)
    (parent binderArity : Nat) where
  concreteParent : Fin (rawDiagram diagram).regionCount
  region_eq : (rawDiagram diagram).regions region =
    .bubble concreteParent binderArity
  parent_val : concreteParent.val = parent

def rawDiagram_region_bubble_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (region : Fin (rawDiagram diagram).regionCount)
    (parent binderArity : Nat)
    (draftEq : (flattenOpen diagram).regions.get region =
      .bubble parent binderArity) :
    RegionBubbleLookup diagram region parent binderArity := by
  have bubbleBounded :
      (RegionDraft.bubble parent binderArity).Bounded
        (flattenOpen diagram).regions.length := by
    rw [← draftEq]
    exact (flattenOpen_bounded diagram).regions _ (List.get_mem _ region)
  refine ⟨⟨parent, bubbleBounded⟩, ?_, rfl⟩
  unfold rawDiagram
  dsimp only
  exact (RegionDraft.toConcrete_congr draftEq
    ((flattenOpen_bounded diagram).regions _ (List.get_mem _ region))).trans
      (by rfl)

structure RegionCutLookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (region : Fin (rawDiagram diagram).regionCount)
    (parent : Nat) where
  concreteParent : Fin (rawDiagram diagram).regionCount
  region_eq : (rawDiagram diagram).regions region = .cut concreteParent
  parent_val : concreteParent.val = parent

def rawDiagram_region_cut_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (region : Fin (rawDiagram diagram).regionCount)
    (parent : Nat)
    (draftEq : (flattenOpen diagram).regions.get region = .cut parent) :
    RegionCutLookup diagram region parent := by
  have cutBounded :
      (RegionDraft.cut parent).Bounded
        (flattenOpen diagram).regions.length := by
    rw [← draftEq]
    exact (flattenOpen_bounded diagram).regions _ (List.get_mem _ region)
  refine ⟨⟨parent, cutBounded⟩, ?_, rfl⟩
  unfold rawDiagram
  dsimp only
  exact (RegionDraft.toConcrete_congr draftEq
    ((flattenOpen_bounded diagram).regions _ (List.get_mem _ region))).trans
      (by rfl)

theorem rawDiagram_region_sheet_lookup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (region : Fin (rawDiagram diagram).regionCount)
    (draftEq : (flattenOpen diagram).regions.get region = .sheet) :
    (rawDiagram diagram).regions region = .sheet := by
  unfold rawDiagram
  dsimp only
  exact (RegionDraft.toConcrete_congr draftEq
    ((flattenOpen_bounded diagram).regions _ (List.get_mem _ region))).trans
      (by rfl)

private def List.SegmentAt (whole segment : List α) (base : Nat) : Prop :=
  ∃ before after, before.length = base ∧
    whole = before ++ segment ++ after

private theorem List.SegmentAt.get
    {whole segment : List α} {base : Nat}
    (allocated : List.SegmentAt whole segment base)
    (index : Fin segment.length) :
    whole.get ⟨base + index.val, by
      rcases allocated with ⟨before, after, beforeLength, rfl⟩
      simp only [List.length_append]
      omega⟩ = segment.get index := by
  rcases allocated with ⟨before, after, beforeLength, rfl⟩
  subst base
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simp)]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem List.SegmentAt.index_lt
    {whole segment : List α} {base : Nat}
    (allocated : List.SegmentAt whole segment base)
    (index : Fin segment.length) :
    base + index.val < whole.length := by
  rcases allocated with ⟨before, after, beforeLength, rfl⟩
  simp only [List.length_append]
  omega

private theorem List.SegmentAt.end_le
    {whole segment : List α} {base : Nat}
    (allocated : List.SegmentAt whole segment base) :
    base + segment.length ≤ whole.length := by
  rcases allocated with ⟨before, after, beforeLength, rfl⟩
  simp only [List.length_append]
  omega

private theorem List.SegmentAt.left
    {whole left right : List α} {base : Nat}
    (allocated : List.SegmentAt whole (left ++ right) base) :
    List.SegmentAt whole left base := by
  rcases allocated with ⟨before, after, beforeLength, wholeEq⟩
  exact ⟨before, right ++ after, beforeLength, by
    simpa only [List.append_assoc] using wholeEq⟩

private theorem List.SegmentAt.right
    {whole left right : List α} {base : Nat}
    (allocated : List.SegmentAt whole (left ++ right) base) :
    List.SegmentAt whole right (base + left.length) := by
  rcases allocated with ⟨before, after, beforeLength, wholeEq⟩
  refine ⟨before ++ left, after, ?_, ?_⟩
  · simp only [List.length_append, beforeLength]
  · simpa only [List.append_assoc] using wholeEq

private theorem List.SegmentAt.tail
    {whole : List α} {head : α} {tail : List α} {base : Nat}
    (allocated : List.SegmentAt whole (head :: tail) base) :
    List.SegmentAt whole tail (base + 1) := by
  have right := allocated.right (left := [head]) (right := tail)
  simpa using right

private structure Flat.SegmentAt
    (whole segment : Flat) (regionBase nodeBase wireBase : Nat) : Prop where
  regions : List.SegmentAt whole.regions segment.regions regionBase
  nodes : List.SegmentAt whole.nodes segment.nodes nodeBase
  wireScopes : List.SegmentAt whole.wireScopes segment.wireScopes wireBase

private theorem Flat.SegmentAt.left
    {whole left right : Flat} {regionBase nodeBase wireBase : Nat}
    (allocated : Flat.SegmentAt whole (left.append right)
      regionBase nodeBase wireBase) :
    Flat.SegmentAt whole left regionBase nodeBase wireBase := by
  exact {
    regions := allocated.regions.left
    nodes := allocated.nodes.left
    wireScopes := allocated.wireScopes.left
  }

private theorem Flat.SegmentAt.right
    {whole left right : Flat} {regionBase nodeBase wireBase : Nat}
    (allocated : Flat.SegmentAt whole (left.append right)
      regionBase nodeBase wireBase) :
    Flat.SegmentAt whole right
      (regionBase + left.regions.length)
      (nodeBase + left.nodes.length)
      (wireBase + left.wireScopes.length) := by
  exact {
    regions := allocated.regions.right
    nodes := allocated.nodes.right
    wireScopes := allocated.wireScopes.right
  }


inductive OccurrenceDraft
  | node (index : Nat)
  | child (index : Nat)
  deriving DecidableEq

def occurrenceDrafts :
    Nat → Nat → ItemSeq wires rels → List OccurrenceDraft
  | _, _, .nil => []
  | regionBase, nodeBase, .cons head tail =>
      (match head with
        | .atom _ _ => .node nodeBase
        | .identity _ _ => .node nodeBase
        | .cut _ => .child regionBase
        | .bubble _ _ => .child regionBase) ::
      occurrenceDrafts
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes) tail

@[simp] theorem occurrenceDrafts_length :
    (items : ItemSeq wires rels) →
    (occurrenceDrafts regionBase nodeBase items).length = items.length
  | .nil => rfl
  | .cons head tail => by
      simp [occurrenceDrafts, ItemSeq.length, occurrenceDrafts_length]

def OccurrenceDraft.After
    (regionBase nodeBase : Nat) : OccurrenceDraft → Prop
  | .node index => nodeBase ≤ index
  | .child index => regionBase ≤ index

theorem occurrenceDrafts_after :
    (items : ItemSeq wires rels) →
    ∀ draft, draft ∈ occurrenceDrafts regionBase nodeBase items →
      draft.After regionBase nodeBase
  | .nil => by simp [occurrenceDrafts]
  | .cons head tail => by
      intro draft member
      simp only [occurrenceDrafts, List.mem_cons] at member
      rcases member with rfl | member
      · cases head <;> simp [OccurrenceDraft.After]
      · have result := occurrenceDrafts_after
          (regionBase := regionBase + (itemCounts head).regions)
          (nodeBase := nodeBase + (itemCounts head).nodes) tail draft member
        cases draft <;> simp only [OccurrenceDraft.After] at result ⊢ <;> omega

def OccurrenceDraft.Before
    (regionLimit nodeLimit : Nat) : OccurrenceDraft → Prop
  | .node index => index < nodeLimit
  | .child index => index < regionLimit

theorem occurrenceDrafts_before :
    (items : ItemSeq wires rels) →
    ∀ draft, draft ∈ occurrenceDrafts regionBase nodeBase items →
      draft.Before
        (regionBase + (itemSeqCounts items).regions)
        (nodeBase + (itemSeqCounts items).nodes)
  | .nil => by simp [occurrenceDrafts]
  | .cons head tail => by
      intro draft member
      simp only [occurrenceDrafts, List.mem_cons] at member
      rcases member with rfl | member
      · cases head with
        | atom relation arguments =>
            simp only [OccurrenceDraft.Before, itemSeqCounts, Counts.add,
              itemCounts]
            omega
        | identity arity arguments =>
            simp only [OccurrenceDraft.Before, itemSeqCounts, Counts.add,
              itemCounts]
            omega
        | cut body =>
            have positive := regionCounts_regions_pos body
            simp only [OccurrenceDraft.Before, itemSeqCounts, Counts.add,
              itemCounts]
            omega
        | bubble arity body =>
            have positive := regionCounts_regions_pos body
            simp only [OccurrenceDraft.Before, itemSeqCounts, Counts.add,
              itemCounts]
            omega
      · have result := occurrenceDrafts_before
          (regionBase := regionBase + (itemCounts head).regions)
          (nodeBase := nodeBase + (itemCounts head).nodes) tail draft member
        cases draft <;>
          simp only [OccurrenceDraft.Before] at result ⊢ <;>
          simp only [itemSeqCounts, Counts.add] <;> omega

theorem occurrenceDrafts_nodup :
    (items : ItemSeq wires rels) →
    (occurrenceDrafts regionBase nodeBase items).Nodup
  | .nil => by simp [occurrenceDrafts]
  | .cons head tail => by
      change ((match head with
        | .atom _ _ => .node nodeBase
        | .identity _ _ => .node nodeBase
        | .cut _ => .child regionBase
        | .bubble _ _ => .child regionBase) ::
        occurrenceDrafts
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes) tail).Nodup
      rw [List.nodup_cons]
      constructor
      · intro member
        have after := occurrenceDrafts_after
          (regionBase := regionBase + (itemCounts head).regions)
          (nodeBase := nodeBase + (itemCounts head).nodes) tail _ member
        cases head with
        | atom relation arguments =>
            simp [itemCounts, OccurrenceDraft.After] at after
            omega
        | identity arity arguments =>
            simp [itemCounts, OccurrenceDraft.After] at after
            omega
        | cut body =>
            cases body
            simp [itemCounts, regionCounts, OccurrenceDraft.After] at after
            omega
        | bubble arity body =>
            cases body
            simp [itemCounts, regionCounts, OccurrenceDraft.After] at after
            omega
      · exact occurrenceDrafts_nodup tail

def OccurrenceDraft.Bounded
    (regionCount nodeCount : Nat) : OccurrenceDraft → Prop
  | .node index => index < nodeCount
  | .child index => index < regionCount

private theorem occurrenceDrafts_bounded
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount) (binders : BinderMap rels)
    (items : ItemSeq wireCount rels)
    (allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItems currentRegion regionBase nodeBase wireBase
        wires binders items) regionBase nodeBase wireBase) :
    ∀ draft, draft ∈ occurrenceDrafts regionBase nodeBase items →
      draft.Bounded (rawDiagram diagram).regionCount
        (rawDiagram diagram).nodeCount := by
  intro draft member
  have before := occurrenceDrafts_before items draft member
  have lengths := flattenItems_lengths currentRegion regionBase nodeBase
    wireBase wires binders items
  have regionsEnd := allocated.regions.end_le
  have nodesEnd := allocated.nodes.end_le
  change regionBase +
      (flattenItems currentRegion regionBase nodeBase wireBase
        wires binders items).regions.length ≤
      (rawDiagram diagram).regionCount at regionsEnd
  change nodeBase +
      (flattenItems currentRegion regionBase nodeBase wireBase
        wires binders items).nodes.length ≤
      (rawDiagram diagram).nodeCount at nodesEnd
  rw [lengths.1] at regionsEnd
  rw [lengths.2.1] at nodesEnd
  cases draft <;> simp only [OccurrenceDraft.Before,
    OccurrenceDraft.Bounded] at before ⊢ <;> omega

def OccurrenceDraft.toConcrete
    {d : Diagram}
    (draft : OccurrenceDraft)
    (bounded : draft.Bounded d.regionCount d.nodeCount) :
    Elaboration.LocalOccurrence d.regionCount d.nodeCount :=
  match draft with
  | .node index => .node ⟨index, bounded⟩
  | .child index => .child ⟨index, bounded⟩

def OccurrenceDraft.OwnedBy
    (d : Diagram) (region : Fin d.regionCount)
    (draft : OccurrenceDraft)
    (bounded : draft.Bounded d.regionCount d.nodeCount) : Prop :=
  match draft with
  | .node index => (d.nodes ⟨index, bounded⟩).region = region
  | .child index => (d.regions ⟨index, bounded⟩).parent? = some region

private theorem occurrenceDrafts_owned
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current : Fin (rawDiagram diagram).regionCount)
    (regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount) (binders : BinderMap rels) :
    (items : ItemSeq wireCount rels) →
    (allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItems current.val regionBase nodeBase wireBase
        wires binders items) regionBase nodeBase wireBase) →
    ∀ draft (member : draft ∈ occurrenceDrafts regionBase nodeBase items),
      draft.OwnedBy (rawDiagram diagram) current
        (occurrenceDrafts_bounded diagram current.val regionBase nodeBase
          wireBase wires binders items allocated draft member)
  | .nil, allocated => by simp [occurrenceDrafts]
  | .cons head tail, allocated => by
      let headFlat := flattenItem current.val regionBase nodeBase wireBase
        wires binders head
      let tailFlat := flattenItems current.val
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders tail
      have flatEq : flattenItems current.val regionBase nodeBase wireBase
          wires binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt (flattenOpen diagram)
          (headFlat.append tailFlat) regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths current.val regionBase nodeBase
        wireBase wires binders head
      have headRegionsLength : headFlat.regions.length =
          (itemCounts head).regions := headLengths.1
      have headNodesLength : headFlat.nodes.length =
          (itemCounts head).nodes := headLengths.2.1
      have headWiresLength : headFlat.wireScopes.length =
          (itemCounts head).wires := headLengths.2.2
      rw [headRegionsLength, headNodesLength, headWiresLength] at tailAllocated
      intro draft member
      simp only [occurrenceDrafts, List.mem_cons] at member
      rcases member with rfl | member
      · cases head with
        | atom relation arguments =>
            have nodeNonempty : 0 < headFlat.nodes.length := by
              simp [headFlat, flattenItem]
            let node : Fin (rawDiagram diagram).nodeCount :=
              ⟨nodeBase, headAllocated.nodes.index_lt ⟨0, nodeNonempty⟩⟩
            have draftEq : (flattenOpen diagram).nodes.get node =
                .atom current.val (binders _ relation) _
                  (wires ∘ arguments) := by
              have lookup := headAllocated.nodes.get ⟨0, nodeNonempty⟩
              simpa [node, headFlat, flattenItem] using lookup
            obtain ⟨concreteRegion, concreteBinder, nodeEq, regionVal,
                binderVal⟩ := rawDiagram_node_atom_lookup diagram node
              current.val (binders _ relation) _ (wires ∘ arguments) draftEq
            simp only [OccurrenceDraft.OwnedBy]
            have concreteRegionEq : concreteRegion = current := Fin.ext regionVal
            change ((rawDiagram diagram).nodes node).region = current
            rw [nodeEq]
            exact concreteRegionEq
        | identity arity arguments =>
            have nodeNonempty : 0 < headFlat.nodes.length := by
              simp [headFlat, flattenItem]
            let node : Fin (rawDiagram diagram).nodeCount :=
              ⟨nodeBase, headAllocated.nodes.index_lt ⟨0, nodeNonempty⟩⟩
            have draftEq : (flattenOpen diagram).nodes.get node =
                .identity current.val arity (wires ∘ arguments) := by
              have lookup := headAllocated.nodes.get ⟨0, nodeNonempty⟩
              simpa [node, headFlat, flattenItem] using lookup
            obtain ⟨concreteRegion, nodeEq, regionVal⟩ :=
              rawDiagram_node_identity_lookup diagram node current.val arity
                (wires ∘ arguments) draftEq
            simp only [OccurrenceDraft.OwnedBy]
            have concreteRegionEq : concreteRegion = current := Fin.ext regionVal
            change ((rawDiagram diagram).nodes node).region = current
            rw [nodeEq]
            exact concreteRegionEq
        | cut body =>
            have regionNonempty : 0 < headFlat.regions.length := by
              simp [headFlat, flattenItem, flattenRegion_regions_pos]
            let child : Fin (rawDiagram diagram).regionCount :=
              ⟨regionBase,
                headAllocated.regions.index_lt ⟨0, regionNonempty⟩⟩
            have draftEq : (flattenOpen diagram).regions.get child =
                .cut current.val := by
              have lookup := headAllocated.regions.get ⟨0, regionNonempty⟩
              exact lookup.trans (by
                simpa [headFlat, flattenItem] using
                  flattenRegion_regions_get_zero (.cut current.val)
                    regionBase nodeBase wireBase wires binders body)
            obtain ⟨concreteParent, childEq, parentVal⟩ :=
              rawDiagram_region_cut_lookup diagram child current.val draftEq
            simp only [OccurrenceDraft.OwnedBy]
            have concreteParentEq : concreteParent = current := Fin.ext parentVal
            simpa [child, concreteParentEq] using congrArg CRegion.parent? childEq
        | bubble arity body =>
            have regionNonempty : 0 < headFlat.regions.length := by
              simp [headFlat, flattenItem, flattenRegion_regions_pos]
            let child : Fin (rawDiagram diagram).regionCount :=
              ⟨regionBase,
                headAllocated.regions.index_lt ⟨0, regionNonempty⟩⟩
            have draftEq : (flattenOpen diagram).regions.get child =
                .bubble current.val arity := by
              have lookup := headAllocated.regions.get ⟨0, regionNonempty⟩
              exact lookup.trans (by
                simpa [headFlat, flattenItem] using
                  flattenRegion_regions_get_zero (.bubble current.val arity)
                    regionBase nodeBase wireBase wires
                    (binders.push regionBase) body)
            obtain ⟨concreteParent, childEq, parentVal⟩ :=
              rawDiagram_region_bubble_lookup diagram child current.val arity
                draftEq
            simp only [OccurrenceDraft.OwnedBy]
            have concreteParentEq : concreteParent = current := Fin.ext parentVal
            simpa [child, concreteParentEq] using congrArg CRegion.parent? childEq
      · exact occurrenceDrafts_owned diagram current
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wires binders tail
          tailAllocated draft member

def realizeOccurrenceDrafts
    {d : Diagram}
    (drafts : List OccurrenceDraft)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount) :
    List (Elaboration.LocalOccurrence d.regionCount d.nodeCount) :=
  drafts.pmap (@OccurrenceDraft.toConcrete d) bounded

private theorem realizeOccurrenceDrafts_mem_localOccurrences
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current : Fin (rawDiagram diagram).regionCount)
    (regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount) (binders : BinderMap rels)
    (items : ItemSeq wireCount rels)
    (allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItems current.val regionBase nodeBase wireBase
        wires binders items) regionBase nodeBase wireBase) :
    ∀ occurrence,
      occurrence ∈ realizeOccurrenceDrafts
        (d := rawDiagram diagram) (occurrenceDrafts regionBase nodeBase items)
        (occurrenceDrafts_bounded diagram current.val regionBase nodeBase
          wireBase wires binders items allocated) →
      occurrence ∈ Elaboration.localOccurrences (rawDiagram diagram) current := by
  intro occurrence member
  unfold realizeOccurrenceDrafts at member
  rw [List.mem_pmap] at member
  obtain ⟨draft, draftMember, occurrenceEq⟩ := member
  subst occurrence
  have owned := occurrenceDrafts_owned diagram current regionBase nodeBase
    wireBase wires binders items allocated draft draftMember
  cases draft with
  | node index =>
      apply (Elaboration.mem_localOccurrences_node
        (rawDiagram diagram) current _).2
      exact owned
  | child index =>
      apply (Elaboration.mem_localOccurrences_child
        (rawDiagram diagram) current _).2
      exact owned

@[simp] theorem realizeOccurrenceDrafts_length
    {d : Diagram}
    (drafts : List OccurrenceDraft)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount) :
    (realizeOccurrenceDrafts drafts bounded).length = drafts.length := by
  simp [realizeOccurrenceDrafts]

theorem OccurrenceDraft.toConcrete_injective
    {d : Diagram}
    {drafts : List OccurrenceDraft}
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount) :
    ∀ first (hfirst : first ∈ drafts) second (hsecond : second ∈ drafts),
      first ≠ second →
      first.toConcrete (bounded first hfirst) ≠
        second.toConcrete (bounded second hsecond) := by
  intro first hfirst second hsecond different equal
  cases first <;> cases second <;> simp_all [OccurrenceDraft.toConcrete]

theorem realizeOccurrenceDrafts_nodup
    {d : Diagram}
    (drafts : List OccurrenceDraft)
    (draftNodup : drafts.Nodup)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount) :
    (realizeOccurrenceDrafts drafts bounded).Nodup := by
  induction drafts with
  | nil => simp [realizeOccurrenceDrafts]
  | cons head tail ih =>
      simp only [List.nodup_cons] at draftNodup
      simp only [realizeOccurrenceDrafts, List.pmap]
      rw [List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_pmap] at member
        obtain ⟨draft, draftMember, equal⟩ := member
        have different : head ≠ draft := by
          intro equality
          subst draft
          exact draftNodup.1 draftMember
        exact (OccurrenceDraft.toConcrete_injective bounded head (by simp)
          draft (by simp [draftMember]) different) equal.symm
      · simpa only [realizeOccurrenceDrafts] using
          ih draftNodup.2 (fun draft member =>
            bounded draft (by simp [member]))

noncomputable def localOccurrenceDraftEquiv
    {d : Diagram} (region : Fin d.regionCount)
    (drafts : List OccurrenceDraft)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount)
    (draftNodup : drafts.Nodup)
    (mem_iff : ∀ occurrence,
      occurrence ∈ Elaboration.localOccurrences d region ↔
        occurrence ∈ realizeOccurrenceDrafts drafts bounded) :
    FiniteEquiv (Fin drafts.length)
      (Fin (Elaboration.localOccurrences d region).length) :=
  (FiniteEquiv.finCast
      (realizeOccurrenceDrafts_length drafts bounded).symm).trans
    (FiniteEquiv.restrictLists
      (FiniteEquiv.refl
      (Elaboration.LocalOccurrence d.regionCount d.nodeCount))
      (realizeOccurrenceDrafts drafts bounded)
      (Elaboration.localOccurrences d region)
      (realizeOccurrenceDrafts_nodup drafts draftNodup bounded)
      (Elaboration.localOccurrences_nodup d region)
      (fun occurrence => by
        simp only [FiniteEquiv.refl_apply]
        exact mem_iff occurrence))

theorem localOccurrenceDraftEquiv_lookup
    {d : Diagram} (region : Fin d.regionCount)
    (drafts : List OccurrenceDraft)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount)
    (draftNodup : drafts.Nodup)
    (mem_iff : ∀ occurrence,
      occurrence ∈ Elaboration.localOccurrences d region ↔
        occurrence ∈ realizeOccurrenceDrafts drafts bounded)
    (index : Fin drafts.length) :
    (Elaboration.localOccurrences d region).get
      (localOccurrenceDraftEquiv region drafts bounded draftNodup mem_iff index) =
      (realizeOccurrenceDrafts drafts bounded).get
        ⟨index.val, by
          rw [realizeOccurrenceDrafts_length drafts bounded]
          exact index.isLt⟩ := by
  unfold localOccurrenceDraftEquiv
  rw [FiniteEquiv.trans_apply]
  rw [FiniteEquiv.restrictLists_spec]
  rfl

def wireSlice (d : Diagram) (wireBase localWires : Nat)
    (bounded : wireBase + localWires ≤ d.wireCount) :
    List (Fin d.wireCount) :=
  List.ofFn fun localIndex : Fin localWires =>
    ⟨wireBase + localIndex.val, by omega⟩

@[simp] theorem wireSlice_length
    (bounded : wireBase + localWires ≤ d.wireCount) :
    (wireSlice d wireBase localWires bounded).length = localWires := by
  simp [wireSlice]

@[simp] theorem wireSlice_get
    (bounded : wireBase + localWires ≤ d.wireCount)
    (index : Fin (wireSlice d wireBase localWires bounded).length) :
    (wireSlice d wireBase localWires bounded).get index =
      ⟨wireBase + index.val, by
        have := index.isLt
        simp only [wireSlice_length] at this
        omega⟩ := by
  simp [wireSlice]

theorem wireSlice_nodup
    (bounded : wireBase + localWires ≤ d.wireCount) :
    (wireSlice d wireBase localWires bounded).Nodup := by
  have functionInjective : Function.Injective
      (fun localIndex : Fin localWires =>
        (⟨wireBase + localIndex.val, by omega⟩ : Fin d.wireCount)) := by
    intro i j equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    simp only at values
    omega
  have listEq : wireSlice d wireBase localWires bounded =
      (allFin localWires).map (fun localIndex : Fin localWires =>
        (⟨wireBase + localIndex.val, by omega⟩ : Fin d.wireCount)) := by
    rw [wireSlice, allFin_eq_finRange, List.finRange, List.map_ofFn]
    congr
  rw [listEq]
  exact (allFin_nodup localWires).map _
    (fun first second distinct equal => distinct (functionInjective equal))

noncomputable def exactScopeSliceEquiv
    (d : Diagram) (region : Fin d.regionCount)
    (wireBase localWires : Nat)
    (bounded : wireBase + localWires ≤ d.wireCount)
    (mem_iff : ∀ wire,
      wire ∈ Elaboration.exactScopeWires d region ↔
        wire ∈ wireSlice d wireBase localWires bounded) :
    FiniteEquiv (Fin localWires)
      (Fin (Elaboration.exactScopeWires d region).length) :=
  (FiniteEquiv.finCast (wireSlice_length bounded).symm).trans
    (FiniteEquiv.restrictLists (FiniteEquiv.refl (Fin d.wireCount))
      (wireSlice d wireBase localWires bounded)
      (Elaboration.exactScopeWires d region)
      (wireSlice_nodup bounded)
      (Elaboration.exactScopeWires_nodup d region)
      (fun wire => by
        simp only [FiniteEquiv.refl_apply]
        exact mem_iff wire))

theorem exactScopeSliceEquiv_lookup
    (d : Diagram) (region : Fin d.regionCount)
    (wireBase localWires : Nat)
    (bounded : wireBase + localWires ≤ d.wireCount)
    (mem_iff : ∀ wire,
      wire ∈ Elaboration.exactScopeWires d region ↔
        wire ∈ wireSlice d wireBase localWires bounded)
    (index : Fin localWires) :
    (Elaboration.exactScopeWires d region).get
      (exactScopeSliceEquiv d region wireBase localWires bounded mem_iff index) =
      ⟨wireBase + index.val, by omega⟩ := by
  unfold exactScopeSliceEquiv
  rw [FiniteEquiv.trans_apply]
  rw [FiniteEquiv.restrictLists_spec]
  simp [FiniteEquiv.finCast, wireSlice]

private def RegionDraft.parentIndex? : RegionDraft → Option Nat
  | .sheet => none
  | .cut parent | .bubble parent _ => some parent

private def NodeDraft.ownerIndex : NodeDraft → Nat
  | .atom region _ _ _ | .identity region _ _ => region

private def ParentBand
    (direct lower upper : Nat) : RegionDraft → Prop
  | .sheet => True
  | .cut parent | .bubble parent _ =>
      parent = direct ∨ (lower ≤ parent ∧ parent < upper)

private def NodeBand
    (direct lower upper : Nat) : NodeDraft → Prop
  | .atom region _ _ _ | .identity region _ _ =>
      region = direct ∨ (lower ≤ region ∧ region < upper)

private theorem ParentBand.parentIndex
    (band : ParentBand direct lower upper draft)
    (parentEq : draft.parentIndex? = some parent) :
    parent = direct ∨ (lower ≤ parent ∧ parent < upper) := by
  cases draft <;> simp_all [RegionDraft.parentIndex?, ParentBand]

private theorem NodeBand.ownerIndex
    (band : NodeBand direct lower upper draft) :
    draft.ownerIndex = direct ∨
      (lower ≤ draft.ownerIndex ∧ draft.ownerIndex < upper) := by
  cases draft <;> exact band

private structure OwnerBand
    (flat : Flat) (direct lower upper : Nat) : Prop where
  regions : ∀ draft, draft ∈ flat.regions →
    ParentBand direct lower upper draft
  nodes : ∀ draft, draft ∈ flat.nodes →
    NodeBand direct lower upper draft
  wireScopes : ∀ scope, scope ∈ flat.wireScopes →
    lower ≤ scope ∧ scope < upper

private def flattenOne
    (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels) : Item wireCount rels → Flat
  | .atom relation arguments =>
      ⟨[], [.atom current (binders _ relation) _ (wires ∘ arguments)], []⟩
  | .identity arity arguments =>
      ⟨[], [.identity current arity (wires ∘ arguments)], []⟩
  | .cut body =>
      flattenRegion (.cut current) regionBase nodeBase wireBase
        wires binders body
  | .bubble arity body =>
      flattenRegion (.bubble current arity) regionBase nodeBase wireBase
        wires (binders.push regionBase) body

private theorem OwnerBand.widen
    (band : OwnerBand flat direct lower middle)
    (middleLe : middle ≤ upper) :
    OwnerBand flat direct lower upper := by
  exact {
    regions := by
      intro draft member
      have result := band.regions draft member
      cases draft with
      | sheet => trivial
      | cut parent | bubble parent arity =>
          rcases result with rfl | result
          · exact Or.inl rfl
          · exact Or.inr ⟨result.1, by omega⟩
    nodes := by
      intro draft member
      have result := band.nodes draft member
      cases draft with
      | atom region binder arity arguments | identity region arity arguments =>
          rcases result with rfl | result
          · exact Or.inl rfl
          · exact Or.inr ⟨result.1, by omega⟩
    wireScopes := by
      intro scope member
      have result := band.wireScopes scope member
      exact ⟨result.1, by omega⟩
  }

private theorem OwnerBand.raiseLower
    (band : OwnerBand flat direct middle upper)
    (lowerLe : lower ≤ middle) :
    OwnerBand flat direct lower upper := by
  exact {
    regions := by
      intro draft member
      have result := band.regions draft member
      cases draft with
      | sheet => trivial
      | cut parent | bubble parent arity =>
          rcases result with rfl | result
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, result.2⟩
    nodes := by
      intro draft member
      have result := band.nodes draft member
      cases draft with
      | atom region binder arity arguments | identity region arity arguments =>
          rcases result with rfl | result
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, result.2⟩
    wireScopes := by
      intro scope member
      have result := band.wireScopes scope member
      exact ⟨by omega, result.2⟩
  }

private theorem OwnerBand.append
    (leftBand : OwnerBand left direct lower middle)
    (rightBand : OwnerBand right direct middle upper)
    (lowerLeMiddle : lower ≤ middle)
    (middleLeUpper : middle ≤ upper) :
    OwnerBand (Flat.append left right) direct lower upper := by
  exact {
    regions := by
      intro draft member
      rcases List.mem_append.mp member with member | member
      · exact (leftBand.widen middleLeUpper).regions draft member
      · exact (rightBand.raiseLower lowerLeMiddle).regions draft member
    nodes := by
      intro draft member
      rcases List.mem_append.mp member with member | member
      · exact (leftBand.widen middleLeUpper).nodes draft member
      · exact (rightBand.raiseLower lowerLeMiddle).nodes draft member
    wireScopes := by
      intro scope member
      rcases List.mem_append.mp member with member | member
      · exact (leftBand.widen middleLeUpper).wireScopes scope member
      · exact (rightBand.raiseLower lowerLeMiddle).wireScopes scope member
  }

private def RegionOwnerMotive
    (wireCount : Nat) (rels : RelCtx)
    (region : Region wireCount rels) : Prop :=
  ∀ (regionKind : RegionDraft)
    (direct regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap wireCount)
    (binders : BinderMap rels),
    ParentBand direct regionBase
      (regionBase + (regionCounts region).regions) regionKind →
    OwnerBand (flattenRegion regionKind regionBase nodeBase wireBase
      outerWires binders region) direct regionBase
        (regionBase + (regionCounts region).regions)

private def ItemOwnerMotive
    (wireCount : Nat) (rels : RelCtx)
    (item : Item wireCount rels) : Prop :=
  ∀ (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels),
    current < regionBase →
    OwnerBand (flattenOne current regionBase nodeBase wireBase wires binders
      item) current regionBase
        (regionBase + (itemCounts item).regions)

private def ItemsOwnerMotive
    (wireCount : Nat) (rels : RelCtx)
    (items : ItemSeq wireCount rels) : Prop :=
  ∀ (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels),
    current < regionBase →
    OwnerBand (flattenItems current regionBase nodeBase wireBase wires binders
      items) current regionBase
        (regionBase + (itemSeqCounts items).regions)

private theorem flattenItems_ownerBand_core
    (items : ItemSeq wireCount rels) :
    ItemsOwnerMotive wireCount rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionOwnerMotive)
      (motive_2 := ItemOwnerMotive)
      (motive_3 := ItemsOwnerMotive)
  case mk =>
      intro sourceWires sourceRels localWires nested nestedBand
      intro regionKind direct regionBase nodeBase wireBase outerWires binders
        kindBand
      have nestedResult := nestedBand regionBase (regionBase + 1) nodeBase
        (wireBase + localWires)
        (outerWires.extend wireBase localWires) binders (by omega)
      exact {
        regions := by
          intro draft member
          simp only [flattenRegion, List.mem_cons] at member
          rcases member with rfl | member
          · exact kindBand
          · have result := nestedResult.regions draft member
            cases draft with
            | sheet => trivial
            | cut parent | bubble parent arity =>
                rcases result with rfl | result
                · exact Or.inr (by
                    simp only [regionCounts]
                    constructor <;> omega)
                · exact Or.inr (by
                    simp only [regionCounts] at result ⊢
                    constructor <;> omega)
        nodes := by
          intro draft member
          have result := nestedResult.nodes draft (by
            simpa only [flattenRegion] using member)
          cases draft with
          | atom region binder arity arguments | identity region arity arguments =>
              rcases result with rfl | result
              · exact Or.inr (by
                  simp only [regionCounts]
                  constructor <;> omega)
              · exact Or.inr (by
                  simp only [regionCounts] at result ⊢
                  constructor <;> omega)
        wireScopes := by
          intro scope member
          simp only [flattenRegion, List.mem_append, List.mem_replicate] at member
          rcases member with ⟨_, rfl⟩ | member
          · simp only [regionCounts]
            constructor <;> omega
          · have result := nestedResult.wireScopes scope member
            simp only [regionCounts] at result ⊢
            constructor <;> omega
      }
  case atom =>
      intro sourceRels nodeArity sourceWires relation arguments
      intro current regionBase nodeBase wireBase wires binders currentLt
      exact {
        regions := by simp [flattenOne]
        nodes := by
          intro draft member
          simp only [flattenOne, List.mem_singleton] at member
          subst draft
          exact Or.inl rfl
        wireScopes := by simp [flattenOne]
      }
  case identity =>
      intro sourceWires sourceRels nodeArity arguments
      intro current regionBase nodeBase wireBase wires binders currentLt
      exact {
        regions := by simp [flattenOne]
        nodes := by
          intro draft member
          simp only [flattenOne, List.mem_singleton] at member
          subst draft
          exact Or.inl rfl
        wireScopes := by simp [flattenOne]
      }
  case cut =>
      intro sourceWires sourceRels body bodyBand
      intro current regionBase nodeBase wireBase wires binders currentLt
      simpa only [flattenOne, itemCounts] using
        bodyBand (.cut current) current regionBase nodeBase wireBase wires
          binders (Or.inl rfl)
  case bubble =>
      intro sourceWires sourceRels binderArity body bodyBand
      intro current regionBase nodeBase wireBase wires binders currentLt
      simpa only [flattenOne, itemCounts] using
        bodyBand (.bubble current binderArity) current regionBase nodeBase
          wireBase wires (binders.push regionBase) (Or.inl rfl)
  case nil =>
      intro sourceWires sourceRels
      intro current regionBase nodeBase wireBase wires binders currentLt
      exact {
        regions := by simp [flattenItems, Flat.empty]
        nodes := by simp [flattenItems, Flat.empty]
        wireScopes := by simp [flattenItems, Flat.empty]
      }
  case cons =>
      intro sourceWires sourceRels head tail headBand tailBand
      intro current regionBase nodeBase wireBase wires binders currentLt
      have left := headBand current regionBase nodeBase wireBase wires binders
        currentLt
      have right := tailBand current
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders (by omega)
      have joined := OwnerBand.append left right (by omega) (by omega)
      cases head <;>
        simpa [flattenItems, flattenOne, itemSeqCounts, Counts.add,
          Nat.add_assoc] using joined

private theorem flattenItems_ownerBand
    (items : ItemSeq wireCount rels)
    (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels)
    (currentLt : current < regionBase) :
    OwnerBand (flattenItems current regionBase nodeBase wireBase wires binders
      items) current regionBase
        (regionBase + (itemSeqCounts items).regions) :=
  flattenItems_ownerBand_core items current regionBase nodeBase wireBase
    wires binders currentLt

private def ItemsNodeFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (items : ItemSeq wireCount rels) : Prop :=
  ∀ (whole : Flat) (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount) (binders : BinderMap rels),
    Flat.SegmentAt whole
      (flattenItems current regionBase nodeBase wireBase wires binders items)
      regionBase nodeBase wireBase →
    current < regionBase →
    ∀ node : Fin whole.nodes.length,
      (whole.nodes.get node).ownerIndex = current →
      nodeBase ≤ node.val →
      node.val < nodeBase + (itemSeqCounts items).nodes →
      .node node.val ∈ occurrenceDrafts regionBase nodeBase items

private def RegionNodeFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (_region : Region wireCount rels) : Prop := True

private def ItemNodeFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (_item : Item wireCount rels) : Prop := True

private theorem flattenItems_nodeFiber (items : ItemSeq wireCount rels) :
    ItemsNodeFiberMotive wireCount rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionNodeFiberMotive)
      (motive_2 := ItemNodeFiberMotive)
      (motive_3 := ItemsNodeFiberMotive)
  case mk => simp [RegionNodeFiberMotive]
  case atom => simp [ItemNodeFiberMotive]
  case identity => simp [ItemNodeFiberMotive]
  case cut => simp [RegionNodeFiberMotive, ItemNodeFiberMotive]
  case bubble => simp [RegionNodeFiberMotive, ItemNodeFiberMotive]
  case nil =>
      intro sourceWires sourceRels whole current regionBase nodeBase wireBase
        wires binders allocated currentLt node owner lower upper
      simp only [itemSeqCounts] at upper
      omega
  case cons =>
      intro sourceWires sourceRels head tail headProof ih
      intro whole current regionBase nodeBase wireBase wires binders allocated
        currentLt node owner lower upper
      let headFlat := flattenItem current regionBase nodeBase wireBase
        wires binders head
      let tailFlat := flattenItems current
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders tail
      have flatEq : flattenItems current regionBase nodeBase wireBase
          wires binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt whole (headFlat.append tailFlat)
          regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths current regionBase nodeBase
        wireBase wires binders head
      have headRegionsLength : headFlat.regions.length =
          (itemCounts head).regions := headLengths.1
      have headNodesLength : headFlat.nodes.length =
          (itemCounts head).nodes := headLengths.2.1
      have headWiresLength : headFlat.wireScopes.length =
          (itemCounts head).wires := headLengths.2.2
      rw [headRegionsLength, headNodesLength, headWiresLength] at tailAllocated
      by_cases inHead : node.val < nodeBase + (itemCounts head).nodes
      · cases head with
        | atom relation arguments =>
            have nodeEq : node.val = nodeBase := by
              simp only [itemCounts] at inHead
              omega
            simp [occurrenceDrafts, nodeEq]
        | identity arity arguments =>
            have nodeEq : node.val = nodeBase := by
              simp only [itemCounts] at inHead
              omega
            simp [occurrenceDrafts, nodeEq]
        | cut body =>
            cases body with
            | mk localWires nested =>
                let nestedFlat := flattenItems regionBase (regionBase + 1)
                  nodeBase (wireBase + localWires)
                  (wires.extend wireBase localWires) binders nested
                have nestedBand := flattenItems_ownerBand nested regionBase
                  (regionBase + 1) nodeBase (wireBase + localWires)
                  (wires.extend wireBase localWires) binders (by omega)
                have nestedLength : nestedFlat.nodes.length =
                    (itemSeqCounts nested).nodes := by
                  exact (flattenItems_lengths regionBase (regionBase + 1)
                    nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires) binders nested).2.1
                have nestedUpper : node.val < nodeBase + nestedFlat.nodes.length := by
                  simpa [itemCounts, regionCounts, nestedFlat, nestedLength]
                    using inHead
                let localIndex : Fin nestedFlat.nodes.length :=
                  ⟨node.val - nodeBase, by omega⟩
                have lookup : whole.nodes.get node =
                    nestedFlat.nodes.get localIndex := by
                  have lookup' := headAllocated.nodes.get localIndex
                  have globalEq :
                      (⟨nodeBase + localIndex.val, by
                        exact headAllocated.nodes.index_lt localIndex⟩ :
                        Fin whole.nodes.length) = node := by
                    apply Fin.ext
                    simp [localIndex]
                    omega
                  rw [globalEq] at lookup'
                  simpa [headFlat, flattenItem, flattenRegion, nestedFlat]
                    using lookup'
                have nestedOwner :
                    (nestedFlat.nodes.get localIndex).ownerIndex = current := by
                  rw [← lookup]
                  exact owner
                have band := (nestedBand.nodes _
                  (List.get_mem nestedFlat.nodes localIndex)).ownerIndex
                rw [nestedOwner] at band
                rcases band with equality | descendant
                · omega
                · omega
        | bubble arity body =>
            cases body with
            | mk localWires nested =>
                let nestedFlat := flattenItems regionBase (regionBase + 1)
                  nodeBase (wireBase + localWires)
                  (wires.extend wireBase localWires)
                  (binders.push regionBase) nested
                have nestedBand := flattenItems_ownerBand nested regionBase
                  (regionBase + 1) nodeBase (wireBase + localWires)
                  (wires.extend wireBase localWires)
                  (binders.push regionBase) (by omega)
                have nestedLength : nestedFlat.nodes.length =
                    (itemSeqCounts nested).nodes := by
                  exact (flattenItems_lengths regionBase (regionBase + 1)
                    nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires)
                    (binders.push regionBase) nested).2.1
                have nestedUpper : node.val < nodeBase + nestedFlat.nodes.length := by
                  simpa [itemCounts, regionCounts, nestedFlat, nestedLength]
                    using inHead
                let localIndex : Fin nestedFlat.nodes.length :=
                  ⟨node.val - nodeBase, by omega⟩
                have lookup : whole.nodes.get node =
                    nestedFlat.nodes.get localIndex := by
                  have lookup' := headAllocated.nodes.get localIndex
                  have globalEq :
                      (⟨nodeBase + localIndex.val, by
                        exact headAllocated.nodes.index_lt localIndex⟩ :
                        Fin whole.nodes.length) = node := by
                    apply Fin.ext
                    simp [localIndex]
                    omega
                  rw [globalEq] at lookup'
                  simpa [headFlat, flattenItem, flattenRegion, nestedFlat]
                    using lookup'
                have nestedOwner :
                    (nestedFlat.nodes.get localIndex).ownerIndex = current := by
                  rw [← lookup]
                  exact owner
                have band := (nestedBand.nodes _
                  (List.get_mem nestedFlat.nodes localIndex)).ownerIndex
                rw [nestedOwner] at band
                rcases band with equality | descendant
                · omega
                · omega
      · have tailLower :
            nodeBase + (itemCounts head).nodes ≤ node.val := by omega
        have tailUpper : node.val <
            nodeBase + (itemCounts head).nodes +
              (itemSeqCounts tail).nodes := by
          simp only [itemSeqCounts, Counts.add] at upper
          omega
        have tailMember := ih whole current
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wires binders tailAllocated
          (by omega) node owner tailLower tailUpper
        simp only [occurrenceDrafts, List.mem_cons]
        exact Or.inr tailMember

private def ItemsChildFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (items : ItemSeq wireCount rels) : Prop :=
  ∀ (whole : Flat) (current regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount) (binders : BinderMap rels),
    Flat.SegmentAt whole
      (flattenItems current regionBase nodeBase wireBase wires binders items)
      regionBase nodeBase wireBase →
    current < regionBase →
    ∀ child : Fin whole.regions.length,
      (whole.regions.get child).parentIndex? = some current →
      regionBase ≤ child.val →
      child.val < regionBase + (itemSeqCounts items).regions →
      .child child.val ∈ occurrenceDrafts regionBase nodeBase items

private def RegionChildFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (_region : Region wireCount rels) : Prop := True

private def ItemChildFiberMotive
    (wireCount : Nat) (rels : RelCtx)
    (_item : Item wireCount rels) : Prop := True

private theorem flattenItems_childFiber (items : ItemSeq wireCount rels) :
    ItemsChildFiberMotive wireCount rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionChildFiberMotive)
      (motive_2 := ItemChildFiberMotive)
      (motive_3 := ItemsChildFiberMotive)
  case mk => simp [RegionChildFiberMotive]
  case atom => simp [ItemChildFiberMotive]
  case identity => simp [ItemChildFiberMotive]
  case cut => simp [RegionChildFiberMotive, ItemChildFiberMotive]
  case bubble => simp [RegionChildFiberMotive, ItemChildFiberMotive]
  case nil =>
      intro sourceWires sourceRels whole current regionBase nodeBase wireBase
        wires binders allocated currentLt child parent lower upper
      simp only [itemSeqCounts] at upper
      omega
  case cons =>
      intro sourceWires sourceRels head tail headProof ih
      intro whole current regionBase nodeBase wireBase wires binders allocated
        currentLt child parent lower upper
      let headFlat := flattenItem current regionBase nodeBase wireBase
        wires binders head
      let tailFlat := flattenItems current
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders tail
      have flatEq : flattenItems current regionBase nodeBase wireBase
          wires binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt whole (headFlat.append tailFlat)
          regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths current regionBase nodeBase
        wireBase wires binders head
      have headRegionsLength : headFlat.regions.length =
          (itemCounts head).regions := headLengths.1
      have headNodesLength : headFlat.nodes.length =
          (itemCounts head).nodes := headLengths.2.1
      have headWiresLength : headFlat.wireScopes.length =
          (itemCounts head).wires := headLengths.2.2
      rw [headRegionsLength, headNodesLength, headWiresLength] at tailAllocated
      by_cases inHead : child.val < regionBase + (itemCounts head).regions
      · cases head with
        | atom relation arguments =>
            simp only [itemCounts] at inHead
            omega
        | identity arity arguments =>
            simp only [itemCounts] at inHead
            omega
        | cut body =>
            cases body with
            | mk localWires nested =>
                by_cases direct : child.val = regionBase
                · simp [occurrenceDrafts, direct]
                · let nestedFlat := flattenItems regionBase
                    (regionBase + 1) nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires) binders nested
                  have nestedBand := flattenItems_ownerBand nested regionBase
                    (regionBase + 1) nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires) binders (by omega)
                  have nestedLength : nestedFlat.regions.length =
                      (itemSeqCounts nested).regions := by
                    exact (flattenItems_lengths regionBase (regionBase + 1)
                      nodeBase (wireBase + localWires)
                      (wires.extend wireBase localWires) binders nested).1
                  have nestedUpper : child.val <
                      regionBase + 1 + nestedFlat.regions.length := by
                    rw [nestedLength]
                    simp only [itemCounts, regionCounts] at inHead
                    omega
                  let localIndex : Fin nestedFlat.regions.length :=
                    ⟨child.val - (regionBase + 1), by omega⟩
                  have nestedAllocated : List.SegmentAt whole.regions
                      nestedFlat.regions (regionBase + 1) := by
                    simpa [headFlat, flattenItem, flattenRegion, nestedFlat]
                      using headAllocated.regions.tail
                  have lookup : whole.regions.get child =
                      nestedFlat.regions.get localIndex := by
                    have lookup' := nestedAllocated.get localIndex
                    have globalEq :
                        (⟨regionBase + 1 + localIndex.val, by
                          exact nestedAllocated.index_lt localIndex⟩ :
                          Fin whole.regions.length) = child := by
                      apply Fin.ext
                      simp [localIndex]
                      omega
                    rw [globalEq] at lookup'
                    exact lookup'
                  have nestedParent :
                      (nestedFlat.regions.get localIndex).parentIndex? =
                        some current := by
                    rw [← lookup]
                    exact parent
                  have band := (nestedBand.regions _
                    (List.get_mem nestedFlat.regions localIndex)).parentIndex
                      nestedParent
                  rcases band with equality | descendant
                  · omega
                  · omega
        | bubble arity body =>
            cases body with
            | mk localWires nested =>
                by_cases direct : child.val = regionBase
                · simp [occurrenceDrafts, direct]
                · let nestedFlat := flattenItems regionBase
                    (regionBase + 1) nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires)
                    (binders.push regionBase) nested
                  have nestedBand := flattenItems_ownerBand nested regionBase
                    (regionBase + 1) nodeBase (wireBase + localWires)
                    (wires.extend wireBase localWires)
                    (binders.push regionBase) (by omega)
                  have nestedLength : nestedFlat.regions.length =
                      (itemSeqCounts nested).regions := by
                    exact (flattenItems_lengths regionBase (regionBase + 1)
                      nodeBase (wireBase + localWires)
                      (wires.extend wireBase localWires)
                      (binders.push regionBase) nested).1
                  have nestedUpper : child.val <
                      regionBase + 1 + nestedFlat.regions.length := by
                    rw [nestedLength]
                    simp only [itemCounts, regionCounts] at inHead
                    omega
                  let localIndex : Fin nestedFlat.regions.length :=
                    ⟨child.val - (regionBase + 1), by omega⟩
                  have nestedAllocated : List.SegmentAt whole.regions
                      nestedFlat.regions (regionBase + 1) := by
                    simpa [headFlat, flattenItem, flattenRegion, nestedFlat]
                      using headAllocated.regions.tail
                  have lookup : whole.regions.get child =
                      nestedFlat.regions.get localIndex := by
                    have lookup' := nestedAllocated.get localIndex
                    have globalEq :
                        (⟨regionBase + 1 + localIndex.val, by
                          exact nestedAllocated.index_lt localIndex⟩ :
                          Fin whole.regions.length) = child := by
                      apply Fin.ext
                      simp [localIndex]
                      omega
                    rw [globalEq] at lookup'
                    exact lookup'
                  have nestedParent :
                      (nestedFlat.regions.get localIndex).parentIndex? =
                        some current := by
                    rw [← lookup]
                    exact parent
                  have band := (nestedBand.regions _
                    (List.get_mem nestedFlat.regions localIndex)).parentIndex
                      nestedParent
                  rcases band with equality | descendant
                  · omega
                  · omega
      · have tailLower :
            regionBase + (itemCounts head).regions ≤ child.val := by omega
        have tailUpper : child.val <
            regionBase + (itemCounts head).regions +
              (itemSeqCounts tail).regions := by
          simp only [itemSeqCounts, Counts.add] at upper
          omega
        have tailMember := ih whole current
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wires binders tailAllocated
          (by omega) child parent tailLower tailUpper
        simp only [occurrenceDrafts, List.mem_cons]
        exact Or.inr tailMember

/-- Proof-only pre-order index of the source regions.  Each record retains
the exact local-wire slice and direct source-item occurrence fiber consumed by
the body roundtrip. -/
private structure RegionRecord where
  index : Nat
  wireBase : Nat
  localWires : Nat
  occurrences : List OccurrenceDraft

mutual
  private def regionRecords :
      (regionBase nodeBase wireBase : Nat) →
      Region wires rels → List RegionRecord
    | regionBase, nodeBase, wireBase, .mk localWires items =>
        { index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items } ::
        itemRecords (regionBase + 1) nodeBase (wireBase + localWires) items

  private def itemRecords :
      (regionBase nodeBase wireBase : Nat) →
      ItemSeq wires rels → List RegionRecord
    | _, _, _, .nil => []
    | regionBase, nodeBase, wireBase, .cons head tail =>
        let headRecords := match head with
          | .atom _ _ => []
          | .identity _ _ => []
          | .cut body => regionRecords regionBase nodeBase wireBase body
          | .bubble _ body => regionRecords regionBase nodeBase wireBase body
        headRecords ++ itemRecords
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) tail
end

private def itemRecordBlock
    (regionBase nodeBase wireBase : Nat)
    (item : Item wires rels) : List RegionRecord :=
  match item with
  | .atom _ _ => []
  | .identity _ _ => []
  | .cut body => regionRecords regionBase nodeBase wireBase body
  | .bubble _ body => regionRecords regionBase nodeBase wireBase body

private theorem itemRecords_cons
    (head : Item wires rels) (tail : ItemSeq wires rels) :
    itemRecords regionBase nodeBase wireBase (.cons head tail) =
      itemRecordBlock regionBase nodeBase wireBase head ++
        itemRecords (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) tail := by
  cases head <;> rfl

private def openRegionRecords
    (diagram : VisualProof.Diagram.OpenDiagram arity) : List RegionRecord :=
  regionRecords 0 0 diagram.externalClasses diagram.body

private def RegionRecordsLengthMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    (regionRecords regionBase nodeBase wireBase region).length =
      (regionCounts region).regions

private def ItemRecordsLengthMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    (itemRecordBlock regionBase nodeBase wireBase item).length =
      (itemCounts item).regions

private def ItemsRecordsLengthMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    (itemRecords regionBase nodeBase wireBase items).length =
      (itemSeqCounts items).regions

private theorem itemRecords_lengths (items : ItemSeq wires rels) :
    ItemsRecordsLengthMotive wires rels items := by
  apply ItemSeq.rec
    (motive_1 := RegionRecordsLengthMotive)
    (motive_2 := ItemRecordsLengthMotive)
    (motive_3 := ItemsRecordsLengthMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsLength
      intro regionBase nodeBase wireBase
      simp only [regionRecords, List.length_cons, regionCounts]
      rw [itemsLength (regionBase + 1) nodeBase (wireBase + localWires)]
  case atom =>
      intros
      simp [ItemRecordsLengthMotive, itemRecordBlock, itemCounts]
  case identity =>
      intros
      simp [ItemRecordsLengthMotive, itemRecordBlock, itemCounts]
  case cut =>
      intro sourceWires sourceRels body bodyLength
      intro regionBase nodeBase wireBase
      simpa [ItemRecordsLengthMotive, itemCounts] using
        bodyLength regionBase nodeBase wireBase
  case bubble =>
      intro sourceWires sourceRels arity body bodyLength
      intro regionBase nodeBase wireBase
      simpa [ItemRecordsLengthMotive, itemCounts] using
        bodyLength regionBase nodeBase wireBase
  case nil =>
      intros
      simp [ItemsRecordsLengthMotive, itemRecords, itemSeqCounts]
  case cons =>
      intro sourceWires sourceRels head tail headLength tailLength
      intro regionBase nodeBase wireBase
      unfold ItemRecordsLengthMotive at headLength
      unfold ItemsRecordsLengthMotive at tailLength
      rw [itemRecords_cons, List.length_append, itemSeqCounts]
      change _ = (itemCounts head).regions + (itemSeqCounts tail).regions
      rw [headLength regionBase nodeBase wireBase, tailLength]

private theorem regionRecords_lengths (region : Region wires rels) :
    RegionRecordsLengthMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro regionBase nodeBase wireBase
      simp only [regionRecords, List.length_cons, regionCounts]
      rw [itemRecords_lengths items (regionBase + 1) nodeBase
        (wireBase + localWires)]

private theorem itemRecordBlock_length (item : Item wires rels) :
    ItemRecordsLengthMotive wires rels item := by
  intro regionBase nodeBase wireBase
  have result := itemRecords_lengths (.cons item .nil) regionBase nodeBase
    wireBase
  unfold ItemsRecordsLengthMotive at result
  simpa [itemRecords_cons, itemSeqCounts, Counts.add] using result

private def RegionRecord.Sequential : Nat → List RegionRecord → Prop
  | _, [] => True
  | index, head :: tail =>
      head.index = index ∧ Sequential (index + 1) tail

private theorem RegionRecord.Sequential.append
    (left right : List RegionRecord)
    (leftSequential : RegionRecord.Sequential base left)
    (rightSequential : RegionRecord.Sequential (base + left.length) right) :
    RegionRecord.Sequential base (left ++ right) := by
  induction left generalizing base with
  | nil => simpa [RegionRecord.Sequential] using rightSequential
  | cons head tail ih =>
      rcases leftSequential with ⟨headIndex, tailSequential⟩
      exact ⟨headIndex, ih tailSequential (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          rightSequential)⟩

private def RegionRecordsSequentialMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RegionRecord.Sequential regionBase
      (regionRecords regionBase nodeBase wireBase region)

private def ItemRecordsSequentialMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RegionRecord.Sequential regionBase
      (itemRecordBlock regionBase nodeBase wireBase item)

private def ItemsRecordsSequentialMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RegionRecord.Sequential regionBase
      (itemRecords regionBase nodeBase wireBase items)

private theorem itemRecords_sequential (items : ItemSeq wires rels) :
    ItemsRecordsSequentialMotive wires rels items := by
  apply ItemSeq.rec
    (motive_1 := RegionRecordsSequentialMotive)
    (motive_2 := ItemRecordsSequentialMotive)
    (motive_3 := ItemsRecordsSequentialMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsSequential
      intro regionBase nodeBase wireBase
      exact ⟨rfl, itemsSequential (regionBase + 1) nodeBase
        (wireBase + localWires)⟩
  case atom =>
      intros
      simp [ItemRecordsSequentialMotive, itemRecordBlock,
        RegionRecord.Sequential]
  case identity =>
      intros
      simp [ItemRecordsSequentialMotive, itemRecordBlock,
        RegionRecord.Sequential]
  case cut =>
      intro sourceWires sourceRels body bodySequential
      exact bodySequential
  case bubble =>
      intro sourceWires sourceRels arity body bodySequential
      exact bodySequential
  case nil =>
      intros
      simp [ItemsRecordsSequentialMotive, itemRecords,
        RegionRecord.Sequential]
  case cons =>
      intro sourceWires sourceRels head tail headSequential tailSequential
      intro regionBase nodeBase wireBase
      rw [itemRecords_cons]
      apply RegionRecord.Sequential.append
      · exact headSequential regionBase nodeBase wireBase
      · have headLength := itemRecordBlock_length head regionBase nodeBase
          wireBase
        unfold ItemRecordsLengthMotive at headLength
        rw [headLength]
        exact tailSequential
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires)

private theorem regionRecords_sequential (region : Region wires rels) :
    RegionRecordsSequentialMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro regionBase nodeBase wireBase
      exact ⟨rfl, itemRecords_sequential items (regionBase + 1) nodeBase
        (wireBase + localWires)⟩

private theorem RegionRecord.Sequential.get
    (sequential : RegionRecord.Sequential base records)
    (index : Fin records.length) :
    (records.get index).index = base + index.val := by
  induction records generalizing base with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      rcases sequential with ⟨headIndex, tailSequential⟩
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simpa using headIndex
      · have result := ih tailSequential tailIndex
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

private theorem openRegionRecords_index
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (index : Fin (openRegionRecords diagram).length) :
    ((openRegionRecords diagram).get index).index = index.val := by
  simpa [openRegionRecords] using
    (regionRecords_sequential diagram.body 0 0 diagram.externalClasses).get
      index

private def RegionRecordsNodupMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase record,
    record ∈ regionRecords regionBase nodeBase wireBase region →
      record.occurrences.Nodup

private def ItemRecordsNodupMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase record,
    record ∈ itemRecordBlock regionBase nodeBase wireBase item →
      record.occurrences.Nodup

private def ItemsRecordsNodupMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase record,
    record ∈ itemRecords regionBase nodeBase wireBase items →
      record.occurrences.Nodup

private theorem itemRecords_occurrences_nodup
    (items : ItemSeq wires rels) :
    ItemsRecordsNodupMotive wires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionRecordsNodupMotive)
      (motive_2 := ItemRecordsNodupMotive)
      (motive_3 := ItemsRecordsNodupMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsNodup
      intro regionBase nodeBase wireBase record member
      simp only [regionRecords, List.mem_cons] at member
      rcases member with rfl | member
      · exact occurrenceDrafts_nodup items
      · exact itemsNodup (regionBase + 1) nodeBase
          (wireBase + localWires) record member
  case atom =>
      simp [ItemRecordsNodupMotive, itemRecordBlock]
  case identity =>
      simp [ItemRecordsNodupMotive, itemRecordBlock]
  case cut =>
      intro sourceWires sourceRels body bodyNodup
      exact bodyNodup
  case bubble =>
      intro sourceWires sourceRels arity body bodyNodup
      exact bodyNodup
  case nil =>
      simp [ItemsRecordsNodupMotive, itemRecords]
  case cons =>
      intro sourceWires sourceRels head tail headNodup tailNodup
      intro regionBase nodeBase wireBase record member
      rw [itemRecords_cons, List.mem_append] at member
      rcases member with member | member
      · exact headNodup regionBase nodeBase wireBase record member
      · exact tailNodup
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) record member

private theorem regionRecords_occurrences_nodup
    (region : Region wires rels) :
    RegionRecordsNodupMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro regionBase nodeBase wireBase record member
      simp only [regionRecords, List.mem_cons] at member
      rcases member with rfl | member
      · exact occurrenceDrafts_nodup items
      · exact itemRecords_occurrences_nodup items (regionBase + 1)
          nodeBase (wireBase + localWires) record member

private theorem openRegionRecords_occurrences_nodup
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord) (member : record ∈ openRegionRecords diagram) :
    record.occurrences.Nodup :=
  regionRecords_occurrences_nodup diagram.body 0 0 diagram.externalClasses
    record (by simpa [openRegionRecords] using member)

private def recordOccurrences (records : List RegionRecord) :
    List OccurrenceDraft :=
  records.flatMap (fun record => record.occurrences)

private def itemDrafts
    (regionBase nodeBase wireBase : Nat) (item : Item wires rels) :
    List OccurrenceDraft :=
  (match item with
    | .atom _ _ | .identity _ _ => [.node nodeBase]
    | .cut _ | .bubble _ _ => [.child regionBase]) ++
  recordOccurrences (itemRecordBlock regionBase nodeBase wireBase item)

private def itemsDrafts
    (regionBase nodeBase wireBase : Nat) (items : ItemSeq wires rels) :
    List OccurrenceDraft :=
  occurrenceDrafts regionBase nodeBase items ++
    recordOccurrences (itemRecords regionBase nodeBase wireBase items)

private theorem mem_itemsDrafts_cons
    (draft : OccurrenceDraft) (head : Item wires rels)
    (tail : ItemSeq wires rels) :
    draft ∈ itemsDrafts regionBase nodeBase wireBase (.cons head tail) ↔
      draft ∈ itemDrafts regionBase nodeBase wireBase head ∨
      draft ∈ itemsDrafts
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) tail := by
  cases head <;>
    simp [itemsDrafts, itemDrafts, itemRecords_cons, recordOccurrences,
      occurrenceDrafts, List.mem_append, or_assoc, or_left_comm]

private structure DraftCoverage
    (drafts : List OccurrenceDraft)
    (regionBase regionLimit nodeBase nodeLimit : Nat) : Prop where
  nodes : ∀ index, nodeBase ≤ index → index < nodeLimit →
    .node index ∈ drafts
  children : ∀ index, regionBase ≤ index → index < regionLimit →
    .child index ∈ drafts

private def RegionCoverageMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    DraftCoverage
      (recordOccurrences (regionRecords regionBase nodeBase wireBase region))
      (regionBase + 1) (regionBase + (regionCounts region).regions)
      nodeBase (nodeBase + (regionCounts region).nodes)

private def ItemCoverageMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    DraftCoverage (itemDrafts regionBase nodeBase wireBase item)
      regionBase (regionBase + (itemCounts item).regions)
      nodeBase (nodeBase + (itemCounts item).nodes)

private def ItemsCoverageMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    DraftCoverage (itemsDrafts regionBase nodeBase wireBase items)
      regionBase (regionBase + (itemSeqCounts items).regions)
      nodeBase (nodeBase + (itemSeqCounts items).nodes)

private theorem itemRecords_coverage (items : ItemSeq wires rels) :
    ItemsCoverageMotive wires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionCoverageMotive)
      (motive_2 := ItemCoverageMotive)
      (motive_3 := ItemsCoverageMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsCoverage
      intro regionBase nodeBase wireBase
      simp only [regionRecords, recordOccurrences, List.flatMap_cons,
        regionCounts]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        itemsCoverage (regionBase + 1) nodeBase (wireBase + localWires)
  case atom =>
      intro sourceRels arity sourceWires relation arguments
      intro regionBase nodeBase wireBase
      exact {
        nodes := by
          intro index lower upper
          have equality : index = nodeBase := by
            simp only [itemCounts] at upper
            omega
          simp [itemDrafts, equality]
        children := by
          intro index lower upper
          simp only [itemCounts] at upper
          omega
      }
  case identity =>
      intro sourceWires sourceRels arity arguments
      intro regionBase nodeBase wireBase
      exact {
        nodes := by
          intro index lower upper
          have equality : index = nodeBase := by
            simp only [itemCounts] at upper
            omega
          simp [itemDrafts, equality]
        children := by
          intro index lower upper
          simp only [itemCounts] at upper
          omega
      }
  case cut =>
      intro sourceWires sourceRels body bodyCoverage
      intro regionBase nodeBase wireBase
      have coverage := bodyCoverage regionBase nodeBase wireBase
      exact {
        nodes := by
          intro index lower upper
          exact List.mem_append_right _ (coverage.nodes index lower (by
            simpa [itemCounts] using upper))
        children := by
          intro index lower upper
          by_cases direct : index = regionBase
          · simp [itemDrafts, direct]
          · apply List.mem_append_right
            exact coverage.children index (by omega) (by
              simpa [itemCounts] using upper)
      }
  case bubble =>
      intro sourceWires sourceRels arity body bodyCoverage
      intro regionBase nodeBase wireBase
      have coverage := bodyCoverage regionBase nodeBase wireBase
      exact {
        nodes := by
          intro index lower upper
          exact List.mem_append_right _ (coverage.nodes index lower (by
            simpa [itemCounts] using upper))
        children := by
          intro index lower upper
          by_cases direct : index = regionBase
          · simp [itemDrafts, direct]
          · apply List.mem_append_right
            exact coverage.children index (by omega) (by
              simpa [itemCounts] using upper)
      }
  case nil =>
      intro sourceWires sourceRels regionBase nodeBase wireBase
      exact {
        nodes := by
          intro index lower upper
          simp only [itemSeqCounts] at upper
          omega
        children := by
          intro index lower upper
          simp only [itemSeqCounts] at upper
          omega
      }
  case cons =>
      intro sourceWires sourceRels head tail headCoverage tailCoverage
      intro regionBase nodeBase wireBase
      have headResult := headCoverage regionBase nodeBase wireBase
      have tailResult := tailCoverage
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires)
      exact {
        nodes := by
          intro index lower upper
          rw [mem_itemsDrafts_cons]
          by_cases inHead : index < nodeBase + (itemCounts head).nodes
          · exact Or.inl (headResult.nodes index lower inHead)
          · apply Or.inr
            apply tailResult.nodes index (by omega)
            simp only [itemSeqCounts, Counts.add] at upper
            omega
        children := by
          intro index lower upper
          rw [mem_itemsDrafts_cons]
          by_cases inHead : index < regionBase + (itemCounts head).regions
          · exact Or.inl (headResult.children index lower inHead)
          · apply Or.inr
            apply tailResult.children index (by omega)
            simp only [itemSeqCounts, Counts.add] at upper
            omega
      }

private theorem regionRecords_coverage (region : Region wires rels) :
    RegionCoverageMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro regionBase nodeBase wireBase
      simp only [regionRecords, recordOccurrences, List.flatMap_cons,
        regionCounts]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        itemRecords_coverage items (regionBase + 1) nodeBase
          (wireBase + localWires)

private structure RegionRecord.OwnedIn
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (record : RegionRecord) where
  current : Fin (rawDiagram diagram).regionCount
  bounded : ∀ draft, draft ∈ record.occurrences →
    draft.Bounded (rawDiagram diagram).regionCount
      (rawDiagram diagram).nodeCount
  index_eq : current.val = record.index
  owned : ∀ draft (member : draft ∈ record.occurrences),
    draft.OwnedBy (rawDiagram diagram) current (bounded draft member)

private def RegionRecordsOwnedMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenRegion regionKind regionBase nodeBase wireBase
        outerWires binders region) regionBase nodeBase wireBase →
    ∀ record, record ∈ regionRecords regionBase nodeBase wireBase region →
      record.OwnedIn diagram

private def ItemRecordsOwnedMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenItem current regionBase nodeBase wireBase wireMap binders item)
      regionBase nodeBase wireBase →
    ∀ record, record ∈ itemRecordBlock regionBase nodeBase wireBase item →
      record.OwnedIn diagram

private def ItemsRecordsOwnedMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenItems current regionBase nodeBase wireBase wireMap binders items)
      regionBase nodeBase wireBase →
    ∀ record, record ∈ itemRecords regionBase nodeBase wireBase items →
      record.OwnedIn diagram

private noncomputable def itemRecords_owned (items : ItemSeq wires rels) :
    ItemsRecordsOwnedMotive wires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionRecordsOwnedMotive)
      (motive_2 := ItemRecordsOwnedMotive)
      (motive_3 := ItemsRecordsOwnedMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsOwned
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders allocated record member
      simp only [regionRecords, List.mem_cons] at member
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders items).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders items).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      let nestedFlat := flattenItems regionBase (regionBase + 1) nodeBase
        (wireBase + localWires) (outerWires.extend wireBase localWires)
        binders items
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [flattenRegion, nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      by_cases hroot : record = {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
      · subst record
        let current : Fin (rawDiagram diagram).regionCount :=
          ⟨regionBase, regionAllocation.index_lt ⟨0, by simp⟩⟩
        let bounded := occurrenceDrafts_bounded diagram regionBase
          (regionBase + 1) nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders items nestedAllocated
        refine ⟨current, bounded, rfl, ?_⟩
        intro draft draftMember
        exact occurrenceDrafts_owned diagram current (regionBase + 1)
          nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders items
          nestedAllocated draft draftMember
      · have member : record ∈ itemRecords (regionBase + 1) nodeBase
            (wireBase + localWires) items := by
          rcases member with heq | hmember
          · exact False.elim (hroot heq)
          · exact hmember
        exact itemsOwned diagram regionBase (regionBase + 1) nodeBase
          (wireBase + localWires) (outerWires.extend wireBase localWires)
          binders nestedAllocated record member
  case atom =>
      intro sourceRels arity sourceWires relation arguments
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      simp [itemRecordBlock] at member
  case identity =>
      intro sourceWires sourceRels arity arguments
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      simp [itemRecordBlock] at member
  case cut =>
      intro sourceWires sourceRels body bodyOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      exact bodyOwned diagram (.cut current) regionBase nodeBase wireBase
        wireMap binders (by simpa [flattenItem] using allocated) record
        (by simpa [itemRecordBlock] using member)
  case bubble =>
      intro sourceWires sourceRels arity body bodyOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      exact bodyOwned diagram (.bubble current arity) regionBase nodeBase
        wireBase wireMap (binders.push regionBase)
        (by simpa [flattenItem] using allocated) record
        (by simpa [itemRecordBlock] using member)
  case nil =>
      intro sourceWires sourceRels openArity diagram current regionBase
        nodeBase wireBase wireMap binders allocated record member
      simp [itemRecords] at member
  case cons =>
      intro sourceWires sourceRels head tail headOwned tailOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      let headFlat := flattenItem current regionBase nodeBase wireBase
        wireMap binders head
      let tailFlat := flattenItems current
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wireMap binders tail
      have flatEq : flattenItems current regionBase nodeBase wireBase
          wireMap binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt (flattenOpen diagram)
          (headFlat.append tailFlat) regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths current regionBase nodeBase
        wireBase wireMap binders head
      have headRegionsLength : headFlat.regions.length =
          (itemCounts head).regions := headLengths.1
      have headNodesLength : headFlat.nodes.length =
          (itemCounts head).nodes := headLengths.2.1
      have headWiresLength : headFlat.wireScopes.length =
          (itemCounts head).wires := headLengths.2.2
      rw [headRegionsLength, headNodesLength, headWiresLength] at tailAllocated
      rw [itemRecords_cons] at member
      by_cases hhead : record ∈ itemRecordBlock regionBase nodeBase
          wireBase head
      · exact headOwned diagram current regionBase nodeBase wireBase wireMap
          binders headAllocated record hhead
      · have member : record ∈ itemRecords
            (regionBase + (itemCounts head).regions)
            (nodeBase + (itemCounts head).nodes)
            (wireBase + (itemCounts head).wires) tail := by
          exact (List.mem_append.mp member).resolve_left hhead
        exact tailOwned diagram current
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wireMap binders tailAllocated
          record member

private noncomputable def regionRecords_owned (region : Region wires rels) :
    RegionRecordsOwnedMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders allocated record member
      simp only [regionRecords, List.mem_cons] at member
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders items).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders items).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      let nestedFlat := flattenItems regionBase (regionBase + 1) nodeBase
        (wireBase + localWires) (outerWires.extend wireBase localWires)
        binders items
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [flattenRegion, nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      by_cases hroot : record = {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
      · subst record
        let current : Fin (rawDiagram diagram).regionCount :=
          ⟨regionBase, regionAllocation.index_lt ⟨0, by simp⟩⟩
        let bounded := occurrenceDrafts_bounded diagram regionBase
          (regionBase + 1) nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders items nestedAllocated
        refine ⟨current, bounded, rfl, ?_⟩
        intro draft draftMember
        exact occurrenceDrafts_owned diagram current (regionBase + 1)
          nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders items
          nestedAllocated draft draftMember
      · have member : record ∈ itemRecords (regionBase + 1) nodeBase
            (wireBase + localWires) items := by
          rcases member with heq | hmember
          · exact False.elim (hroot heq)
          · exact hmember
        exact itemRecords_owned items diagram regionBase (regionBase + 1)
          nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders nestedAllocated
          record member

private noncomputable def openRegionRecords_owned
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    ∀ record, record ∈ openRegionRecords diagram →
      record.OwnedIn diagram := by
  let bodyFlat := flattenRegion .sheet 0 0 diagram.externalClasses
    (fun external => external.val) BinderMap.empty diagram.body
  have bodyAllocated : Flat.SegmentAt (flattenOpen diagram) bodyFlat
      0 0 diagram.externalClasses := by
    exact {
      regions := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
      nodes := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
      wireScopes := ⟨List.replicate diagram.externalClasses 0, [], by simp,
        by simp [flattenOpen, bodyFlat]⟩
    }
  intro record member
  exact regionRecords_owned diagram.body diagram .sheet 0 0
    diagram.externalClasses (fun external => external.val) BinderMap.empty
    (by simpa [bodyFlat] using bodyAllocated) record
    (by simpa [openRegionRecords] using member)

private theorem openRegionRecords_node_coverage
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (node : Fin (rawDiagram diagram).nodeCount) :
    .node node.val ∈ recordOccurrences (openRegionRecords diagram) := by
  have coverage := regionRecords_coverage diagram.body 0 0
    diagram.externalClasses
  apply coverage.nodes node.val (by omega)
  have length := flattenRegion_nodes_length .sheet 0 0
    diagram.externalClasses (fun external => external.val) BinderMap.empty
    diagram.body
  have nodeLt := node.isLt
  change node.val < (flattenOpen diagram).nodes.length at nodeLt
  simpa [flattenOpen, length] using nodeLt

private theorem openRegionRecords_child_coverage
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (child : Fin (rawDiagram diagram).regionCount)
    (notRoot : child ≠ (rawDiagram diagram).root) :
    .child child.val ∈ recordOccurrences (openRegionRecords diagram) := by
  have coverage := regionRecords_coverage diagram.body 0 0
    diagram.externalClasses
  apply coverage.children child.val (by
    have valuesDifferent : child.val ≠ 0 := by
      intro equality
      apply notRoot
      apply Fin.ext
      exact equality
    omega)
  have length := flattenRegion_regions_length .sheet 0 0
    diagram.externalClasses (fun external => external.val) BinderMap.empty
    diagram.body
  have childLt := child.isLt
  change child.val < (flattenOpen diagram).regions.length at childLt
  simpa [flattenOpen, length] using childLt

private theorem openRegionRecords_unique_index
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    {first second : RegionRecord}
    (firstMember : first ∈ openRegionRecords diagram)
    (secondMember : second ∈ openRegionRecords diagram)
    (indexEq : first.index = second.index) :
    first = second := by
  rw [List.mem_iff_get] at firstMember secondMember
  rcases firstMember with ⟨firstPosition, firstEq⟩
  rcases secondMember with ⟨secondPosition, secondEq⟩
  have positionsVal : firstPosition.val = secondPosition.val := by
    have firstIndex := openRegionRecords_index diagram firstPosition
    have secondIndex := openRegionRecords_index diagram secondPosition
    rw [firstEq] at firstIndex
    rw [secondEq] at secondIndex
    omega
  have positionsEq : firstPosition = secondPosition := Fin.ext positionsVal
  subst secondPosition
  exact firstEq.symm.trans secondEq

private structure LocalOccurrencesCertificate
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord)
    (current : Fin (rawDiagram diagram).regionCount) where
  bounded : ∀ draft, draft ∈ record.occurrences →
    draft.Bounded (rawDiagram diagram).regionCount
      (rawDiagram diagram).nodeCount
  mem_iff : ∀ occurrence,
    occurrence ∈ Elaboration.localOccurrences (rawDiagram diagram) current ↔
      occurrence ∈ realizeOccurrenceDrafts record.occurrences bounded

private noncomputable def record_localOccurrences
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord)
    (recordMember : record ∈ openRegionRecords diagram)
    (current : Fin (rawDiagram diagram).regionCount)
    (currentIndex : current.val = record.index) :
    LocalOccurrencesCertificate diagram record current := by
  obtain ⟨ownedCurrent, bounded, ownedIndex, owned⟩ :=
    openRegionRecords_owned diagram record recordMember
  have ownedCurrentEq : ownedCurrent = current := by
    apply Fin.ext
    exact ownedIndex.trans currentIndex.symm
  subst ownedCurrent
  refine ⟨bounded, ?_⟩
  intro occurrence
  constructor
  · intro localMember
    cases occurrence with
    | node node =>
        have aggregateMember := openRegionRecords_node_coverage diagram node
        rw [recordOccurrences, List.mem_flatMap] at aggregateMember
        obtain ⟨candidate, candidateMember, draftMember⟩ := aggregateMember
        obtain ⟨candidateCurrent, candidateBounded, candidateIndex,
            candidateOwned⟩ :=
          openRegionRecords_owned diagram candidate candidateMember
        have candidateOwns := candidateOwned (.node node.val) draftMember
        have localOwns := (Elaboration.mem_localOccurrences_node
          (rawDiagram diagram) current node).mp localMember
        have concreteNodeEq :
            (⟨node.val, candidateBounded (.node node.val) draftMember⟩ :
              Fin (rawDiagram diagram).nodeCount) = node := by
          apply Fin.ext
          rfl
        simp only [OccurrenceDraft.OwnedBy] at candidateOwns
        rw [concreteNodeEq] at candidateOwns
        have candidateCurrentEq : candidateCurrent = current :=
          candidateOwns.symm.trans localOwns
        have recordsEq : candidate = record := by
          apply openRegionRecords_unique_index diagram candidateMember recordMember
          rw [← candidateIndex, ← currentIndex, candidateCurrentEq]
        subst candidate
        unfold realizeOccurrenceDrafts
        rw [List.mem_pmap]
        refine ⟨.node node.val, draftMember, ?_⟩
        apply congrArg Elaboration.LocalOccurrence.node
        apply Fin.ext
        rfl
    | child child =>
        have childNotRoot : child ≠ (rawDiagram diagram).root := by
          intro childEq
          subst child
          have localParent := (Elaboration.mem_localOccurrences_child
            (rawDiagram diagram) current (rawDiagram diagram).root).mp
              localMember
          have rootDraft : (flattenOpen diagram).regions.get
              (rawDiagram diagram).root = .sheet := by
            simpa only [rawDiagram, flattenOpen, List.get_eq_getElem] using
              flattenRegion_regions_get_zero .sheet 0 0
                diagram.externalClasses (fun external => external.val)
                BinderMap.empty diagram.body
          have rootSheet := rawDiagram_region_sheet_lookup diagram
            (rawDiagram diagram).root rootDraft
          rw [rootSheet] at localParent
          contradiction
        have aggregateMember := openRegionRecords_child_coverage diagram child
          childNotRoot
        rw [recordOccurrences, List.mem_flatMap] at aggregateMember
        obtain ⟨candidate, candidateMember, draftMember⟩ := aggregateMember
        obtain ⟨candidateCurrent, candidateBounded, candidateIndex,
            candidateOwned⟩ :=
          openRegionRecords_owned diagram candidate candidateMember
        have candidateOwns := candidateOwned (.child child.val) draftMember
        have localOwns := (Elaboration.mem_localOccurrences_child
          (rawDiagram diagram) current child).mp localMember
        have concreteChildEq :
            (⟨child.val, candidateBounded (.child child.val) draftMember⟩ :
              Fin (rawDiagram diagram).regionCount) = child := by
          apply Fin.ext
          rfl
        simp only [OccurrenceDraft.OwnedBy] at candidateOwns
        rw [concreteChildEq] at candidateOwns
        have candidateCurrentEq : candidateCurrent = current := by
          exact Option.some.inj (candidateOwns.symm.trans localOwns)
        have recordsEq : candidate = record := by
          apply openRegionRecords_unique_index diagram candidateMember recordMember
          rw [← candidateIndex, ← currentIndex, candidateCurrentEq]
        subst candidate
        unfold realizeOccurrenceDrafts
        rw [List.mem_pmap]
        refine ⟨.child child.val, draftMember, ?_⟩
        apply congrArg Elaboration.LocalOccurrence.child
        apply Fin.ext
        rfl
  · intro realizedMember
    unfold realizeOccurrenceDrafts at realizedMember
    rw [List.mem_pmap] at realizedMember
    obtain ⟨draft, draftMember, occurrenceEq⟩ := realizedMember
    rw [← occurrenceEq]
    have draftOwned := owned draft draftMember
    cases draft with
    | node index =>
        exact (Elaboration.mem_localOccurrences_node
          (rawDiagram diagram) current _).mpr draftOwned
    | child index =>
        exact (Elaboration.mem_localOccurrences_child
          (rawDiagram diagram) current _).mpr draftOwned

private def RecordsCoverWires
    (records : List RegionRecord) (wireBase wireLimit : Nat) : Prop :=
  ∀ index, wireBase ≤ index → index < wireLimit →
    ∃ record, record ∈ records ∧
      ∃ localWire : Fin record.localWires,
        index = record.wireBase + localWire.val

private def RegionWireCoverageMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RecordsCoverWires (regionRecords regionBase nodeBase wireBase region)
      wireBase (wireBase + (regionCounts region).wires)

private def ItemWireCoverageMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RecordsCoverWires (itemRecordBlock regionBase nodeBase wireBase item)
      wireBase (wireBase + (itemCounts item).wires)

private def ItemsWireCoverageMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Prop :=
  ∀ regionBase nodeBase wireBase,
    RecordsCoverWires (itemRecords regionBase nodeBase wireBase items)
      wireBase (wireBase + (itemSeqCounts items).wires)

private theorem itemRecords_wire_coverage (items : ItemSeq wires rels) :
    ItemsWireCoverageMotive wires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionWireCoverageMotive)
      (motive_2 := ItemWireCoverageMotive)
      (motive_3 := ItemsWireCoverageMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsCoverage
      intro regionBase nodeBase wireBase index lower upper
      simp only [regionCounts] at upper
      by_cases currentLocal : index < wireBase + localWires
      · let record : RegionRecord := {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
        let localWire : Fin localWires := ⟨index - wireBase, by omega⟩
        refine ⟨record, by simp [regionRecords, record], localWire, ?_⟩
        simp [record, localWire]
        omega
      · obtain ⟨record, member, localWire, equality⟩ :=
          itemsCoverage (regionBase + 1) nodeBase (wireBase + localWires)
            index (by omega) (by omega)
        exact ⟨record, by simp [regionRecords, member], localWire, equality⟩
  case atom =>
      intro sourceRels arity sourceWires relation arguments
      intro regionBase nodeBase wireBase index lower upper
      simp only [itemCounts] at upper
      omega
  case identity =>
      intro sourceWires sourceRels arity arguments
      intro regionBase nodeBase wireBase index lower upper
      simp only [itemCounts] at upper
      omega
  case cut =>
      intro sourceWires sourceRels body bodyCoverage
      intro regionBase nodeBase wireBase
      simpa [itemRecordBlock, itemCounts] using
        bodyCoverage regionBase nodeBase wireBase
  case bubble =>
      intro sourceWires sourceRels arity body bodyCoverage
      intro regionBase nodeBase wireBase
      simpa [itemRecordBlock, itemCounts] using
        bodyCoverage regionBase nodeBase wireBase
  case nil =>
      intro sourceWires sourceRels regionBase nodeBase wireBase index lower upper
      simp only [itemSeqCounts] at upper
      omega
  case cons =>
      intro sourceWires sourceRels head tail headCoverage tailCoverage
      intro regionBase nodeBase wireBase index lower upper
      simp only [itemSeqCounts, Counts.add] at upper
      by_cases inHead : index < wireBase + (itemCounts head).wires
      · obtain ⟨record, member, localWire, equality⟩ :=
          headCoverage regionBase nodeBase wireBase index lower inHead
        refine ⟨record, ?_, localWire, equality⟩
        rw [itemRecords_cons, List.mem_append]
        exact Or.inl member
      · obtain ⟨record, member, localWire, equality⟩ := tailCoverage
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) index (by omega) (by omega)
        refine ⟨record, ?_, localWire, equality⟩
        rw [itemRecords_cons, List.mem_append]
        exact Or.inr member

private theorem regionRecords_wire_coverage (region : Region wires rels) :
    RegionWireCoverageMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro regionBase nodeBase wireBase index lower upper
      simp only [regionCounts] at upper
      by_cases currentLocal : index < wireBase + localWires
      · let record : RegionRecord := {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
        let localWire : Fin localWires := ⟨index - wireBase, by omega⟩
        refine ⟨record, by simp [regionRecords, record], localWire, ?_⟩
        simp [record, localWire]
        omega
      · obtain ⟨record, member, localWire, equality⟩ :=
          itemRecords_wire_coverage items (regionBase + 1) nodeBase
            (wireBase + localWires) index (by omega) (by omega)
        exact ⟨record, by simp [regionRecords, member], localWire, equality⟩

private theorem openRegionRecords_wire_coverage
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (wire : Fin (rawDiagram diagram).wireCount)
    (notExternal : diagram.externalClasses ≤ wire.val) :
    ∃ record, record ∈ openRegionRecords diagram ∧
      ∃ localWire : Fin record.localWires,
        wire.val = record.wireBase + localWire.val := by
  apply regionRecords_wire_coverage diagram.body 0 0 diagram.externalClasses
    wire.val notExternal
  have length := flattenRegion_wireScopes_length .sheet 0 0
    diagram.externalClasses (fun external => external.val) BinderMap.empty
    diagram.body
  have wireLt := wire.isLt
  change wire.val < (flattenOpen diagram).wireScopes.length at wireLt
  simp only [flattenOpen, List.length_append, List.length_replicate] at wireLt
  rw [length] at wireLt
  omega

private structure RegionRecord.WiresOwnedIn
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (record : RegionRecord) where
  current : Fin (rawDiagram diagram).regionCount
  wireEnd : record.wireBase + record.localWires ≤
    (rawDiagram diagram).wireCount
  index_eq : current.val = record.index
  local_scope : ∀ localWire : Fin record.localWires,
    ((rawDiagram diagram).wires
      ⟨record.wireBase + localWire.val, by
        have := localWire.isLt
        exact Nat.lt_of_lt_of_le (by omega) wireEnd⟩).scope = current

private def RegionRecordsWiresOwnedMotive
    (wires : Nat) (rels : RelCtx) (region : Region wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenRegion regionKind regionBase nodeBase wireBase
        outerWires binders region) regionBase nodeBase wireBase →
    ∀ record, record ∈ regionRecords regionBase nodeBase wireBase region →
      record.WiresOwnedIn diagram

private def ItemRecordsWiresOwnedMotive
    (wires : Nat) (rels : RelCtx) (item : Item wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenItem current regionBase nodeBase wireBase wireMap binders item)
      regionBase nodeBase wireBase →
    ∀ record, record ∈ itemRecordBlock regionBase nodeBase wireBase item →
      record.WiresOwnedIn diagram

private def ItemsRecordsWiresOwnedMotive
    (wires : Nat) (rels : RelCtx) (items : ItemSeq wires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (current regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap wires) (binders : BinderMap rels),
    Flat.SegmentAt (flattenOpen diagram)
      (flattenItems current regionBase nodeBase wireBase wireMap binders items)
      regionBase nodeBase wireBase →
    ∀ record, record ∈ itemRecords regionBase nodeBase wireBase items →
      record.WiresOwnedIn diagram

private noncomputable def itemRecords_wires_owned (items : ItemSeq wires rels) :
    ItemsRecordsWiresOwnedMotive wires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionRecordsWiresOwnedMotive)
      (motive_2 := ItemRecordsWiresOwnedMotive)
      (motive_3 := ItemsRecordsWiresOwnedMotive)
  case mk =>
      intro sourceWires sourceRels localWires items itemsOwned
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders allocated record member
      simp only [regionRecords, List.mem_cons] at member
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders items).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders items).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      let nestedFlat := flattenItems regionBase (regionBase + 1) nodeBase
        (wireBase + localWires) (outerWires.extend wireBase localWires)
        binders items
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [flattenRegion, nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      by_cases hroot : record = {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
      · subst record
        have localAllocation : List.SegmentAt
            (flattenOpen diagram).wireScopes
            (List.replicate localWires regionBase) wireBase :=
          wireAllocation.left
        let current : Fin (rawDiagram diagram).regionCount :=
          ⟨regionBase, regionAllocation.index_lt ⟨0, by simp⟩⟩
        have wireEnd : wireBase + localWires ≤
            (flattenOpen diagram).wireScopes.length
            := by simpa using localAllocation.end_le
        refine ⟨current, wireEnd, rfl, ?_⟩
        intro localWire
        let slot : Fin (List.replicate localWires regionBase).length :=
          ⟨localWire.val, by simp⟩
        let wire : Fin (rawDiagram diagram).wireCount :=
          ⟨wireBase + localWire.val, localAllocation.index_lt slot⟩
        have scopeEq : (flattenOpen diagram).wireScopes.get wire =
            regionBase := by
          have lookup := localAllocation.get slot
          simpa [wire, slot] using lookup
        apply Fin.ext
        exact scopeEq
      · have member : record ∈ itemRecords (regionBase + 1) nodeBase
            (wireBase + localWires) items := by
          rcases member with heq | hmember
          · exact False.elim (hroot heq)
          · exact hmember
        exact itemsOwned diagram regionBase (regionBase + 1) nodeBase
          (wireBase + localWires) (outerWires.extend wireBase localWires)
          binders nestedAllocated record member
  case atom =>
      intro sourceRels arity sourceWires relation arguments
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      change record ∈ ([] : List RegionRecord) at member
      exact False.elim (List.not_mem_nil member)
  case identity =>
      intro sourceWires sourceRels arity arguments
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      change record ∈ ([] : List RegionRecord) at member
      exact False.elim (List.not_mem_nil member)
  case cut =>
      intro sourceWires sourceRels body bodyOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      exact bodyOwned diagram (.cut current) regionBase nodeBase wireBase
        wireMap binders (by simpa [flattenItem] using allocated) record
        (by simpa [itemRecordBlock] using member)
  case bubble =>
      intro sourceWires sourceRels arity body bodyOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      exact bodyOwned diagram (.bubble current arity) regionBase nodeBase
        wireBase wireMap (binders.push regionBase)
        (by simpa [flattenItem] using allocated) record
        (by simpa [itemRecordBlock] using member)
  case nil =>
      intro sourceWires sourceRels openArity diagram current regionBase
        nodeBase wireBase wireMap binders allocated record member
      change record ∈ ([] : List RegionRecord) at member
      exact False.elim (List.not_mem_nil member)
  case cons =>
      intro sourceWires sourceRels head tail headOwned tailOwned
      intro openArity diagram current regionBase nodeBase wireBase wireMap
        binders allocated record member
      let headFlat := flattenItem current regionBase nodeBase wireBase
        wireMap binders head
      let tailFlat := flattenItems current
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wireMap binders tail
      have flatEq : flattenItems current regionBase nodeBase wireBase
          wireMap binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt (flattenOpen diagram)
          (headFlat.append tailFlat) regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths current regionBase nodeBase
        wireBase wireMap binders head
      rw [headLengths.1, headLengths.2.1, headLengths.2.2] at tailAllocated
      rw [itemRecords_cons, List.mem_append] at member
      by_cases hhead : record ∈ itemRecordBlock regionBase nodeBase
          wireBase head
      · exact headOwned diagram current regionBase nodeBase wireBase wireMap
          binders headAllocated record hhead
      · have member : record ∈ itemRecords
            (regionBase + (itemCounts head).regions)
            (nodeBase + (itemCounts head).nodes)
            (wireBase + (itemCounts head).wires) tail := by
          exact member.resolve_left hhead
        exact tailOwned diagram current
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) wireMap binders tailAllocated
          record member

private noncomputable def regionRecords_wires_owned (region : Region wires rels) :
    RegionRecordsWiresOwnedMotive wires rels region := by
  cases region with
  | mk localWires items =>
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders allocated record member
      simp only [regionRecords, List.mem_cons] at member
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders items).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders items).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      let nestedFlat := flattenItems regionBase (regionBase + 1) nodeBase
        (wireBase + localWires) (outerWires.extend wireBase localWires)
        binders items
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [flattenRegion, nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      by_cases hroot : record = {
          index := regionBase
          wireBase := wireBase
          localWires := localWires
          occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
        }
      · subst record
        have localAllocation : List.SegmentAt
            (flattenOpen diagram).wireScopes
            (List.replicate localWires regionBase) wireBase :=
          wireAllocation.left
        let current : Fin (rawDiagram diagram).regionCount :=
          ⟨regionBase, regionAllocation.index_lt ⟨0, by simp⟩⟩
        have wireEnd : wireBase + localWires ≤
            (flattenOpen diagram).wireScopes.length
            := by simpa using localAllocation.end_le
        refine ⟨current, wireEnd, rfl, ?_⟩
        intro localWire
        let slot : Fin (List.replicate localWires regionBase).length :=
          ⟨localWire.val, by simp⟩
        let wire : Fin (rawDiagram diagram).wireCount :=
          ⟨wireBase + localWire.val, localAllocation.index_lt slot⟩
        have scopeEq : (flattenOpen diagram).wireScopes.get wire =
            regionBase := by
          have lookup := localAllocation.get slot
          simpa [wire, slot] using lookup
        apply Fin.ext
        exact scopeEq
      · have member : record ∈ itemRecords (regionBase + 1) nodeBase
            (wireBase + localWires) items := by
          rcases member with heq | hmember
          · exact False.elim (hroot heq)
          · exact hmember
        exact itemRecords_wires_owned items diagram regionBase
          (regionBase + 1) nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) binders nestedAllocated
          record member

private noncomputable def openRegionRecords_wires_owned
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    ∀ record, record ∈ openRegionRecords diagram →
      record.WiresOwnedIn diagram := by
  let bodyFlat := flattenRegion .sheet 0 0 diagram.externalClasses
    (fun external => external.val) BinderMap.empty diagram.body
  have bodyAllocated : Flat.SegmentAt (flattenOpen diagram) bodyFlat
      0 0 diagram.externalClasses := by
    exact {
      regions := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
      nodes := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
      wireScopes := ⟨List.replicate diagram.externalClasses 0, [], by simp,
        by simp [flattenOpen, bodyFlat]⟩
    }
  intro record member
  exact regionRecords_wires_owned diagram.body diagram .sheet 0 0
    diagram.externalClasses (fun external => external.val) BinderMap.empty
    (by simpa [bodyFlat] using bodyAllocated) record
    (by simpa [openRegionRecords] using member)

private theorem rawDiagram_external_index_scope
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (wire : Fin (rawDiagram diagram).wireCount)
    (external : wire.val < diagram.externalClasses) :
    ((rawDiagram diagram).wires wire).scope = (rawDiagram diagram).root := by
  apply Fin.ext
  change (flattenOpen diagram).wireScopes.get wire = 0
  unfold flattenOpen
  simp only [List.get_eq_getElem]
  rw [List.getElem_append_left (by simpa using external)]
  simp

private structure ExactScopeCertificate
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord)
    (current : Fin (rawDiagram diagram).regionCount) where
  wireEnd : record.wireBase + record.localWires ≤
    (rawDiagram diagram).wireCount
  mem_iff : ∀ wire,
    wire ∈ Elaboration.exactScopeWires (rawDiagram diagram) current ↔
      wire ∈ wireSlice (rawDiagram diagram) record.wireBase
        record.localWires wireEnd

private noncomputable def record_exactScopeWires
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord)
    (recordMember : record ∈ openRegionRecords diagram)
    (current : Fin (rawDiagram diagram).regionCount)
    (currentIndex : current.val = record.index)
    (notRoot : current ≠ (rawDiagram diagram).root) :
    ExactScopeCertificate diagram record current := by
  obtain ⟨ownedCurrent, wireEnd, ownedIndex, localScope⟩ :=
    openRegionRecords_wires_owned diagram record recordMember
  have ownedCurrentEq : ownedCurrent = current := by
    apply Fin.ext
    exact ownedIndex.trans currentIndex.symm
  subst ownedCurrent
  refine ⟨wireEnd, ?_⟩
  intro wire
  constructor
  · intro exactScope
    have wireScope := (Elaboration.mem_exactScopeWires
      (rawDiagram diagram) current wire).mp exactScope
    have notExternalIndex : diagram.externalClasses ≤ wire.val := by
      apply Nat.le_of_not_gt
      intro lower
      have rootScope := rawDiagram_external_index_scope diagram wire (by omega)
      exact notRoot (wireScope.symm.trans rootScope)
    obtain ⟨candidate, candidateMember, localWire, wireEq⟩ :=
      openRegionRecords_wire_coverage diagram wire notExternalIndex
    obtain ⟨candidateCurrent, candidateEnd, candidateIndex,
        candidateScope⟩ :=
      openRegionRecords_wires_owned diagram candidate candidateMember
    let candidateWire : Fin (rawDiagram diagram).wireCount :=
      ⟨candidate.wireBase + localWire.val, by
        have := localWire.isLt
        exact Nat.lt_of_lt_of_le (by omega) candidateEnd⟩
    have concreteWireEq : candidateWire = wire := by
      apply Fin.ext
      exact wireEq.symm
    have candidateCurrentEq : candidateCurrent = current := by
      have scope := candidateScope localWire
      change ((rawDiagram diagram).wires candidateWire).scope =
        candidateCurrent at scope
      rw [concreteWireEq] at scope
      exact scope.symm.trans wireScope
    have recordsEq : candidate = record := by
      apply openRegionRecords_unique_index diagram candidateMember recordMember
      rw [← candidateIndex, ← currentIndex, candidateCurrentEq]
    subst candidate
    apply List.mem_ofFn.mpr
    refine ⟨localWire, ?_⟩
    apply Fin.ext
    simpa [wireSlice] using wireEq.symm
  · intro sliceMember
    rcases List.mem_ofFn.mp sliceMember with ⟨localWire, wireEq⟩
    apply (Elaboration.mem_exactScopeWires
      (rawDiagram diagram) current wire).mpr
    have scope := localScope localWire
    have concreteWireEq :
        (⟨record.wireBase + localWire.val, by
          have := localWire.isLt
          exact Nat.lt_of_lt_of_le (by omega) wireEnd⟩ :
          Fin (rawDiagram diagram).wireCount) = wire := by
      apply Fin.ext
      simpa [wireSlice] using congrArg Fin.val wireEq
    rw [concreteWireEq] at scope
    exact scope

private theorem record_hiddenWires
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (record : RegionRecord)
    (recordMember : record ∈ openRegionRecords diagram)
    (rootIndex : (rawDiagram diagram).root.val = record.index)
    (rootWireBase : record.wireBase = diagram.externalClasses) :
    ∃ wireEnd : record.wireBase + record.localWires ≤
        (rawDiagram diagram).wireCount,
      ∀ wire,
        wire ∈ (rawOpen diagram).hiddenWires ↔
          wire ∈ wireSlice (rawDiagram diagram) record.wireBase
            record.localWires wireEnd := by
  obtain ⟨ownedCurrent, wireEnd, ownedIndex, localScope⟩ :=
    openRegionRecords_wires_owned diagram record recordMember
  have ownedCurrentEq : ownedCurrent = (rawDiagram diagram).root := by
    apply Fin.ext
    exact ownedIndex.trans rootIndex.symm
  subst ownedCurrent
  refine ⟨wireEnd, ?_⟩
  intro wire
  constructor
  · intro hidden
    have hiddenFacts := (VisualProof.Concrete.OpenDiagram.mem_hiddenWires
      (rawOpen diagram) wire).mp hidden
    have notExternalIndex : diagram.externalClasses ≤ wire.val := by
      apply Nat.le_of_not_gt
      intro lower
      let external : Fin diagram.externalClasses := ⟨wire.val, by omega⟩
      have wireEq : wire = externalWire diagram external := by
        apply Fin.ext
        simp [externalWire, external]
      exact hiddenFacts.2 ((mem_rawOpen_exposedWires_iff diagram wire).mpr
        ((mem_externalWires diagram wire).mpr ⟨external, wireEq⟩))
    obtain ⟨candidate, candidateMember, localWire, wireEq⟩ :=
      openRegionRecords_wire_coverage diagram wire notExternalIndex
    obtain ⟨candidateCurrent, candidateEnd, candidateIndex,
        candidateScope⟩ :=
      openRegionRecords_wires_owned diagram candidate candidateMember
    let candidateWire : Fin (rawDiagram diagram).wireCount :=
      ⟨candidate.wireBase + localWire.val, by
        have := localWire.isLt
        exact Nat.lt_of_lt_of_le (by omega) candidateEnd⟩
    have concreteWireEq : candidateWire = wire := by
      apply Fin.ext
      exact wireEq.symm
    have candidateCurrentEq : candidateCurrent = (rawDiagram diagram).root := by
      have scope := candidateScope localWire
      change ((rawDiagram diagram).wires candidateWire).scope =
        candidateCurrent at scope
      rw [concreteWireEq] at scope
      exact scope.symm.trans hiddenFacts.1
    have recordsEq : candidate = record := by
      apply openRegionRecords_unique_index diagram candidateMember recordMember
      rw [← candidateIndex, ← rootIndex, candidateCurrentEq]
    subst candidate
    apply List.mem_ofFn.mpr
    refine ⟨localWire, ?_⟩
    apply Fin.ext
    simpa [wireSlice] using wireEq.symm
  · intro sliceMember
    rcases List.mem_ofFn.mp sliceMember with ⟨localWire, wireEq⟩
    apply (VisualProof.Concrete.OpenDiagram.mem_hiddenWires
      (rawOpen diagram) wire).mpr
    constructor
    · have scope := localScope localWire
      have concreteWireEq :
          (⟨record.wireBase + localWire.val, by
            have := localWire.isLt
            exact Nat.lt_of_lt_of_le (by omega) wireEnd⟩ :
            Fin (rawDiagram diagram).wireCount) = wire := by
        apply Fin.ext
        simpa [wireSlice] using congrArg Fin.val wireEq
      rw [concreteWireEq] at scope
      exact scope
    · intro exposed
      have exposedExternal :=
        (mem_rawOpen_exposedWires_iff diagram wire).mp exposed
      obtain ⟨external, externalEq⟩ :=
        (mem_externalWires diagram wire).mp exposedExternal
      have sliceVal : wire.val = record.wireBase + localWire.val := by
        simpa [wireSlice] using congrArg Fin.val wireEq.symm
      have externalVal : wire.val = external.val := by
        rw [externalEq]
        simp [externalWire]
      have := external.isLt
      omega

private def RegionPath
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (ancestor descendant : Nat) : Prop :=
  ∃ (ancestorBounded : ancestor < (rawDiagram diagram).regionCount)
    (descendantBounded : descendant < (rawDiagram diagram).regionCount)
    (steps : Nat),
    steps ≤ descendant ∧
      (rawDiagram diagram).climb steps ⟨descendant, descendantBounded⟩ =
        some ⟨ancestor, ancestorBounded⟩

private theorem RegionPath.refl
    (bounded : region < (rawDiagram diagram).regionCount) :
    RegionPath diagram region region := by
  exact ⟨bounded, bounded, 0, by omega, rfl⟩

private theorem RegionPath.descend
    (path : RegionPath diagram ancestor parent)
    (childBounded : child < (rawDiagram diagram).regionCount)
    (parentLt : parent < child)
    (concreteParent : Fin (rawDiagram diagram).regionCount)
    (parentVal : concreteParent.val = parent)
    (parentEq : ((rawDiagram diagram).regions
      ⟨child, childBounded⟩).parent? = some concreteParent) :
    RegionPath diagram ancestor child := by
  rcases path with ⟨ancestorBounded, parentBounded, steps, stepsLe, climb⟩
  have concreteParentEq : concreteParent = ⟨parent, parentBounded⟩ :=
    Fin.ext parentVal
  subst concreteParent
  refine ⟨ancestorBounded, childBounded, steps + 1, by omega, ?_⟩
  simp only [Diagram.climb]
  rw [parentEq]
  exact climb

private theorem RegionPath.encloses
    (path : RegionPath diagram ancestor descendant)
    (concreteAncestor concreteDescendant :
      Fin (rawDiagram diagram).regionCount)
    (ancestorVal : concreteAncestor.val = ancestor)
    (descendantVal : concreteDescendant.val = descendant) :
    (rawDiagram diagram).Encloses concreteAncestor concreteDescendant := by
  rcases path with
    ⟨ancestorBounded, descendantBounded, steps, stepsLe, climb⟩
  have ancestorEq : concreteAncestor = ⟨ancestor, ancestorBounded⟩ :=
    Fin.ext ancestorVal
  have descendantEq : concreteDescendant =
      ⟨descendant, descendantBounded⟩ := Fin.ext descendantVal
  subst concreteAncestor
  subst concreteDescendant
  exact ⟨⟨steps, by omega⟩, climb⟩

private def RegionDraft.OrderedAt (index : Nat) : RegionDraft → Prop
  | .sheet => index = 0
  | .cut parent => parent < index
  | .bubble parent _ => parent < index

private def RegionDraft.OrderedFrom : Nat → List RegionDraft → Prop
  | _, [] => True
  | index, head :: tail =>
      head.OrderedAt index ∧ OrderedFrom (index + 1) tail

private theorem RegionDraft.OrderedFrom.append
    (left right : List RegionDraft) :
    RegionDraft.OrderedFrom base (left ++ right) ↔
      RegionDraft.OrderedFrom base left ∧
        RegionDraft.OrderedFrom (base + left.length) right := by
  induction left generalizing base with
  | nil => simp [RegionDraft.OrderedFrom]
  | cons head tail ih =>
      simp only [List.cons_append, RegionDraft.OrderedFrom,
        List.length_cons]
      rw [ih]
      constructor
      · rintro ⟨headOrdered, tailOrdered, rightOrdered⟩
        exact ⟨⟨headOrdered, tailOrdered⟩, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rightOrdered⟩
      · rintro ⟨⟨headOrdered, tailOrdered⟩, rightOrdered⟩
        exact ⟨headOrdered, tailOrdered, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            rightOrdered⟩

private theorem RegionDraft.OrderedFrom.get
    (ordered : RegionDraft.OrderedFrom base regions)
    (index : Fin regions.length) :
    (regions.get index).OrderedAt (base + index.val) := by
  induction regions generalizing base with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      rcases ordered with ⟨headOrdered, tailOrdered⟩
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simpa using headOrdered
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih tailOrdered tailIndex

private def NodeDraft.ValidIn
    (diagram : VisualProof.Diagram.OpenDiagram openArity) : NodeDraft → Prop
  | .atom region binder nodeArity arguments =>
      ∃ (concreteRegion concreteBinder parent :
          Fin (rawDiagram diagram).regionCount),
        concreteRegion.val = region ∧
        concreteBinder.val = binder ∧
        (rawDiagram diagram).regions concreteBinder =
          .bubble parent nodeArity ∧
        RegionPath diagram binder region ∧
        ∀ port, ∃ wire : Fin (rawDiagram diagram).wireCount,
          wire.val = arguments port ∧
          RegionPath diagram ((rawDiagram diagram).wires wire).scope.val region
  | .identity region _ arguments =>
      ∀ port, ∃ wire : Fin (rawDiagram diagram).wireCount,
        wire.val = arguments port ∧
        RegionPath diagram ((rawDiagram diagram).wires wire).scope.val region

private def WireMap.ValidIn
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (wires : WireMap wireCount) (region : Nat) : Prop :=
  ∀ source, ∃ wire : Fin (rawDiagram diagram).wireCount,
    wire.val = wires source ∧
    RegionPath diagram ((rawDiagram diagram).wires wire).scope.val region

private def BinderMap.ValidIn
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (binders : BinderMap rels) (region : Nat) : Prop :=
  ∀ arity (relation : RelVar rels arity),
    ∃ (binder parent : Fin (rawDiagram diagram).regionCount),
      binder.val = binders arity relation ∧
      (rawDiagram diagram).regions binder = .bubble parent arity ∧
      RegionPath diagram binder.val region

private structure Flat.ValidAt
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (flat : Flat) (regionBase : Nat) : Prop where
  regions : RegionDraft.OrderedFrom regionBase flat.regions
  nodes : ∀ draft, draft ∈ flat.nodes → draft.ValidIn diagram

private theorem Flat.ValidAt.append
    {left right : Flat}
    (leftValid : Flat.ValidAt diagram left regionBase)
    (rightValid : Flat.ValidAt diagram right
      (regionBase + left.regions.length)) :
    Flat.ValidAt diagram (left.append right) regionBase := by
  exact {
    regions := (RegionDraft.OrderedFrom.append
      left.regions right.regions).mpr ⟨leftValid.regions, rightValid.regions⟩
    nodes := by
      intro draft member
      rcases List.mem_append.mp member with member | member
      · exact leftValid.nodes draft member
      · exact rightValid.nodes draft member
  }

private def RegionValidMotive
    (wireCount : Nat) (rels : RelCtx)
    (region : Region wireCount rels) : Prop :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap wireCount)
    (binders : BinderMap rels)
    (_allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenRegion regionKind regionBase nodeBase wireBase
        outerWires binders region) regionBase nodeBase wireBase),
    regionKind.OrderedAt regionBase →
    outerWires.ValidIn diagram regionBase →
    binders.ValidIn diagram regionBase →
    Flat.ValidAt diagram
      (flattenRegion regionKind regionBase nodeBase wireBase
        outerWires binders region) regionBase

private def ItemValidMotive
    (wireCount : Nat) (rels : RelCtx)
    (item : Item wireCount rels) : Prop :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels)
    (_allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItem currentRegion regionBase nodeBase wireBase
        wires binders item) regionBase nodeBase wireBase),
    currentRegion < regionBase →
    wires.ValidIn diagram currentRegion →
    binders.ValidIn diagram currentRegion →
    Flat.ValidAt diagram
      (flattenItem currentRegion regionBase nodeBase wireBase
        wires binders item) regionBase

private def ItemsValidMotive
    (wireCount : Nat) (rels : RelCtx)
    (items : ItemSeq wireCount rels) : Prop :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wires : WireMap wireCount)
    (binders : BinderMap rels)
    (_allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItems currentRegion regionBase nodeBase wireBase
        wires binders items) regionBase nodeBase wireBase),
    currentRegion < regionBase →
    wires.ValidIn diagram currentRegion →
    binders.ValidIn diagram currentRegion →
    Flat.ValidAt diagram
      (flattenItems currentRegion regionBase nodeBase wireBase
        wires binders items) regionBase

private theorem flattenItems_valid_core
    (items : ItemSeq wireCount rels) :
    ItemsValidMotive wireCount rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionValidMotive)
      (motive_2 := ItemValidMotive)
      (motive_3 := ItemsValidMotive)
  case mk =>
      intro sourceWires sourceRels localWires nested nestedValid
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders
        allocated kindOrdered outerValid bindersValid
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders nested).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders nested).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      have currentBounded :
          regionBase < (rawDiagram diagram).regionCount := by
        change regionBase < (flattenOpen diagram).regions.length
        exact regionAllocation.index_lt ⟨0, by simp⟩
      have localAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase) wireBase :=
        wireAllocation.left
      have currentWiresValid :
          (outerWires.extend wireBase localWires).ValidIn
            diagram regionBase := by
        intro source
        refine Fin.addCases (fun outerIndex => ?_)
          (fun localIndex => ?_) source
        · obtain ⟨wire, wireEq, path⟩ := outerValid outerIndex
          exact ⟨wire, by simpa [WireMap.extend] using wireEq, path⟩
        · let localSlot : Fin (List.replicate localWires regionBase).length :=
            ⟨localIndex.val, by simp⟩
          let wire : Fin (rawDiagram diagram).wireCount :=
            ⟨wireBase + localIndex.val, by
              change wireBase + localIndex.val <
                (flattenOpen diagram).wireScopes.length
              exact localAllocation.index_lt localSlot⟩
          have scopeEq : (flattenOpen diagram).wireScopes.get wire =
              regionBase := by
            have lookup := localAllocation.get localSlot
            simpa [localSlot] using lookup
          have rawScopeEq :
              ((rawDiagram diagram).wires wire).scope.val = regionBase := by
            exact scopeEq
          refine ⟨wire, ?_, ?_⟩
          · simp [wire, WireMap.extend]
          · rw [rawScopeEq]
            exact RegionPath.refl currentBounded
      let nestedFlat := flattenItems regionBase (regionBase + 1)
        nodeBase (wireBase + localWires)
        (outerWires.extend wireBase localWires) binders nested
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by
            simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      have nestedResult := nestedValid diagram regionBase (regionBase + 1)
        nodeBase (wireBase + localWires)
        (outerWires.extend wireBase localWires) binders nestedAllocated
        (by omega) currentWiresValid bindersValid
      exact {
        regions := ⟨kindOrdered, nestedResult.regions⟩
        nodes := nestedResult.nodes
      }
  case atom =>
      intro sourceRels nodeArity sourceWires relation arguments
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      obtain ⟨concreteBinder, parent, binderVal, bubbleEq, binderPath⟩ :=
        bindersValid nodeArity relation
      rcases binderPath with
        ⟨binderBounded, currentBounded, steps, stepsLe, climb⟩
      let concreteRegion : Fin (rawDiagram diagram).regionCount :=
        ⟨currentRegion, currentBounded⟩
      have restoredBinderPath : RegionPath diagram
          (binders nodeArity relation) currentRegion := by
        refine ⟨?_, currentBounded, steps, stepsLe, ?_⟩
        · simpa [binderVal] using binderBounded
        · simpa [binderVal] using climb
      have nodeValid :
          (NodeDraft.atom currentRegion (binders nodeArity relation)
            nodeArity (wires ∘ arguments)).ValidIn diagram := by
        refine ⟨concreteRegion, concreteBinder, parent, rfl, binderVal,
          bubbleEq, restoredBinderPath, ?_⟩
        intro port
        simpa using wiresValid (arguments port)
      exact {
        regions := by simp [flattenItem, RegionDraft.OrderedFrom]
        nodes := by
          intro draft member
          simp only [flattenItem, List.mem_singleton] at member
          subst draft
          exact nodeValid
      }
  case identity =>
      intro sourceWires sourceRels nodeArity arguments
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      exact {
        regions := by simp [flattenItem, RegionDraft.OrderedFrom]
        nodes := by
          intro draft member
          simp only [flattenItem, List.mem_singleton] at member
          subst draft
          intro port
          simpa using wiresValid (arguments port)
      }
  case cut =>
      intro sourceWires sourceRels body bodyValid
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      have childBounded :
          regionBase < (rawDiagram diagram).regionCount := by
        change regionBase < (flattenOpen diagram).regions.length
        exact allocated.regions.index_lt ⟨0, by
          simpa [flattenItem] using flattenRegion_regions_pos
            (.cut currentRegion) regionBase nodeBase wireBase
            wires binders body⟩
      let child : Fin (rawDiagram diagram).regionCount :=
        ⟨regionBase, childBounded⟩
      have childDraftEq : (flattenOpen diagram).regions.get child =
          .cut currentRegion := by
        have lookup := allocated.regions.get ⟨0, by
          simpa [flattenItem] using flattenRegion_regions_pos
            (.cut currentRegion) regionBase nodeBase wireBase
            wires binders body⟩
        exact lookup.trans (by
          simpa only [flattenItem] using flattenRegion_regions_get_zero
            (.cut currentRegion) regionBase nodeBase wireBase
            wires binders body)
      obtain ⟨concreteParent, childEq, parentVal⟩ :=
        rawDiagram_region_cut_lookup diagram child currentRegion childDraftEq
      have descendPath : ∀ {ancestor},
          RegionPath diagram ancestor currentRegion →
          RegionPath diagram ancestor regionBase := by
        intro ancestor path
        exact path.descend childBounded currentLt concreteParent parentVal (by
          rw [childEq]
          rfl)
      have childWiresValid : wires.ValidIn diagram regionBase := by
        intro source
        obtain ⟨wire, wireEq, path⟩ := wiresValid source
        exact ⟨wire, wireEq, descendPath path⟩
      have childBindersValid : binders.ValidIn diagram regionBase := by
        intro relationArity relation
        obtain ⟨binder, parent, binderVal, bubbleEq, path⟩ :=
          bindersValid relationArity relation
        exact ⟨binder, parent, binderVal, bubbleEq, descendPath path⟩
      exact bodyValid diagram (.cut currentRegion) regionBase nodeBase
        wireBase wires binders allocated currentLt childWiresValid
        childBindersValid
  case bubble =>
      intro sourceWires sourceRels binderArity body bodyValid
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      have childBounded :
          regionBase < (rawDiagram diagram).regionCount := by
        change regionBase < (flattenOpen diagram).regions.length
        exact allocated.regions.index_lt ⟨0, by
          simpa [flattenItem] using flattenRegion_regions_pos
            (.bubble currentRegion binderArity) regionBase nodeBase wireBase
            wires (binders.push regionBase) body⟩
      let child : Fin (rawDiagram diagram).regionCount :=
        ⟨regionBase, childBounded⟩
      have childDraftEq : (flattenOpen diagram).regions.get child =
          .bubble currentRegion binderArity := by
        have lookup := allocated.regions.get ⟨0, by
          simpa [flattenItem] using flattenRegion_regions_pos
            (.bubble currentRegion binderArity) regionBase nodeBase wireBase
            wires (binders.push regionBase) body⟩
        exact lookup.trans (by
          simpa only [flattenItem] using flattenRegion_regions_get_zero
            (.bubble currentRegion binderArity) regionBase nodeBase wireBase
            wires (binders.push regionBase) body)
      obtain ⟨concreteParent, childEq, parentVal⟩ :=
        rawDiagram_region_bubble_lookup diagram child currentRegion
          binderArity childDraftEq
      have descendPath : ∀ {ancestor},
          RegionPath diagram ancestor currentRegion →
          RegionPath diagram ancestor regionBase := by
        intro ancestor path
        exact path.descend childBounded currentLt concreteParent parentVal (by
          rw [childEq]
          rfl)
      have childWiresValid : wires.ValidIn diagram regionBase := by
        intro source
        obtain ⟨wire, wireEq, path⟩ := wiresValid source
        exact ⟨wire, wireEq, descendPath path⟩
      have inheritedBindersValid : binders.ValidIn diagram regionBase := by
        intro relationArity relation
        obtain ⟨binder, parent, binderVal, bubbleEq, path⟩ :=
          bindersValid relationArity relation
        exact ⟨binder, parent, binderVal, bubbleEq, descendPath path⟩
      have childBindersValid :
          (binders.push regionBase : BinderMap (binderArity :: sourceRels)).ValidIn
            diagram regionBase := by
        intro relationArity relation
        rcases relation with ⟨index, hasArity⟩
        revert hasArity
        refine Fin.cases ?_ (fun tailIndex => ?_) index
        · intro hasArity
          have arityEq : relationArity = binderArity := by
            simpa using hasArity.symm
          subst relationArity
          refine ⟨child, concreteParent, rfl, childEq, ?_⟩
          exact RegionPath.refl childBounded
        · intro hasArity
          let inherited : RelVar sourceRels relationArity := {
            index := tailIndex
            hasArity := by simpa using hasArity
          }
          obtain ⟨binder, parent, binderVal, bubbleEq, path⟩ :=
            inheritedBindersValid relationArity inherited
          refine ⟨binder, parent, ?_, bubbleEq, path⟩
          simpa [BinderMap.push, inherited]
      exact bodyValid diagram (.bubble currentRegion binderArity) regionBase
        nodeBase wireBase wires (binders.push regionBase) allocated currentLt
        childWiresValid childBindersValid
  case nil =>
      intro sourceWires sourceRels
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      exact {
        regions := by simp [flattenItems, Flat.empty,
          RegionDraft.OrderedFrom]
        nodes := by simp [flattenItems, Flat.empty]
      }
  case cons =>
      intro sourceWires sourceRels head tail headValid tailValid
      intro openArity diagram currentRegion regionBase nodeBase wireBase
        wires binders
        allocated currentLt wiresValid bindersValid
      let headFlat := flattenItem currentRegion regionBase nodeBase wireBase
        wires binders head
      let tailFlat := flattenItems currentRegion
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders tail
      have flatEq : flattenItems currentRegion regionBase nodeBase wireBase
          wires binders (.cons head tail) = headFlat.append tailFlat := by
        cases head <;> rfl
      have allocated' : Flat.SegmentAt (flattenOpen diagram)
          (headFlat.append tailFlat) regionBase nodeBase wireBase := by
        rw [← flatEq]
        exact allocated
      have headAllocated := allocated'.left
      have tailAllocated := allocated'.right
      have headLengths := flattenItem_lengths currentRegion regionBase nodeBase
        wireBase wires binders head
      have headRegionsLength : headFlat.regions.length =
          (itemCounts head).regions := by
        exact headLengths.1
      have headWiresLength : headFlat.wireScopes.length =
          (itemCounts head).wires := by
        exact headLengths.2.2
      have headNodesLength : headFlat.nodes.length =
          (itemCounts head).nodes := by
        exact headLengths.2.1
      rw [headRegionsLength, headNodesLength, headWiresLength] at tailAllocated
      have headResult := headValid diagram currentRegion regionBase nodeBase
        wireBase wires binders headAllocated currentLt wiresValid bindersValid
      have tailResult := tailValid diagram currentRegion
        (regionBase + (itemCounts head).regions)
        (nodeBase + (itemCounts head).nodes)
        (wireBase + (itemCounts head).wires) wires binders tailAllocated
        (by omega) wiresValid bindersValid
      rw [flatEq]
      exact Flat.ValidAt.append headResult (by
        simpa [headRegionsLength] using tailResult)

private theorem flattenRegion_valid_core
    (region : Region wireCount rels) :
    RegionValidMotive wireCount rels region := by
  cases region with
  | mk localWires nested =>
      intro openArity diagram regionKind regionBase nodeBase wireBase
        outerWires binders allocated kindOrdered outerValid bindersValid
      have regionAllocation : List.SegmentAt
          (flattenOpen diagram).regions
          (regionKind :: (flattenItems regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) binders nested).regions)
          regionBase := by
        simpa only [flattenRegion] using allocated.regions
      have wireAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase ++
            (flattenItems regionBase (regionBase + 1)
              nodeBase (wireBase + localWires)
              (outerWires.extend wireBase localWires) binders nested).wireScopes)
          wireBase := by
        simpa only [flattenRegion] using allocated.wireScopes
      have currentBounded :
          regionBase < (rawDiagram diagram).regionCount := by
        change regionBase < (flattenOpen diagram).regions.length
        exact regionAllocation.index_lt ⟨0, by simp⟩
      have localAllocation : List.SegmentAt
          (flattenOpen diagram).wireScopes
          (List.replicate localWires regionBase) wireBase :=
        wireAllocation.left
      have currentWiresValid :
          (outerWires.extend wireBase localWires).ValidIn
            diagram regionBase := by
        intro source
        refine Fin.addCases (fun outerIndex => ?_)
          (fun localIndex => ?_) source
        · obtain ⟨wire, wireEq, path⟩ := outerValid outerIndex
          exact ⟨wire, by simpa [WireMap.extend] using wireEq, path⟩
        · let localSlot : Fin (List.replicate localWires regionBase).length :=
            ⟨localIndex.val, by simp⟩
          let wire : Fin (rawDiagram diagram).wireCount :=
            ⟨wireBase + localIndex.val, by
              change wireBase + localIndex.val <
                (flattenOpen diagram).wireScopes.length
              exact localAllocation.index_lt localSlot⟩
          have scopeEq : (flattenOpen diagram).wireScopes.get wire =
              regionBase := by
            have lookup := localAllocation.get localSlot
            simpa [localSlot] using lookup
          have rawScopeEq :
              ((rawDiagram diagram).wires wire).scope.val = regionBase :=
            scopeEq
          refine ⟨wire, ?_, ?_⟩
          · simp [wire, WireMap.extend]
          · rw [rawScopeEq]
            exact RegionPath.refl currentBounded
      let nestedFlat := flattenItems regionBase (regionBase + 1)
        nodeBase (wireBase + localWires)
        (outerWires.extend wireBase localWires) binders nested
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          (regionBase + 1) nodeBase (wireBase + localWires) := by
        exact {
          regions := by
            simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [nestedFlat] using allocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires regionBase)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      have nestedResult := flattenItems_valid_core nested diagram regionBase
        (regionBase + 1) nodeBase (wireBase + localWires)
        (outerWires.extend wireBase localWires) binders nestedAllocated
        (by omega) currentWiresValid bindersValid
      exact {
        regions := ⟨kindOrdered, nestedResult.regions⟩
        nodes := nestedResult.nodes
      }

theorem Flat.Valid.diagram_wellFormed
    (valid : Flat.Valid diagram) :
    (rawDiagram diagram).WellFormed := by
  let d := rawDiagram diagram
  have rootVal : d.root.val = 0 := rfl
  have rootIsSheet : d.RootIsSheet := by
    cases kindEq : d.regions d.root with
    | sheet => exact kindEq
    | cut parent =>
        have ordered := valid.region_ordered d.root
        rw [kindEq] at ordered
        exact False.elim (by omega)
    | bubble parent binderArity =>
        have ordered := valid.region_ordered d.root
        rw [kindEq] at ordered
        exact False.elim (by omega)
  have onlyRootIsSheet : d.OnlyRootIsSheet := by
    intro region sheetEq
    have ordered := valid.region_ordered region
    rw [sheetEq] at ordered
    exact ordered
  have allReachRoot : d.AllRegionsReachRoot := by
    intro region
    have boundedClimb : ∃ steps : Nat, steps ≤ region.val ∧
        d.climb steps region = some d.root := by
      have general : ∀ n : Nat, ∀ candidate : Fin d.regionCount,
          candidate.val = n →
          ∃ steps : Nat, steps ≤ candidate.val ∧
            d.climb steps candidate = some d.root := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ih =>
            intro candidate candidateVal
            cases kindEq : d.regions candidate with
            | sheet =>
                have rootEq := valid.region_ordered candidate
                rw [kindEq] at rootEq
                subst candidate
                exact ⟨0, by omega, rfl⟩
            | cut parent =>
                have parentLt := valid.region_ordered candidate
                rw [kindEq] at parentLt
                obtain ⟨steps, stepsBound, climbEq⟩ :=
                  ih parent.val (by omega) parent rfl
                refine ⟨steps + 1, by omega, ?_⟩
                simpa [Diagram.climb, kindEq] using climbEq
            | bubble parent binderArity =>
                have parentLt := valid.region_ordered candidate
                rw [kindEq] at parentLt
                obtain ⟨steps, stepsBound, climbEq⟩ :=
                  ih parent.val (by omega) parent rfl
                refine ⟨steps + 1, by omega, ?_⟩
                simpa [Diagram.climb, kindEq] using climbEq
      exact general region.val region rfl
    obtain ⟨steps, stepsBound, climbEq⟩ := boundedClimb
    exact ⟨⟨steps, by have := region.isLt; omega⟩, climbEq⟩
  have atomBindersAreBubbles : d.AtomBindersAreBubbles := by
    intro node
    cases draftEq : (flattenOpen diagram).nodes.get node with
    | atom region binder nodeArity arguments =>
        have atomValid := valid.atom_valid node
        rw [draftEq] at atomValid
        obtain ⟨concreteRegion, concreteBinder, parent, nodeEq,
          binderEq, encloses⟩ := atomValid
        rw [nodeEq]
        exact ⟨parent, nodeArity, binderEq⟩
    | identity region nodeArity arguments =>
        obtain ⟨concreteRegion, nodeEq, regionVal⟩ :=
          rawDiagram_node_identity_lookup diagram node region nodeArity
            arguments draftEq
        rw [nodeEq]
        trivial
  have atomBindersEnclose : d.AtomBindersEnclose := by
    intro node
    cases draftEq : (flattenOpen diagram).nodes.get node with
    | atom region binder nodeArity arguments =>
        have atomValid := valid.atom_valid node
        rw [draftEq] at atomValid
        obtain ⟨concreteRegion, concreteBinder, parent, nodeEq,
          binderEq, encloses⟩ := atomValid
        rw [nodeEq]
        exact encloses
    | identity region nodeArity arguments =>
        obtain ⟨concreteRegion, nodeEq, regionVal⟩ :=
          rawDiagram_node_identity_lookup diagram node region nodeArity
            arguments draftEq
        rw [nodeEq]
        trivial
  have endpointsAreValid : d.EndpointsAreValid := by
    intro wire endpoint member
    rcases endpoint with ⟨node, ⟨index⟩⟩
    have argument := (mem_endpointsForWire_iff
      (flattenOpen diagram).nodes wire.val ⟨node, .arg index⟩).mp member
    cases draftEq : (flattenOpen diagram).nodes.get node with
    | atom region binder nodeArity arguments =>
        simp only [draftEq, NodeDraft.argument?, NodeDraft.arity] at argument
        split at argument
        · rename_i bound
          have atomValid := valid.atom_valid node
          rw [draftEq] at atomValid
          obtain ⟨concreteRegion, concreteBinder, parent, nodeEq,
            binderEq, encloses⟩ := atomValid
          apply (Diagram.requiresPort_atom_bubble_iff d node (.arg index)
            concreteRegion concreteBinder parent nodeArity nodeEq binderEq).mpr
          exact ⟨⟨index, bound⟩, rfl⟩
        · contradiction
    | identity region nodeArity arguments =>
        simp only [draftEq, NodeDraft.argument?, NodeDraft.arity] at argument
        split at argument
        · rename_i bound
          obtain ⟨concreteRegion, nodeEq, regionVal⟩ :=
            rawDiagram_node_identity_lookup diagram node region nodeArity
              arguments draftEq
          apply (Diagram.requiresPort_identity_iff d node (.arg index)
            concreteRegion nodeArity nodeEq).mpr
          exact ⟨⟨index, bound⟩, rfl⟩
        · contradiction
  have requiredPortsCovered : d.RequiredPortsAreCovered := by
    intro node
    cases draftEq : (flattenOpen diagram).nodes.get node with
    | atom region binder nodeArity arguments =>
        have atomValid := valid.atom_valid node
        rw [draftEq] at atomValid
        obtain ⟨concreteRegion, concreteBinder, parent, nodeEq,
          binderEq, encloses⟩ := atomValid
        rw [nodeEq]
        simp only
        rw [binderEq]
        intro port
        have arityEq : ((flattenOpen diagram).nodes.get node).arity =
            nodeArity := congrArg NodeDraft.arity draftEq
        let draftPort : Fin ((flattenOpen diagram).nodes.get node).arity :=
          Fin.cast arityEq.symm port
        obtain ⟨wire, wireEq, wireEncloses⟩ :=
          valid.argument_valid node draftPort
        refine ⟨wire, ?_⟩
        apply (mem_endpointsForWire_iff
          (flattenOpen diagram).nodes wire.val ⟨node, .arg port.val⟩).mpr
        simp only [NodeDraft.argument?]
        split
        · rename_i bound
          simp only [Option.some.injEq]
          have portEq : (⟨port.val, bound⟩ :
              Fin ((flattenOpen diagram).nodes.get node).arity) =
              draftPort := Fin.ext rfl
          rw [portEq]
          exact wireEq.symm
        · rename_i unbounded
          have bounded : port.val <
              ((flattenOpen diagram).nodes.get node).arity := by
            rw [arityEq]
            exact port.isLt
          contradiction
    | identity region nodeArity arguments =>
        obtain ⟨concreteRegion, nodeEq, regionVal⟩ :=
          rawDiagram_node_identity_lookup diagram node region nodeArity
            arguments draftEq
        rw [nodeEq]
        intro port
        have arityEq : ((flattenOpen diagram).nodes.get node).arity =
            nodeArity := congrArg NodeDraft.arity draftEq
        let draftPort : Fin ((flattenOpen diagram).nodes.get node).arity :=
          Fin.cast arityEq.symm port
        obtain ⟨wire, wireEq, wireEncloses⟩ :=
          valid.argument_valid node draftPort
        refine ⟨wire, ?_⟩
        apply (mem_endpointsForWire_iff
          (flattenOpen diagram).nodes wire.val ⟨node, .arg port.val⟩).mpr
        simp only [NodeDraft.argument?]
        split
        · rename_i bound
          simp only [Option.some.injEq]
          have portEq : (⟨port.val, bound⟩ :
              Fin ((flattenOpen diagram).nodes.get node).arity) =
              draftPort := Fin.ext rfl
          rw [portEq]
          exact wireEq.symm
        · rename_i unbounded
          have bounded : port.val <
              ((flattenOpen diagram).nodes.get node).arity := by
            rw [arityEq]
            exact port.isLt
          contradiction
  have wireScopesEnclose : d.WireScopesEnclose := by
    intro wire endpoint member
    rcases endpoint with ⟨node, ⟨index⟩⟩
    have argument := (mem_endpointsForWire_iff
      (flattenOpen diagram).nodes wire.val ⟨node, .arg index⟩).mp member
    simp only [NodeDraft.argument?] at argument
    split at argument
    · rename_i bound
      obtain ⟨mappedWire, mappedEq, mappedEncloses⟩ :=
        valid.argument_valid node ⟨index, bound⟩
      have wireEq : mappedWire = wire := by
        apply Fin.ext
        exact mappedEq.trans (Option.some.inj argument)
      subst mappedWire
      exact mappedEncloses
    · contradiction
  exact {
    root_is_sheet := rootIsSheet
    only_root_is_sheet := onlyRootIsSheet
    all_regions_reach_root := allReachRoot
    atom_binders_are_bubbles := atomBindersAreBubbles
    atom_binders_enclose := atomBindersEnclose
    endpoints_are_valid := endpointsAreValid
    endpoints_are_nodup := fun wire => endpointsForWire_nodup _ wire.val
    wire_endpoints_are_disjoint := by
      intro left right different endpoint leftMember
      have different' : left.val ≠ right.val := by
        intro valuesEq
        have finEq : left = right := Fin.ext valuesEq
        subst right
        simp at different
      have disjoint := endpointsForWire_disjoint
        (nodes := (flattenOpen diagram).nodes)
        (left := left.val) (right := right.val) different'
        endpoint leftMember
      change (!decide (endpoint ∈ endpointsForWire
        (flattenOpen diagram).nodes right.val)) = true
      rw [Bool.not_eq_true', decide_eq_false_iff_not]
      exact disjoint
    required_ports_are_covered := requiredPortsCovered
    wire_scopes_enclose := wireScopesEnclose
  }

@[simp] theorem rawDiagram_externalWire_scope
    (diagram : VisualProof.Diagram.OpenDiagram arity)
    (external : Fin diagram.externalClasses) :
    ((rawDiagram diagram).wires (externalWire diagram external)).scope =
      (rawDiagram diagram).root := by
  apply Fin.ext
  simp [rawDiagram, externalWire, flattenOpen]

theorem flattenOpen_valid
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    Flat.Valid diagram := by
  let bodyFlat := flattenRegion .sheet 0 0 diagram.externalClasses
    (fun external => external.val) BinderMap.empty diagram.body
  have bodyAllocated : Flat.SegmentAt (flattenOpen diagram) bodyFlat
      0 0 diagram.externalClasses := by
    exact {
      regions := ⟨[], [], rfl, by
        simp [flattenOpen, bodyFlat]⟩
      nodes := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
      wireScopes := ⟨List.replicate diagram.externalClasses 0, [], by simp,
        by simp [flattenOpen, bodyFlat]⟩
    }
  have rootBounded : 0 < (rawDiagram diagram).regionCount := by
    exact flattenOpen_regions_pos diagram
  have outerValid :
      WireMap.ValidIn diagram (fun external : Fin diagram.externalClasses =>
        external.val) 0 := by
    intro external
    let wire := externalWire diagram external
    refine ⟨wire, rfl, ?_⟩
    have scopeEq := rawDiagram_externalWire_scope diagram external
    change RegionPath diagram
      ((rawDiagram diagram).wires wire).scope.val 0
    rw [scopeEq]
    exact RegionPath.refl rootBounded
  have bindersValid : BinderMap.ValidIn diagram BinderMap.empty 0 := by
    intro relationArity relation
    exact Fin.elim0 relation.index
  have bodyValid : Flat.ValidAt diagram bodyFlat 0 :=
    flattenRegion_valid_core diagram.body diagram .sheet 0 0
      diagram.externalClasses (fun external => external.val) BinderMap.empty
      bodyAllocated (by rfl) outerValid bindersValid
  exact {
    region_ordered := by
      intro region
      have bodyRegionsLength : bodyFlat.regions.length =
          (flattenOpen diagram).regions.length := by
        rfl
      let bodyRegion : Fin bodyFlat.regions.length :=
        ⟨region.val, by
          rw [bodyRegionsLength]
          exact region.isLt⟩
      have draftOrdered := bodyValid.regions.get bodyRegion
      have ordered : ((flattenOpen diagram).regions.get region).OrderedAt
          region.val := by
        simpa [bodyFlat, bodyRegion, flattenOpen] using draftOrdered
      cases draftEq : (flattenOpen diagram).regions.get region with
      | sheet =>
          rw [draftEq] at ordered
          have concreteEq := rawDiagram_region_sheet_lookup
            diagram region draftEq
          rw [concreteEq]
          apply Fin.ext
          exact ordered
      | cut parent =>
          rw [draftEq] at ordered
          obtain ⟨concreteParent, concreteEq, parentVal⟩ :=
            rawDiagram_region_cut_lookup diagram region parent draftEq
          rw [concreteEq]
          simpa [parentVal] using ordered
      | bubble parent binderArity =>
          rw [draftEq] at ordered
          obtain ⟨concreteParent, concreteEq, parentVal⟩ :=
            rawDiagram_region_bubble_lookup diagram region parent
              binderArity draftEq
          rw [concreteEq]
          simpa [parentVal] using ordered
    atom_valid := by
      intro node
      let draft := (flattenOpen diagram).nodes.get node
      have draftMember : draft ∈ bodyFlat.nodes := by
        change draft ∈ (flattenOpen diagram).nodes
        exact List.get_mem (flattenOpen diagram).nodes node
      have semantic := bodyValid.nodes draft draftMember
      cases draftEq : (flattenOpen diagram).nodes.get node with
      | atom region binder nodeArity arguments =>
          have draftEq' : draft =
              .atom region binder nodeArity arguments := by
            exact draftEq
          rw [draftEq'] at semantic
          obtain ⟨validRegion, validBinder, parent, validRegionVal,
            validBinderVal, bubbleEq, binderPath, argumentsValid⟩ := semantic
          obtain ⟨concreteRegion, concreteBinder, nodeEq,
            concreteRegionVal, concreteBinderVal⟩ :=
              rawDiagram_node_atom_lookup diagram node region binder
                nodeArity arguments draftEq
          have validBinderEq : validBinder = concreteBinder :=
            Fin.ext (validBinderVal.trans concreteBinderVal.symm)
          have bubbleEq' : (rawDiagram diagram).regions concreteBinder =
              .bubble parent nodeArity := by
            simpa [validBinderEq] using bubbleEq
          refine ⟨concreteRegion, concreteBinder, parent, nodeEq,
            bubbleEq', ?_⟩
          exact binderPath.encloses concreteBinder concreteRegion
            concreteBinderVal concreteRegionVal
      | identity region nodeArity arguments =>
          trivial
    argument_valid := by
      intro node
      generalize draftEq : (flattenOpen diagram).nodes.get node = draft
      intro port
      have draftMember : draft ∈ bodyFlat.nodes := by
        have member := List.get_mem (flattenOpen diagram).nodes node
        rw [draftEq] at member
        simpa [bodyFlat, flattenOpen] using member
      have semantic := bodyValid.nodes draft draftMember
      cases draft with
      | atom region binder nodeArity arguments =>
          obtain ⟨validRegion, validBinder, parent, validRegionVal,
            validBinderVal, bubbleEq, binderPath, argumentsValid⟩ := semantic
          obtain ⟨wire, wireVal, wirePath⟩ := argumentsValid port
          obtain ⟨concreteRegion, concreteBinder, nodeEq,
            concreteRegionVal, concreteBinderVal⟩ :=
              rawDiagram_node_atom_lookup diagram node region binder
                nodeArity arguments draftEq
          refine ⟨wire, wireVal, ?_⟩
          rw [nodeEq]
          exact wirePath.encloses ((rawDiagram diagram).wires wire).scope
            concreteRegion rfl concreteRegionVal
      | identity region nodeArity arguments =>
          obtain ⟨wire, wireVal, wirePath⟩ := semantic port
          obtain ⟨concreteRegion, nodeEq, concreteRegionVal⟩ :=
            rawDiagram_node_identity_lookup diagram node region nodeArity
              arguments draftEq
          refine ⟨wire, wireVal, ?_⟩
          rw [nodeEq]
          exact wirePath.encloses ((rawDiagram diagram).wires wire).scope
            concreteRegion rfl concreteRegionVal
  }

theorem rawOpen_boundary_root_scoped
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    ∀ wire, wire ∈ (rawOpen diagram).boundary →
      ((rawDiagram diagram).wires wire).scope =
        (rawDiagram diagram).root := by
  intro wire member
  rw [List.mem_iff_get] at member
  rcases member with ⟨position, rfl⟩
  rw [rawOpen_boundary_get]
  exact rawDiagram_externalWire_scope diagram _

theorem Flat.Valid.open_wellFormed
    (valid : Flat.Valid diagram) : (rawOpen diagram).WellFormed where
  diagram_well_formed := valid.diagram_wellFormed
  boundary_is_root_scoped := rawOpen_boundary_root_scoped diagram

theorem rawOpen_wellFormed
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (rawOpen diagram).WellFormed :=
  (flattenOpen_valid diagram).open_wellFormed

private theorem rawDiagram_wellFormed
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    (rawDiagram diagram).WellFormed := by
  simpa only [rawOpen] using (rawOpen_wellFormed diagram).diagram_well_formed

private def castFinEquiv {source source' target target' : Nat}
    (sourceEq : source = source') (targetEq : target' = target)
    (equiv : FiniteEquiv (Fin source) (Fin target)) :
    FiniteEquiv (Fin source') (Fin target') :=
  (FiniteEquiv.finCast sourceEq.symm).trans
    (equiv.trans (FiniteEquiv.finCast targetEq.symm))

private noncomputable def regionIso_of_target_cast
    {sourceOuter targetOuter sourceLocal targetLocal targetFull : Nat}
    {rels : RelCtx}
    (targetEq : targetFull = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq (sourceOuter + sourceLocal) rels)
    (targetItems : ItemSeq targetFull rels)
    (items : ItemSeqIso
      (castFinEquiv rfl targetEq (extendWireEquiv ambient localEquiv)) rels
      sourceItems targetItems) :
    RegionIso ambient rels (.mk sourceLocal sourceItems)
      (.mk targetLocal (targetItems.castWiresEq targetEq)) := by
  subst targetFull
  simpa [castFinEquiv, FiniteEquiv.finCast] using
    RegionIso.mk localEquiv items

private structure WireMap.ContextAgreement
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (wires : WireMap sourceWires)
    (context : Elaboration.WireContext (rawDiagram diagram))
    (equiv : FiniteEquiv (Fin sourceWires) (Fin context.length)) : Prop where
  bounded : ∀ source, wires source < (rawDiagram diagram).wireCount
  lookup : ∀ source,
    context.get (equiv source) = ⟨wires source, bounded source⟩

private theorem WireMap.ContextAgreement.append
    {openArity sourceWires : Nat}
    {diagram : VisualProof.Diagram.OpenDiagram openArity}
    {outerWires : WireMap sourceWires}
    {context : Elaboration.WireContext (rawDiagram diagram)}
    {outerEquiv : FiniteEquiv (Fin sourceWires) (Fin context.length)}
    (agreement : WireMap.ContextAgreement diagram outerWires context outerEquiv)
    (wireBase localWires : Nat)
    (locals : Elaboration.WireContext (rawDiagram diagram))
    (localBound : wireBase + localWires ≤ (rawDiagram diagram).wireCount)
    (localEquiv : FiniteEquiv (Fin localWires) (Fin locals.length))
    (localLookup : ∀ localIndex,
      locals.get (localEquiv localIndex) =
        (⟨wireBase + localIndex.val, by omega⟩ :
          Fin (rawDiagram diagram).wireCount)) :
    WireMap.ContextAgreement diagram
      (outerWires.extend wireBase localWires) (context ++ locals)
      (castFinEquiv rfl
        (List.length_append (as := context) (bs := locals))
        (extendWireEquiv outerEquiv localEquiv)) := by
  exact {
    bounded := by
      intro source
      exact Fin.addCases
        (fun outer => by
          simpa [WireMap.extend] using agreement.bounded outer)
        (fun localIndex => by
          simp only [WireMap.extend, Fin.addCases_right]
          have := localIndex.isLt
          omega) source
    lookup := by
      intro source
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) source
      · simp only [castFinEquiv, FiniteEquiv.trans_apply,
          FiniteEquiv.finCast, Fin.cast_refl, id_eq, extendWireEquiv_outer]
        have outerBound :
            (Fin.cast (List.length_append (as := context) (bs := locals)).symm
              (Fin.castAdd locals.length (outerEquiv outer))).val <
              context.length := by simp
        rw [List.get_eq_getElem, List.getElem_append_left outerBound]
        simpa [WireMap.extend] using agreement.lookup outer
      · simp only [castFinEquiv, FiniteEquiv.trans_apply,
          FiniteEquiv.finCast, Fin.cast_refl, id_eq, extendWireEquiv_local]
        have localAfter : context.length ≤
            (Fin.cast (List.length_append (as := context) (bs := locals)).symm
              (Fin.natAdd context.length (localEquiv localIndex))).val := by simp
        rw [List.get_eq_getElem, List.getElem_append_right localAfter]
        simpa [WireMap.extend] using localLookup localIndex
  }

private def BinderMap.ContextAgreement
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (binders : BinderMap rels)
    (context : Elaboration.BinderContext (rawDiagram diagram) rels) : Prop :=
  ∀ arity (relation : RelVar rels arity),
    ∃ bounded : binders arity relation < (rawDiagram diagram).regionCount,
      context ⟨binders arity relation, bounded⟩ = some ⟨arity, relation⟩

private theorem BinderMap.empty_contextAgreement
    (diagram : VisualProof.Diagram.OpenDiagram openArity) :
    BinderMap.ContextAgreement diagram BinderMap.empty
      Elaboration.BinderContext.empty := by
  intro arity relation
  exact Fin.elim0 relation.index

private theorem BinderMap.ContextAgreement.push
    {openArity : Nat}
    {diagram : VisualProof.Diagram.OpenDiagram openArity}
    {binders : BinderMap rels}
    {context : Elaboration.BinderContext (rawDiagram diagram) rels}
    (agreement : BinderMap.ContextAgreement diagram binders context)
    (binderBase : Nat)
    (binder : Fin (rawDiagram diagram).regionCount)
    (binderValue : binder.val = binderBase)
    (outerBefore : binders.Bounded binderBase) :
    BinderMap.ContextAgreement diagram
      (@BinderMap.push rels binderArity binders binderBase)
      (context.push binder binderArity) := by
  intro relationArity relation
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · intro hasArity
    have arityEq : relationArity = binderArity := by simpa using hasArity.symm
    have mapHeadEq : BinderMap.push binders binderBase relationArity
        ⟨0, hasArity⟩ = binderBase := by simp [BinderMap.push]
    have mapHeadBounded : BinderMap.push binders binderBase relationArity
        ⟨0, hasArity⟩ < (rawDiagram diagram).regionCount := by
      rw [mapHeadEq, ← binderValue]
      exact binder.isLt
    refine ⟨mapHeadBounded, ?_⟩
    have candidateEq :
        (⟨BinderMap.push binders binderBase relationArity ⟨0, hasArity⟩,
          mapHeadBounded⟩ : Fin (rawDiagram diagram).regionCount) = binder := by
      apply Fin.ext
      exact mapHeadEq.trans binderValue.symm
    rw [candidateEq, Elaboration.BinderContext.push_self]
    cases arityEq
    rfl
  · intro hasArity
    let inherited : RelVar rels relationArity := {
      index := tailIndex
      hasArity := by simpa using hasArity
    }
    obtain ⟨inheritedBounded, inheritedLookup⟩ :=
      agreement relationArity inherited
    have mapEq : BinderMap.push binders binderBase relationArity
        ⟨tailIndex.succ, hasArity⟩ = binders relationArity inherited := by
      simp [BinderMap.push, inherited]
    have candidateNe :
        (⟨binders relationArity inherited, inheritedBounded⟩ :
          Fin (rawDiagram diagram).regionCount) ≠ binder := by
      intro equal
      have equalVal := congrArg Fin.val equal
      have before := outerBefore relationArity inherited
      change binders relationArity inherited = binder.val at equalVal
      omega
    have mapBounded : BinderMap.push binders binderBase relationArity
        ⟨tailIndex.succ, hasArity⟩ < (rawDiagram diagram).regionCount := by
      rw [mapEq]
      exact inheritedBounded
    refine ⟨mapBounded, ?_⟩
    have candidateFinEq :
        (⟨BinderMap.push binders binderBase relationArity
            ⟨tailIndex.succ, hasArity⟩, mapBounded⟩ :
          Fin (rawDiagram diagram).regionCount) =
        ⟨binders relationArity inherited, inheritedBounded⟩ := Fin.ext mapEq
    rw [candidateFinEq, Elaboration.BinderContext.push_other _ _ candidateNe,
      inheritedLookup]
    simp [Elaboration.BinderContext.liftVar, inherited]

private theorem rawDiagram_argument_occurs
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (port : Fin ((flattenOpen diagram).nodes.get node).arity)
    (wire : Fin (rawDiagram diagram).wireCount)
    (wireValue : wire.val =
      ((flattenOpen diagram).nodes.get node).argument port) :
    (rawDiagram diagram).EndpointOccurs wire
      ⟨node, .arg port.val⟩ := by
  apply (mem_endpointsForWire_iff (flattenOpen diagram).nodes wire.val
    ⟨node, .arg port.val⟩).mpr
  simp only [NodeDraft.argument?]
  split
  · rename_i bounded
    have portEq :
        (⟨port.val, bounded⟩ :
          Fin ((flattenOpen diagram).nodes.get node).arity) = port :=
      Fin.ext rfl
    rw [portEq]
    exact congrArg some wireValue.symm
  · rename_i unbounded
    exact False.elim (unbounded port.isLt)

private theorem WireMap.ContextAgreement.position
    {diagram : VisualProof.Diagram.OpenDiagram openArity}
    {wires : WireMap sourceWires}
    {context : Elaboration.WireContext (rawDiagram diagram)}
    {equiv : FiniteEquiv (Fin sourceWires) (Fin context.length)}
    {parent : Fin (rawDiagram diagram).regionCount}
    (agreement : WireMap.ContextAgreement diagram wires context equiv)
    (exact : context.Exact parent) (source : Fin sourceWires)
    (owner : Fin (rawDiagram diagram).wireCount)
    (ownerEq : owner = ⟨wires source, agreement.bounded source⟩)
    (visible : (rawDiagram diagram).Encloses
      ((rawDiagram diagram).wires owner).scope parent) :
    context.position exact owner visible = equiv source := by
  apply Fin.ext
  exact (List.getElem_inj exact.nodup).mp (by
    simpa only [List.get_eq_getElem] using
      (Elaboration.WireContext.position_get exact owner visible).trans
        (ownerEq.trans (agreement.lookup source).symm))

private def itemOccurrenceDraft
    (regionBase nodeBase : Nat) : Item wires rels → OccurrenceDraft
  | .atom _ _ | .identity _ _ => .node nodeBase
  | .cut _ | .bubble _ _ => .child regionBase

private theorem occurrenceDrafts_cons
    (head : Item wires rels) (tail : ItemSeq wires rels) :
    occurrenceDrafts regionBase nodeBase (.cons head tail) =
      itemOccurrenceDraft regionBase nodeBase head ::
        occurrenceDrafts (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes) tail := by
  cases head <;> rfl

private theorem realizeOccurrenceDrafts_get
    {d : Diagram}
    (drafts : List OccurrenceDraft)
    (bounded : ∀ draft, draft ∈ drafts →
      draft.Bounded d.regionCount d.nodeCount)
    (index : Fin drafts.length) :
    (realizeOccurrenceDrafts drafts bounded).get ⟨index.val, by simp⟩ =
      (drafts.get index).toConcrete
        (bounded (drafts.get index) (List.get_mem drafts index)) := by
  induction drafts with
  | nil => exact Fin.elim0 index
  | cons head tail ih =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · simp [realizeOccurrenceDrafts]

private theorem List.get_cast
    {first second : List α} (equal : first = second)
    (index : Fin first.length) :
    first.get index = second.get (Fin.cast (congrArg List.length equal) index) := by
  subst second
  rfl

private theorem OccurrenceDraft.toConcrete_congr
    {d : Diagram} {first second : OccurrenceDraft}
    (equal : first = second)
    (bounded : first.Bounded d.regionCount d.nodeCount) :
    first.toConcrete bounded = second.toConcrete (equal ▸ bounded) := by
  subst second
  rfl

private theorem NodeDraft.argument_of_atom
    {region binder arity : Nat} {arguments : Fin arity → Nat}
    {draft : NodeDraft}
    (draftEq : draft = .atom region binder arity arguments)
    (port : Fin arity) :
    draft.argument (Fin.cast (congrArg NodeDraft.arity draftEq).symm port) =
      arguments port := by
  subst draft
  rfl

private theorem NodeDraft.argument_of_identity
    {region arity : Nat} {arguments : Fin arity → Nat}
    {draft : NodeDraft}
    (draftEq : draft = .identity region arity arguments)
    (port : Fin arity) :
    draft.argument (Fin.cast (congrArg NodeDraft.arity draftEq).symm port) =
      arguments port := by
  subst draft
  rfl

private def RegionEncodingMotive
    (sourceWires : Nat) (rels : RelCtx)
    (source : Region sourceWires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (regionKind : RegionDraft)
    (regionBase nodeBase wireBase : Nat)
    (outerWires : WireMap sourceWires)
    (sourceBinders : BinderMap rels)
    (_allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenRegion regionKind regionBase nodeBase wireBase
        outerWires sourceBinders source) regionBase nodeBase wireBase)
    (_recordsIncluded : ∀ record,
      record ∈ regionRecords regionBase nodeBase wireBase source →
        record ∈ openRegionRecords diagram)
    (_bindersBefore : sourceBinders.Bounded (regionBase + 1))
    (current : Fin (rawDiagram diagram).regionCount)
    (_currentValue : current.val = regionBase)
    (_notRoot : current ≠ (rawDiagram diagram).root)
    (context : Elaboration.WireContext (rawDiagram diagram))
    (wireEquiv : FiniteEquiv (Fin sourceWires) (Fin context.length))
    (_wireAgreement : WireMap.ContextAgreement diagram outerWires context
      wireEquiv)
    (binderContext : Elaboration.BinderContext (rawDiagram diagram) rels)
    (_binderAgreement : BinderMap.ContextAgreement diagram sourceBinders
      binderContext)
    (_binderCovers : binderContext.Covers current)
    (_extendedExact : (context.extend current).Exact current)
    (target : Elaboration.CompiledRegion (rawDiagram diagram))
    (_targetOrigin : target.origin = current)
    (_targetValid : target.Valid),
    RegionIso wireEquiv rels source
      (target.erase _targetValid (rawDiagram_wellFormed diagram)
        context (Elaboration.exactScopeWires (rawDiagram diagram) current)
        rels binderContext (by
          rw [_targetOrigin]
          simpa [Elaboration.WireContext.extend] using _extendedExact)
        (by simpa [_targetOrigin] using _binderCovers))

private def ItemEncodingMotive
    (sourceWires : Nat) (rels : RelCtx)
    (source : Item sourceWires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap sourceWires)
    (sourceBinders : BinderMap rels)
    (_allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItem currentRegion regionBase nodeBase wireBase
        wireMap sourceBinders source) regionBase nodeBase wireBase)
    (_recordsIncluded : ∀ record,
      record ∈ itemRecordBlock regionBase nodeBase wireBase source →
        record ∈ openRegionRecords diagram)
    (_bindersBefore : sourceBinders.Bounded regionBase)
    (current : Fin (rawDiagram diagram).regionCount)
    (_currentValue : current.val = currentRegion)
    (_currentBefore : currentRegion < regionBase)
    (context : Elaboration.WireContext (rawDiagram diagram))
    (wireEquiv : FiniteEquiv (Fin sourceWires) (Fin context.length))
    (_wireAgreement : WireMap.ContextAgreement diagram wireMap context
      wireEquiv)
    (_contextExact : context.Exact current)
    (binderContext : Elaboration.BinderContext (rawDiagram diagram) rels)
    (_binderAgreement : BinderMap.ContextAgreement diagram sourceBinders
      binderContext)
    (_binderCovers : binderContext.Covers current)
    (draftBounded : (itemOccurrenceDraft regionBase nodeBase source).Bounded
      (rawDiagram diagram).regionCount (rawDiagram diagram).nodeCount)
    (target : Elaboration.CompiledItem (rawDiagram diagram))
    (_targetOrigin : target.origin =
      (itemOccurrenceDraft regionBase nodeBase source).toConcrete draftBounded)
    (_targetValid : target.ValidAt current),
    ItemIso wireEquiv rels source
      (target.erase _targetValid (rawDiagram_wellFormed diagram) context rels
        binderContext _contextExact _binderCovers)

private def ItemsEncodingMotive
    (sourceWires : Nat) (rels : RelCtx)
    (source : ItemSeq sourceWires rels) : Type :=
  ∀ {openArity : Nat}
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (currentRegion regionBase nodeBase wireBase : Nat)
    (wireMap : WireMap sourceWires)
    (sourceBinders : BinderMap rels)
    (allocated : Flat.SegmentAt (flattenOpen diagram)
      (flattenItems currentRegion regionBase nodeBase wireBase
        wireMap sourceBinders source) regionBase nodeBase wireBase)
    (_recordsIncluded : ∀ record,
      record ∈ itemRecords regionBase nodeBase wireBase source →
        record ∈ openRegionRecords diagram)
    (_bindersBefore : sourceBinders.Bounded regionBase)
    (current : Fin (rawDiagram diagram).regionCount)
    (_currentValue : current.val = currentRegion)
    (_currentBefore : currentRegion < regionBase)
    (context : Elaboration.WireContext (rawDiagram diagram))
    (wireEquiv : FiniteEquiv (Fin sourceWires) (Fin context.length))
    (_wireAgreement : WireMap.ContextAgreement diagram wireMap context
      wireEquiv)
    (_contextExact : context.Exact current)
    (binderContext : Elaboration.BinderContext (rawDiagram diagram) rels)
    (_binderAgreement : BinderMap.ContextAgreement diagram sourceBinders
      binderContext)
    (_binderCovers : binderContext.Covers current)
    (index : Fin (occurrenceDrafts regionBase nodeBase source).length)
    (target : Elaboration.CompiledItem (rawDiagram diagram))
    (_targetOrigin : target.origin =
      ((occurrenceDrafts regionBase nodeBase source).get index |>.toConcrete
        (occurrenceDrafts_bounded diagram currentRegion regionBase nodeBase
          wireBase wireMap sourceBinders source allocated _
          (List.get_mem _ index))))
    (_targetValid : target.ValidAt current),
    ItemIso wireEquiv rels
      (source.get (Fin.cast (occurrenceDrafts_length source) index))
      (target.erase _targetValid (rawDiagram_wellFormed diagram) context rels
        binderContext _contextExact _binderCovers)

private structure EncodedAtomValidity
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (node : Fin (rawDiagram diagram).nodeCount) (arity : Nat) where
  region : Fin (rawDiagram diagram).regionCount
  binder : Fin (rawDiagram diagram).regionCount
  parent : Fin (rawDiagram diagram).regionCount
  node_eq : (rawDiagram diagram).nodes node = .atom region binder
  binder_eq : (rawDiagram diagram).regions binder = .bubble parent arity
  binder_encloses : (rawDiagram diagram).Encloses binder region

private noncomputable def encodedAtomValidity
    (diagram : VisualProof.Diagram.OpenDiagram openArity)
    (node : Fin (rawDiagram diagram).nodeCount)
    (region binder arity : Nat) (arguments : Fin arity → Nat)
    (draftEq : (flattenOpen diagram).nodes.get node =
      .atom region binder arity arguments) :
    EncodedAtomValidity diagram node arity := by
  have existsValidity := (flattenOpen_valid diagram).atom_valid node
  rw [draftEq] at existsValidity
  let concreteRegion := Classical.choose existsValidity
  have regionSpec := Classical.choose_spec existsValidity
  let concreteBinder := Classical.choose regionSpec
  have binderSpec := Classical.choose_spec regionSpec
  let concreteParent := Classical.choose binderSpec
  have facts := Classical.choose_spec binderSpec
  exact ⟨concreteRegion, concreteBinder, concreteParent,
    facts.1, facts.2.1, facts.2.2⟩

private noncomputable def encodeAtomMotive
    (relation : RelVar rels arity)
    (arguments : Fin arity → Fin sourceWires) :
    ItemEncodingMotive sourceWires rels (.atom relation arguments) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers draftBounded target targetOrigin targetValid
  let node : Fin (rawDiagram diagram).nodeCount := ⟨nodeBase, draftBounded⟩
  have nodeAllocation : List.SegmentAt (flattenOpen diagram).nodes
      [.atom currentRegion (sourceBinders arity relation) arity
        (wireMap ∘ arguments)] nodeBase := by
    simpa [flattenItem] using allocated.nodes
  have draftEq : (flattenOpen diagram).nodes.get node =
      .atom current.val (sourceBinders arity relation) arity
        (wireMap ∘ arguments) := by
    have lookup := nodeAllocation.get (0 : Fin 1)
    rw [currentValue]
    simpa [node] using lookup
  let expected := encodedAtomValidity diagram node current.val
    (sourceBinders arity relation) arity (wireMap ∘ arguments) draftEq
  cases target with
  | atom targetNode targetBinder targetArity targetPorts =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.node.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      subst targetNode
      have regionEq : expected.region = current := by
        have shapes := expected.node_eq.symm.trans targetValid.1
        exact (CNode.atom.inj shapes).1
      have binderEq : expected.binder = targetBinder := by
        have shapes := expected.node_eq.symm.trans targetValid.1
        exact (CNode.atom.inj shapes).2
      have expectedNode : (rawDiagram diagram).nodes node =
          .atom current targetBinder := by
        simpa [regionEq, binderEq] using expected.node_eq
      have expectedBubble : (rawDiagram diagram).regions targetBinder =
          .bubble expected.parent arity := by
        simpa only [binderEq] using expected.binder_eq
      have arityEq : arity = targetArity := by
        exact (CRegion.bubble.inj
          (expectedBubble.symm.trans targetValid.2.1)).2
      subst targetArity
      have binderBounded : sourceBinders arity relation <
          (rawDiagram diagram).regionCount := by
        obtain ⟨expectedConcreteRegion, expectedConcreteBinder, lookupNode,
          regionValue, binderValue⟩ := rawDiagram_node_atom_lookup diagram
            node current.val (sourceBinders arity relation) arity
              (wireMap ∘ arguments) draftEq
        rw [← binderValue]
        exact expectedConcreteBinder.isLt
      have targetBinderEq : targetBinder =
          (⟨sourceBinders arity relation, binderBounded⟩ :
            Fin (rawDiagram diagram).regionCount) := by
        obtain ⟨expectedConcreteRegion, expectedConcreteBinder, lookupNode,
          regionValue, binderValue⟩ := rawDiagram_node_atom_lookup diagram
            node current.val (sourceBinders arity relation) arity
              (wireMap ∘ arguments) draftEq
        have expectedEq : targetBinder = expectedConcreteBinder := by
          have shapes := targetValid.1.symm.trans lookupNode
          exact (CNode.atom.inj shapes).2
        exact expectedEq.trans (Fin.ext binderValue)
      have relationEq : binderContext.relationAt binderCovers targetBinder
          (Elaboration.bubbleParent (rawDiagram diagram) targetBinder) arity
          targetValid.2.1 targetValid.2.2.1 = relation := by
        obtain ⟨otherBounded, sourceLookup⟩ :=
          binderAgreement arity relation
        have lookup := Elaboration.BinderContext.relationAt_lookup binderCovers
          targetBinder (Elaboration.bubbleParent (rawDiagram diagram) targetBinder)
          arity targetValid.2.1 targetValid.2.2.1
        have binderFinEq : targetBinder =
            (⟨sourceBinders arity relation, otherBounded⟩ :
              Fin (rawDiagram diagram).regionCount) := by
          exact targetBinderEq.trans (Fin.ext rfl)
        have sourceLookupAt : binderContext targetBinder =
            some ⟨arity, relation⟩ := by
          rw [binderFinEq]
          exact sourceLookup
        have pairEq := Option.some.inj (lookup.symm.trans sourceLookupAt)
        injection pairEq
      rw [Elaboration.CompiledItem.erase_atom]
      rw [relationEq]
      apply ItemIso.atom relation
      funext port
      have sourceOccurs : (rawDiagram diagram).EndpointOccurs
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩
          ⟨node, .arg port.val⟩ := by
        let draftPort : Fin ((flattenOpen diagram).nodes.get node).arity :=
          Fin.cast (congrArg NodeDraft.arity draftEq).symm port
        have result := rawDiagram_argument_occurs diagram node draftPort
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩
          (NodeDraft.argument_of_atom draftEq port).symm
        simpa [draftPort] using result
      have ownerEq : targetPorts port =
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩ :=
        Elaboration.endpoint_wire_unique
          (rawDiagram_wellFormed diagram).wire_endpoints_are_disjoint
          (targetValid.2.2.2 port) sourceOccurs
      have visible := (rawDiagram_wellFormed diagram).wire_scopes_enclose
        (targetPorts port) ⟨node, .arg port.val⟩
          (targetValid.2.2.2 port)
      rw [targetValid.1] at visible
      simpa [relationEq, Function.comp_apply] using
        (wireAgreement.position contextExact (arguments port)
          (targetPorts port) ownerEq visible).symm
  | identity targetNode targetArity targetPorts =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.node.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      subst targetNode
      have impossible := expected.node_eq.symm.trans targetValid.1
      contradiction
  | cut body => contradiction
  | bubble targetArity body => contradiction

private noncomputable def encodeIdentityMotive
    (arguments : Fin arity → Fin sourceWires) :
    ItemEncodingMotive sourceWires rels (.identity arity arguments) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers draftBounded target targetOrigin targetValid
  let node : Fin (rawDiagram diagram).nodeCount := ⟨nodeBase, draftBounded⟩
  have nodeAllocation : List.SegmentAt (flattenOpen diagram).nodes
      [.identity currentRegion arity (wireMap ∘ arguments)] nodeBase := by
    simpa [flattenItem] using allocated.nodes
  have draftEq : (flattenOpen diagram).nodes.get node =
      .identity current.val arity (wireMap ∘ arguments) := by
    have lookup := nodeAllocation.get (0 : Fin 1)
    rw [currentValue]
    simpa [node] using lookup
  obtain ⟨expectedRegion, expectedNode, expectedRegionValue⟩ :=
    rawDiagram_node_identity_lookup diagram node current.val arity
      (wireMap ∘ arguments) draftEq
  cases target with
  | atom targetNode targetBinder targetArity targetPorts =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.node.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      subst targetNode
      have impossible := expectedNode.symm.trans targetValid.1
      contradiction
  | identity targetNode targetArity targetPorts =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.node.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      subst targetNode
      have regionEq : expectedRegion = current := by
        have shapes := expectedNode.symm.trans targetValid.1
        exact (CNode.identity.inj shapes).1
      have arityEq : arity = targetArity := by
        have shapes := expectedNode.symm.trans targetValid.1
        exact (CNode.identity.inj shapes).2
      subst targetArity
      rw [Elaboration.CompiledItem.erase_identity]
      apply ItemIso.identity
      funext port
      have sourceOccurs : (rawDiagram diagram).EndpointOccurs
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩
          ⟨node, .arg port.val⟩ := by
        let draftPort : Fin ((flattenOpen diagram).nodes.get node).arity :=
          Fin.cast (congrArg NodeDraft.arity draftEq).symm port
        have result := rawDiagram_argument_occurs diagram node draftPort
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩
          (NodeDraft.argument_of_identity draftEq port).symm
        simpa [draftPort] using result
      have ownerEq : targetPorts port =
          ⟨wireMap (arguments port), wireAgreement.bounded (arguments port)⟩ :=
        Elaboration.endpoint_wire_unique
          (rawDiagram_wellFormed diagram).wire_endpoints_are_disjoint
          (targetValid.2 port) sourceOccurs
      have visible := (rawDiagram_wellFormed diagram).wire_scopes_enclose
        (targetPorts port) ⟨node, .arg port.val⟩ (targetValid.2 port)
      rw [targetValid.1] at visible
      simpa [Function.comp_apply] using
        (wireAgreement.position contextExact (arguments port)
          (targetPorts port) ownerEq visible).symm
  | cut body => contradiction
  | bubble targetArity body => contradiction

private noncomputable def encodeCutMotive
    (body : Region sourceWires rels)
    (bodyEncoded : RegionEncodingMotive sourceWires rels body) :
    ItemEncodingMotive sourceWires rels (.cut body) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers draftBounded target targetOrigin targetValid
  let child : Fin (rawDiagram diagram).regionCount := ⟨regionBase, draftBounded⟩
  have regionAllocation : List.SegmentAt (flattenOpen diagram).regions
      (flattenRegion (.cut currentRegion) regionBase nodeBase wireBase
        wireMap sourceBinders body).regions regionBase := by
    simpa [flattenItem] using allocated.regions
  have childDraftEq : (flattenOpen diagram).regions.get child =
      .cut current.val := by
    have lookup := regionAllocation.get
      ⟨0, flattenRegion_regions_pos (.cut currentRegion) regionBase
        nodeBase wireBase wireMap sourceBinders body⟩
    rw [currentValue]
    exact lookup.trans (flattenRegion_regions_get_zero (.cut currentRegion)
      regionBase nodeBase wireBase wireMap sourceBinders body)
  obtain ⟨concreteParent, childShape, parentValue⟩ :=
    rawDiagram_region_cut_lookup diagram child current.val childDraftEq
  have concreteParentEq : concreteParent = current := Fin.ext parentValue
  have childShape' : (rawDiagram diagram).regions child = .cut current := by
    simpa [concreteParentEq] using childShape
  have parentEq : ((rawDiagram diagram).regions child).parent? = some current := by
    simp [childShape', CRegion.parent?]
  have childNotRoot : child ≠ (rawDiagram diagram).root := by
    intro equal
    have equalValue := congrArg Fin.val equal
    change regionBase = 0 at equalValue
    omega
  cases target with
  | atom targetNode targetBinder targetArity targetPorts => contradiction
  | identity targetNode targetArity targetPorts => contradiction
  | cut targetBody =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.child.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      have targetShape : (rawDiagram diagram).regions child = .cut current := by
        simpa [targetOrigin] using targetValid.1
      rw [Elaboration.CompiledItem.erase_cut]
      apply ItemIso.cut
      have result := bodyEncoded diagram (.cut currentRegion) regionBase nodeBase
        wireBase wireMap sourceBinders
        (by simpa [flattenItem] using allocated)
        (by
          intro record member
          exact recordsIncluded record (by
            simpa [itemRecordBlock] using member))
        (by
          intro relationArity relation
          have := bindersBefore relationArity relation
          omega)
        child rfl childNotRoot context wireEquiv wireAgreement binderContext
        binderAgreement
        (Elaboration.BinderContext.covers_cut_child binderCovers childShape')
        (contextExact.extend_child (rawDiagram_wellFormed diagram) parentEq)
        targetBody targetOrigin targetValid.2
      simpa [targetOrigin] using result
  | bubble targetArity targetBody =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.child.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      have impossible := childShape'.symm.trans (targetOrigin ▸ targetValid.1)
      contradiction

private noncomputable def encodeBubbleMotive
    (body : Region sourceWires (arity :: rels))
    (bodyEncoded : RegionEncodingMotive sourceWires (arity :: rels) body) :
    ItemEncodingMotive sourceWires rels (.bubble arity body) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers draftBounded target targetOrigin targetValid
  let child : Fin (rawDiagram diagram).regionCount := ⟨regionBase, draftBounded⟩
  have regionAllocation : List.SegmentAt (flattenOpen diagram).regions
      (flattenRegion (.bubble currentRegion arity) regionBase nodeBase wireBase
        wireMap (sourceBinders.push regionBase) body).regions regionBase := by
    simpa [flattenItem] using allocated.regions
  have childDraftEq : (flattenOpen diagram).regions.get child =
      .bubble current.val arity := by
    have lookup := regionAllocation.get
      ⟨0, flattenRegion_regions_pos (.bubble currentRegion arity) regionBase
        nodeBase wireBase wireMap (sourceBinders.push regionBase) body⟩
    rw [currentValue]
    exact lookup.trans (flattenRegion_regions_get_zero
      (.bubble currentRegion arity) regionBase nodeBase wireBase wireMap
      (sourceBinders.push regionBase) body)
  obtain ⟨concreteParent, childShape, parentValue⟩ :=
    rawDiagram_region_bubble_lookup diagram child current.val arity childDraftEq
  have concreteParentEq : concreteParent = current := Fin.ext parentValue
  have childShape' : (rawDiagram diagram).regions child =
      .bubble current arity := by simpa [concreteParentEq] using childShape
  have parentEq : ((rawDiagram diagram).regions child).parent? = some current := by
    simp [childShape', CRegion.parent?]
  have childNotRoot : child ≠ (rawDiagram diagram).root := by
    intro equal
    have equalValue := congrArg Fin.val equal
    change regionBase = 0 at equalValue
    omega
  have childBinderAgreement : BinderMap.ContextAgreement diagram
      (sourceBinders.push regionBase) (binderContext.push child arity) :=
    binderAgreement.push regionBase child rfl bindersBefore
  have childBindersBefore :
      (sourceBinders.push regionBase : BinderMap (arity :: rels)).Bounded
        (regionBase + 1) := by
    apply BinderMap.push_bounded sourceBinders
    · intro relationArity relation
      have := bindersBefore relationArity relation
      omega
    · omega
  cases target with
  | atom targetNode targetBinder targetArity targetPorts => contradiction
  | identity targetNode targetArity targetPorts => contradiction
  | cut targetBody =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.child.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      have impossible := childShape'.symm.trans (targetOrigin ▸ targetValid.1)
      contradiction
  | bubble targetArity targetBody =>
      simp only [Elaboration.CompiledItem.origin,
        Elaboration.LocalOccurrence.child.injEq,
        itemOccurrenceDraft, OccurrenceDraft.toConcrete] at targetOrigin
      have arityEq : targetArity = arity := by
        exact (CRegion.bubble.inj
          ((targetOrigin ▸ targetValid.1).symm.trans childShape')).2
      subst targetArity
      rw [Elaboration.CompiledItem.erase_bubble]
      apply ItemIso.bubble
      have result := bodyEncoded diagram (.bubble currentRegion arity)
        regionBase nodeBase wireBase wireMap (sourceBinders.push regionBase)
        (by simpa [flattenItem] using allocated)
        (by
          intro record member
          exact recordsIncluded record (by
            simpa [itemRecordBlock] using member))
        childBindersBefore child rfl childNotRoot context wireEquiv
        wireAgreement (binderContext.push child arity) childBinderAgreement
        (Elaboration.BinderContext.push_covers_bubble_child binderCovers
          childShape')
        (contextExact.extend_child (rawDiagram_wellFormed diagram) parentEq)
        targetBody targetOrigin targetValid.2
      simpa [targetOrigin] using result

private noncomputable def encodeNilMotive :
    ItemsEncodingMotive sourceWires rels
      (.nil : ItemSeq sourceWires rels) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers index
  exact Fin.elim0 index

private noncomputable def encodeConsMotive
    (head : Item sourceWires rels) (tail : ItemSeq sourceWires rels)
    (headEncoded : ItemEncodingMotive sourceWires rels head)
    (tailEncoded : ItemsEncodingMotive sourceWires rels tail) :
    ItemsEncodingMotive sourceWires rels (.cons head tail) := by
  intro openArity diagram currentRegion regionBase nodeBase wireBase wireMap
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    currentBefore context wireEquiv wireAgreement contextExact binderContext
    binderAgreement binderCovers sourceIndex target targetOrigin targetValid
  let headFlat := flattenItem currentRegion regionBase nodeBase wireBase
    wireMap sourceBinders head
  let tailFlat := flattenItems currentRegion
    (regionBase + (itemCounts head).regions)
    (nodeBase + (itemCounts head).nodes)
    (wireBase + (itemCounts head).wires) wireMap sourceBinders tail
  have flatEq : flattenItems currentRegion regionBase nodeBase wireBase
      wireMap sourceBinders (.cons head tail) = headFlat.append tailFlat := by
    cases head <;> rfl
  have allocated' : Flat.SegmentAt (flattenOpen diagram)
      (headFlat.append tailFlat) regionBase nodeBase wireBase := by
    rw [← flatEq]
    exact allocated
  have headAllocated := allocated'.left
  have tailAllocated := allocated'.right
  have headLengths := flattenItem_lengths currentRegion regionBase nodeBase
    wireBase wireMap sourceBinders head
  rw [headLengths.1, headLengths.2.1, headLengths.2.2] at tailAllocated
  have headRecordsIncluded : ∀ record,
      record ∈ itemRecordBlock regionBase nodeBase wireBase head →
        record ∈ openRegionRecords diagram := by
    intro record member
    apply recordsIncluded record
    rw [itemRecords_cons]
    exact List.mem_append_left _ member
  have tailRecordsIncluded : ∀ record,
      record ∈ itemRecords
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes)
          (wireBase + (itemCounts head).wires) tail →
        record ∈ openRegionRecords diagram := by
    intro record member
    apply recordsIncluded record
    rw [itemRecords_cons]
    exact List.mem_append_right _ member
  have tailBindersBefore : sourceBinders.Bounded
      (regionBase + (itemCounts head).regions) := by
    intro relationArity relation
    have := bindersBefore relationArity relation
    omega
  have tailCurrentBefore :
      currentRegion < regionBase + (itemCounts head).regions := by omega
  let consDrafts := itemOccurrenceDraft regionBase nodeBase head ::
    occurrenceDrafts (regionBase + (itemCounts head).regions)
      (nodeBase + (itemCounts head).nodes) tail
  have draftsEq : occurrenceDrafts regionBase nodeBase (.cons head tail) =
      consDrafts := occurrenceDrafts_cons head tail
  let consIndex : Fin consDrafts.length :=
    Fin.cast (congrArg List.length draftsEq) sourceIndex
  have sourceDraftEq := List.get_cast draftsEq sourceIndex
  generalize splitIndexEq : consIndex = splitIndex
  revert splitIndexEq
  refine Fin.cases ?_ (fun tailIndex => ?_) splitIndex
  · intro splitIndexEq
    have sourceIndexValue : sourceIndex.val = 0 := by
      simpa [consIndex] using congrArg Fin.val splitIndexEq
    have sourceItemIndex :
        Fin.cast (occurrenceDrafts_length (.cons head tail)) sourceIndex =
          (⟨0, by change 0 < tail.length + 1; omega⟩ :
            Fin (ItemSeq.cons head tail).length) :=
      Fin.ext sourceIndexValue
    have sourceDraftHead :
        (occurrenceDrafts regionBase nodeBase (.cons head tail)).get
            sourceIndex = itemOccurrenceDraft regionBase nodeBase head := by
      change (occurrenceDrafts regionBase nodeBase (.cons head tail)).get
          sourceIndex = consDrafts.get consIndex at sourceDraftEq
      rw [splitIndexEq] at sourceDraftEq
      simpa [consDrafts] using sourceDraftEq
    let headBounded := occurrenceDrafts_bounded diagram currentRegion
      regionBase nodeBase wireBase wireMap sourceBinders (.cons head tail)
      allocated (itemOccurrenceDraft regionBase nodeBase head) (by
        simp [occurrenceDrafts_cons])
    have concreteEq := OccurrenceDraft.toConcrete_congr sourceDraftHead
      (occurrenceDrafts_bounded diagram currentRegion regionBase nodeBase
        wireBase wireMap sourceBinders (.cons head tail) allocated _
        (List.get_mem _ sourceIndex))
    have headOrigin : target.origin =
        (itemOccurrenceDraft regionBase nodeBase head).toConcrete headBounded := by
      exact targetOrigin.trans concreteEq
    have result := headEncoded diagram currentRegion regionBase nodeBase wireBase
      wireMap sourceBinders (by simpa [headFlat] using headAllocated)
      headRecordsIncluded bindersBefore current currentValue currentBefore
      context wireEquiv wireAgreement contextExact binderContext
      binderAgreement binderCovers headBounded target headOrigin targetValid
    simpa [sourceItemIndex] using result
  · intro splitIndexEq
    have sourceIndexValue : sourceIndex.val = tailIndex.val + 1 := by
      simpa [consIndex] using congrArg Fin.val splitIndexEq
    have tailItemIndex :
        Fin.cast (occurrenceDrafts_length (.cons head tail)) sourceIndex =
          Fin.succ (Fin.cast (occurrenceDrafts_length tail) tailIndex) :=
      Fin.ext sourceIndexValue
    have sourceDraftTail :
        (occurrenceDrafts regionBase nodeBase (.cons head tail)).get
            sourceIndex =
          (occurrenceDrafts
            (regionBase + (itemCounts head).regions)
            (nodeBase + (itemCounts head).nodes) tail).get tailIndex := by
      change (occurrenceDrafts regionBase nodeBase (.cons head tail)).get
          sourceIndex = consDrafts.get consIndex at sourceDraftEq
      rw [splitIndexEq] at sourceDraftEq
      simpa [consDrafts] using sourceDraftEq
    let tailBounded := occurrenceDrafts_bounded diagram currentRegion
      (regionBase + (itemCounts head).regions)
      (nodeBase + (itemCounts head).nodes)
      (wireBase + (itemCounts head).wires) wireMap sourceBinders tail
      tailAllocated _ (List.get_mem _ tailIndex)
    have concreteEq := OccurrenceDraft.toConcrete_congr sourceDraftTail
      (occurrenceDrafts_bounded diagram currentRegion regionBase nodeBase
        wireBase wireMap sourceBinders (.cons head tail) allocated _
        (List.get_mem _ sourceIndex))
    have tailOrigin : target.origin =
        ((occurrenceDrafts
          (regionBase + (itemCounts head).regions)
          (nodeBase + (itemCounts head).nodes) tail).get tailIndex).toConcrete
          tailBounded := targetOrigin.trans concreteEq
    have result := tailEncoded diagram currentRegion
      (regionBase + (itemCounts head).regions)
      (nodeBase + (itemCounts head).nodes)
      (wireBase + (itemCounts head).wires) wireMap sourceBinders tailAllocated
      tailRecordsIncluded tailBindersBefore current currentValue
      tailCurrentBefore context wireEquiv wireAgreement contextExact
      binderContext binderAgreement binderCovers tailIndex target tailOrigin
      targetValid
    simpa [tailItemIndex] using result

private noncomputable def encodeRegionMotive
    (localWires : Nat) (items : ItemSeq (sourceWires + localWires) rels)
    (itemsEncoded : ItemsEncodingMotive (sourceWires + localWires) rels items) :
    RegionEncodingMotive sourceWires rels (.mk localWires items) := by
  intro openArity diagram regionKind regionBase nodeBase wireBase outerWires
    sourceBinders allocated recordsIncluded bindersBefore current currentValue
    notRoot context wireEquiv wireAgreement binderContext binderAgreement
    binderCovers extendedExact target targetOrigin targetValid
  have regionAllocation : List.SegmentAt (flattenOpen diagram).regions
      (regionKind :: (flattenItems regionBase (regionBase + 1)
        nodeBase (wireBase + localWires)
        (outerWires.extend wireBase localWires) sourceBinders items).regions)
      regionBase := by
    simpa only [flattenRegion] using allocated.regions
  have wireAllocation : List.SegmentAt (flattenOpen diagram).wireScopes
      (List.replicate localWires regionBase ++
        (flattenItems regionBase (regionBase + 1)
          nodeBase (wireBase + localWires)
          (outerWires.extend wireBase localWires) sourceBinders items).wireScopes)
      wireBase := by
    simpa only [flattenRegion] using allocated.wireScopes
  let nestedFlat := flattenItems regionBase (regionBase + 1) nodeBase
    (wireBase + localWires) (outerWires.extend wireBase localWires)
    sourceBinders items
  have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
      (regionBase + 1) nodeBase (wireBase + localWires) := by
    exact {
      regions := by simpa only [nestedFlat] using regionAllocation.tail
      nodes := by
        simpa only [flattenRegion, nestedFlat] using allocated.nodes
      wireScopes := by
        have right := wireAllocation.right
          (left := List.replicate localWires regionBase)
        simpa only [List.length_replicate, nestedFlat] using right
    }
  let record : RegionRecord := {
    index := regionBase
    wireBase := wireBase
    localWires := localWires
    occurrences := occurrenceDrafts (regionBase + 1) nodeBase items
  }
  have recordMember : record ∈ openRegionRecords diagram := by
    apply recordsIncluded record
    simp [regionRecords, record]
  obtain ⟨wireEnd, wireMemIff⟩ := record_exactScopeWires diagram record
    recordMember current (by simpa [record] using currentValue) notRoot
  change wireBase + localWires ≤ (rawDiagram diagram).wireCount at wireEnd
  let localEquiv := exactScopeSliceEquiv (rawDiagram diagram) current
    wireBase localWires wireEnd wireMemIff
  have localLookup : ∀ localIndex,
      (Elaboration.exactScopeWires (rawDiagram diagram) current).get
          (localEquiv localIndex) =
        (⟨wireBase + localIndex.val, by omega⟩ :
          Fin (rawDiagram diagram).wireCount) := by
    exact exactScopeSliceEquiv_lookup (rawDiagram diagram) current wireBase
      localWires wireEnd wireMemIff
  have extendedAgreement := wireAgreement.append wireBase localWires
    (Elaboration.exactScopeWires (rawDiagram diagram) current) wireEnd
    localEquiv localLookup
  obtain ⟨occurrenceBounded, occurrenceMemIff⟩ :=
    record_localOccurrences diagram record recordMember current
      (by simpa [record] using currentValue)
  have occurrenceNodup : record.occurrences.Nodup :=
    openRegionRecords_occurrences_nodup diagram record recordMember
  let occurrenceEquiv := localOccurrenceDraftEquiv current record.occurrences
    occurrenceBounded occurrenceNodup occurrenceMemIff
  let targetItems := target.items
  have targetItemsValid : targetItems.ValidAt target.origin :=
    target.items_valid targetValid
  have targetOrigins : targetItems.origins =
      Elaboration.localOccurrences (rawDiagram diagram) current := by
    calc
      targetItems.origins = Elaboration.localOccurrences
          (rawDiagram diagram) target.origin := target.items_origins targetValid
      _ = _ := congrArg (Elaboration.localOccurrences (rawDiagram diagram))
        targetOrigin
  have targetLength : targetItems.length =
      (Elaboration.localOccurrences (rawDiagram diagram) current).length := by
    rw [Elaboration.CompiledItems.length_eq_origins_length, targetOrigins]
  have targetItemsValidCurrent : targetItems.ValidAt current := by
    simpa [targetOrigin] using targetItemsValid
  have itemsIso : ItemSeqIso
      (castFinEquiv rfl (Elaboration.WireContext.length_extend context current)
        (extendWireEquiv wireEquiv localEquiv)) rels items
      (targetItems.erase targetItemsValidCurrent
        (rawDiagram_wellFormed diagram) (context.extend current) rels
        binderContext extendedExact binderCovers) := by
    let targetEraseLength := Elaboration.CompiledItems.erase_length targetItems
      targetItemsValidCurrent (rawDiagram_wellFormed diagram)
      (context.extend current) rels binderContext extendedExact binderCovers
    let positions : FiniteEquiv (Fin items.length)
        (Fin (targetItems.erase targetItemsValidCurrent
          (rawDiagram_wellFormed diagram) (context.extend current) rels
          binderContext extendedExact binderCovers).length) :=
      (FiniteEquiv.finCast (occurrenceDrafts_length items).symm).trans
        (occurrenceEquiv.trans ((FiniteEquiv.finCast targetLength.symm).trans
          (FiniteEquiv.finCast targetEraseLength.symm)))
    apply ItemSeqIso.permute positions
    intro sourceIndex
    let draftIndex : Fin record.occurrences.length :=
      Fin.cast (occurrenceDrafts_length items).symm sourceIndex
    let localIndex := occurrenceEquiv draftIndex
    let targetIndex : Fin targetItems.length :=
      Fin.cast targetLength.symm localIndex
    have occurrenceLookup := localOccurrenceDraftEquiv_lookup current
      record.occurrences occurrenceBounded occurrenceNodup occurrenceMemIff
      draftIndex
    have realizedLookup := realizeOccurrenceDrafts_get record.occurrences
      occurrenceBounded draftIndex
    have localOccurrenceEq := occurrenceLookup.trans realizedLookup
    have targetOriginAt : (targetItems.get targetIndex).origin =
        (record.occurrences.get draftIndex).toConcrete
          (occurrenceDrafts_bounded diagram regionBase (regionBase + 1)
            nodeBase (wireBase + localWires)
            (outerWires.extend wireBase localWires) sourceBinders items
            nestedAllocated _ (List.get_mem _ draftIndex)) := by
      calc
        (targetItems.get targetIndex).origin =
            targetItems.origins.get
              (Fin.cast
                (Elaboration.CompiledItems.length_eq_origins_length targetItems)
                targetIndex) := Elaboration.CompiledItems.origin_get _ _
        _ = (Elaboration.localOccurrences (rawDiagram diagram) current).get
              localIndex := by
            have lookup := List.get_cast targetOrigins
              (Fin.cast
                (Elaboration.CompiledItems.length_eq_origins_length targetItems)
                targetIndex)
            have indexEq :
                Fin.cast (congrArg List.length targetOrigins)
                    (Fin.cast
                      (Elaboration.CompiledItems.length_eq_origins_length
                        targetItems) targetIndex) = localIndex := by
              apply Fin.ext
              rfl
            simpa [indexEq] using lookup
        _ = _ := localOccurrenceEq
    have itemResult := itemsEncoded diagram regionBase (regionBase + 1)
      nodeBase (wireBase + localWires)
      (outerWires.extend wireBase localWires) sourceBinders nestedAllocated
      (by
        intro candidate member
        apply recordsIncluded candidate
        simp [regionRecords, member])
      (by
        intro relationArity relation
        have := bindersBefore relationArity relation
        omega)
      current currentValue (by omega) (context.extend current)
      (castFinEquiv rfl (Elaboration.WireContext.length_extend context current)
        (extendWireEquiv wireEquiv localEquiv))
      (by simpa [Elaboration.WireContext.extend] using extendedAgreement)
      extendedExact binderContext binderAgreement binderCovers draftIndex
      (targetItems.get targetIndex) targetOriginAt
      (targetItems.valid_get targetItemsValidCurrent targetIndex)
    have sourcePosition :
        Fin.cast (occurrenceDrafts_length items) draftIndex = sourceIndex := by
      apply Fin.ext
      rfl
    have targetPosition : positions sourceIndex =
        Fin.cast targetEraseLength.symm targetIndex := by
      apply Fin.ext
      rfl
    rw [sourcePosition] at itemResult
    rw [targetPosition]
    exact (Elaboration.CompiledItems.erase_get targetItems
      targetItemsValidCurrent (rawDiagram_wellFormed diagram)
      (context.extend current) rels binderContext extendedExact binderCovers
      targetIndex).symm ▸ itemResult
  cases target with
  | mk origin nodes children =>
      simp only [Elaboration.CompiledRegion.origin] at targetOrigin
      subst origin
      have targetEraseItems :
          (nodes.append children).erase
              (nodes.valid_append children targetValid.2.2.1 targetValid.2.2.2)
              (rawDiagram_wellFormed diagram) (context.extend current) rels
              binderContext extendedExact binderCovers =
            (nodes.erase targetValid.2.2.1 (rawDiagram_wellFormed diagram)
              (context.extend current) rels binderContext extendedExact
              binderCovers).append
            (children.erase targetValid.2.2.2
              (rawDiagram_wellFormed diagram) (context.extend current) rels
              binderContext extendedExact binderCovers) :=
        Elaboration.CompiledItems.erase_append nodes children
          targetValid.2.2.1 targetValid.2.2.2
          (rawDiagram_wellFormed diagram) (context.extend current) rels
          binderContext extendedExact binderCovers
      rw [Elaboration.CompiledRegion.erase]
      apply regionIso_of_target_cast
        (Elaboration.WireContext.length_extend context current)
        wireEquiv localEquiv items
      simpa [targetItems, Elaboration.CompiledRegion.items, targetEraseItems]
        using itemsIso

private noncomputable def encodeItemsCore
    (items : ItemSeq sourceWires rels) :
    ItemsEncodingMotive sourceWires rels items := by
  apply ItemSeq.rec
      (motive_1 := RegionEncodingMotive)
      (motive_2 := ItemEncodingMotive)
      (motive_3 := ItemsEncodingMotive)
  case mk =>
      intro sourceWires sourceRels localWires nested nestedEncoded
      exact encodeRegionMotive localWires nested nestedEncoded
  case atom =>
      intro sourceRels arity sourceWires relation arguments
      exact encodeAtomMotive relation arguments
  case identity =>
      intro sourceWires sourceRels arity arguments
      exact encodeIdentityMotive arguments
  case cut =>
      intro sourceWires sourceRels body bodyEncoded
      exact encodeCutMotive body bodyEncoded
  case bubble =>
      intro sourceWires sourceRels arity body bodyEncoded
      exact encodeBubbleMotive body bodyEncoded
  case nil =>
      intro sourceWires sourceRels
      exact encodeNilMotive
  case cons =>
      intro sourceWires sourceRels head tail headEncoded tailEncoded
      exact encodeConsMotive head tail headEncoded tailEncoded

private theorem rawOpen_elaborate_isomorphic
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    VisualProof.Diagram.OpenDiagram.Isomorphic
      (show Concrete.CheckedOpen from
        ⟨rawOpen diagram, rawOpen_wellFormed diagram⟩).elaborate
      (diagram.castArity (rawOpen_boundary_length diagram).symm) := by
  generalize bodyEq : diagram.body = sourceBody
  cases sourceBody with
  | mk localWires items =>
      let checked : Concrete.CheckedOpen :=
        ⟨rawOpen diagram, rawOpen_wellFormed diagram⟩
      let bodyFlat := flattenRegion .sheet 0 0 diagram.externalClasses
        (fun external => external.val) BinderMap.empty diagram.body
      have bodyAllocated : Flat.SegmentAt (flattenOpen diagram) bodyFlat
          0 0 diagram.externalClasses := by
        exact {
          regions := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
          nodes := ⟨[], [], rfl, by simp [flattenOpen, bodyFlat]⟩
          wireScopes := ⟨List.replicate diagram.externalClasses 0, [], by simp,
            by simp [flattenOpen, bodyFlat]⟩
        }
      have regionAllocation : List.SegmentAt (flattenOpen diagram).regions
          (.sheet :: (flattenItems 0 1 0
            (diagram.externalClasses + localWires)
            (WireMap.extend
              (fun external : Fin diagram.externalClasses => external.val)
              diagram.externalClasses localWires)
            BinderMap.empty items).regions) 0 := by
        simpa only [bodyFlat, bodyEq, flattenRegion] using bodyAllocated.regions
      have wireAllocation : List.SegmentAt (flattenOpen diagram).wireScopes
          (List.replicate localWires 0 ++
            (flattenItems 0 1 0 (diagram.externalClasses + localWires)
              (WireMap.extend
                (fun external : Fin diagram.externalClasses => external.val)
                diagram.externalClasses localWires)
              BinderMap.empty items).wireScopes)
          diagram.externalClasses := by
        simpa only [bodyFlat, bodyEq, flattenRegion] using
          bodyAllocated.wireScopes
      let nestedFlat := flattenItems 0 1 0
        (diagram.externalClasses + localWires)
        (WireMap.extend
          (fun external : Fin diagram.externalClasses => external.val)
          diagram.externalClasses localWires)
        BinderMap.empty items
      have nestedAllocated : Flat.SegmentAt (flattenOpen diagram) nestedFlat
          1 0 (diagram.externalClasses + localWires) := by
        exact {
          regions := by simpa only [nestedFlat] using regionAllocation.tail
          nodes := by
            simpa only [bodyFlat, bodyEq, flattenRegion, nestedFlat] using
              bodyAllocated.nodes
          wireScopes := by
            have right := wireAllocation.right
              (left := List.replicate localWires 0)
            simpa only [List.length_replicate, nestedFlat] using right
        }
      let record : RegionRecord := {
        index := 0
        wireBase := diagram.externalClasses
        localWires := localWires
        occurrences := occurrenceDrafts 1 0 items
      }
      have recordMember : record ∈ openRegionRecords diagram := by
        simp [openRegionRecords, regionRecords, record, bodyEq]
      obtain ⟨wireEnd, hiddenMemIff⟩ := record_hiddenWires diagram record
        recordMember rfl (by rfl)
      change diagram.externalClasses + localWires ≤
        (rawDiagram diagram).wireCount at wireEnd
      let hiddenRestriction : FiniteEquiv
          (Fin (wireSlice (rawDiagram diagram) diagram.externalClasses
            localWires wireEnd).length)
          (Fin (rawOpen diagram).hiddenWires.length) :=
        FiniteEquiv.restrictLists
          (FiniteEquiv.refl (Fin (rawDiagram diagram).wireCount))
          (wireSlice (rawDiagram diagram) diagram.externalClasses
            localWires wireEnd)
          (rawOpen diagram).hiddenWires (wireSlice_nodup wireEnd)
          (rawOpen diagram).hiddenWires_nodup (fun wire => by
            simp only [FiniteEquiv.refl_apply]
            exact hiddenMemIff wire)
      have hiddenRestrictionLookup : ∀ index,
          (rawOpen diagram).hiddenWires.get (hiddenRestriction index) =
            (wireSlice (rawDiagram diagram) diagram.externalClasses
              localWires wireEnd).get index := by
        intro index
        exact FiniteEquiv.restrictLists_spec
          (FiniteEquiv.refl (Fin (rawDiagram diagram).wireCount))
          (wireSlice (rawDiagram diagram) diagram.externalClasses
            localWires wireEnd)
          (rawOpen diagram).hiddenWires (wireSlice_nodup wireEnd)
          (rawOpen diagram).hiddenWires_nodup (fun wire => by
            simp only [FiniteEquiv.refl_apply]
            exact hiddenMemIff wire) index
      let hiddenEquiv : FiniteEquiv (Fin localWires)
          (Fin (rawOpen diagram).hiddenWires.length) :=
        (FiniteEquiv.finCast (wireSlice_length wireEnd).symm).trans
          hiddenRestriction
      have hiddenLookup : ∀ localIndex,
          (rawOpen diagram).hiddenWires.get (hiddenEquiv localIndex) =
            (⟨diagram.externalClasses + localIndex.val, by omega⟩ :
              Fin (rawDiagram diagram).wireCount) := by
        intro localIndex
        unfold hiddenEquiv
        rw [FiniteEquiv.trans_apply, hiddenRestrictionLookup]
        simp [FiniteEquiv.finCast, wireSlice]
      have externalAgreement : WireMap.ContextAgreement diagram
          (fun external : Fin diagram.externalClasses => external.val)
          (rawOpen diagram).exposedWires (externalEquiv diagram) := {
        bounded := fun external => (externalWire diagram external).isLt
        lookup := fun external => externalEquiv_lookup diagram external
      }
      have rootAgreement := externalAgreement.append diagram.externalClasses
        localWires (rawOpen diagram).hiddenWires wireEnd hiddenEquiv hiddenLookup
      let rootEquiv : FiniteEquiv
          (Fin (diagram.externalClasses + localWires))
          (Fin ((rawOpen diagram).exposedWires ++
            (rawOpen diagram).hiddenWires).length) :=
        castFinEquiv rfl
          (List.length_append (as := (rawOpen diagram).exposedWires)
            (bs := (rawOpen diagram).hiddenWires))
          (extendWireEquiv (externalEquiv diagram) hiddenEquiv)
      have rootAgreement' : WireMap.ContextAgreement diagram
          (WireMap.extend
            (fun external : Fin diagram.externalClasses => external.val)
            diagram.externalClasses localWires)
          ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires)
          rootEquiv := rootAgreement
      have rootExact : Elaboration.WireContext.Exact
          ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires)
          (rawDiagram diagram).root := by
        simpa only [VisualProof.Concrete.OpenDiagram.rootWires] using
          Elaboration.openRootWires_exact (rawOpen_wellFormed diagram)
      have rootCovers : (Elaboration.BinderContext.empty :
          Elaboration.BinderContext (rawDiagram diagram) []).Covers
          (rawDiagram diagram).root :=
        Elaboration.BinderContext.empty_covers_root
          (rawDiagram_wellFormed diagram)
      obtain ⟨occurrenceBounded, occurrenceMemIff⟩ :=
        record_localOccurrences diagram record recordMember
          (rawDiagram diagram).root rfl
      have occurrenceNodup : record.occurrences.Nodup :=
        openRegionRecords_occurrences_nodup diagram record recordMember
      let occurrenceEquiv := localOccurrenceDraftEquiv
        (rawDiagram diagram).root record.occurrences occurrenceBounded
        occurrenceNodup occurrenceMemIff
      let targetBody := checked.compilation
      have targetValid : targetBody.Valid := checked.compilation_valid
      let targetItems := targetBody.items
      have targetItemsValid : targetItems.ValidAt targetBody.origin :=
        targetBody.items_valid targetValid
      have targetOrigin : targetBody.origin = (rawDiagram diagram).root := by
        exact Concrete.CheckedOpen.compilation_origin checked
      have targetItemsValidRoot : targetItems.ValidAt
          (rawDiagram diagram).root := by simpa [targetOrigin] using targetItemsValid
      have targetOrigins : targetItems.origins =
          Elaboration.localOccurrences (rawDiagram diagram)
            (rawDiagram diagram).root := by
        calc
          targetItems.origins = Elaboration.localOccurrences
              (rawDiagram diagram) targetBody.origin :=
            targetBody.items_origins targetValid
          _ = _ := congrArg (Elaboration.localOccurrences (rawDiagram diagram))
            targetOrigin
      have targetLength : targetItems.length =
          (Elaboration.localOccurrences (rawDiagram diagram)
            (rawDiagram diagram).root).length := by
        exact (Elaboration.CompiledItems.length_eq_origins_length
          targetItems).trans (congrArg List.length targetOrigins)
      let targetEraseLength := Elaboration.CompiledItems.erase_length targetItems
        targetItemsValidRoot (rawDiagram_wellFormed diagram)
        ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires) []
        Elaboration.BinderContext.empty rootExact rootCovers
      have itemsIso : ItemSeqIso rootEquiv [] items
          (targetItems.erase targetItemsValidRoot
            (rawDiagram_wellFormed diagram)
            ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires)
            [] Elaboration.BinderContext.empty rootExact rootCovers) := by
        let positions : FiniteEquiv (Fin items.length)
            (Fin (targetItems.erase targetItemsValidRoot
              (rawDiagram_wellFormed diagram)
              ((rawOpen diagram).exposedWires ++
                (rawOpen diagram).hiddenWires)
              [] Elaboration.BinderContext.empty rootExact rootCovers).length) :=
          (FiniteEquiv.finCast (occurrenceDrafts_length items).symm).trans
            (occurrenceEquiv.trans
              ((FiniteEquiv.finCast targetLength.symm).trans
                (FiniteEquiv.finCast targetEraseLength.symm)))
        apply ItemSeqIso.permute positions
        intro sourceIndex
        let draftIndex : Fin record.occurrences.length :=
          Fin.cast (occurrenceDrafts_length items).symm sourceIndex
        let localIndex := occurrenceEquiv draftIndex
        let targetIndex : Fin targetItems.length :=
          Fin.cast targetLength.symm localIndex
        have occurrenceLookup := localOccurrenceDraftEquiv_lookup
          (rawDiagram diagram).root record.occurrences occurrenceBounded
          occurrenceNodup occurrenceMemIff draftIndex
        have realizedLookup := realizeOccurrenceDrafts_get
          record.occurrences occurrenceBounded draftIndex
        have localOccurrenceEq := occurrenceLookup.trans realizedLookup
        have targetOriginAt : (targetItems.get targetIndex).origin =
            (record.occurrences.get draftIndex).toConcrete
              (occurrenceDrafts_bounded diagram 0 1 0
                (diagram.externalClasses + localWires)
                (WireMap.extend
                  (fun external : Fin diagram.externalClasses => external.val)
                  diagram.externalClasses localWires)
                BinderMap.empty items nestedAllocated _
                (List.get_mem _ draftIndex)) := by
          calc
            (targetItems.get targetIndex).origin =
                targetItems.origins.get
                  (Fin.cast
                    (Elaboration.CompiledItems.length_eq_origins_length
                      targetItems) targetIndex) :=
              Elaboration.CompiledItems.origin_get _ _
            _ = (Elaboration.localOccurrences (rawDiagram diagram)
                    (rawDiagram diagram).root).get localIndex := by
              have lookup := List.get_cast targetOrigins
                (Fin.cast
                  (Elaboration.CompiledItems.length_eq_origins_length
                    targetItems) targetIndex)
              have indexEq :
                  Fin.cast (congrArg List.length targetOrigins)
                      (Fin.cast
                        (Elaboration.CompiledItems.length_eq_origins_length
                          targetItems) targetIndex) = localIndex := by
                apply Fin.ext
                rfl
              simpa [indexEq] using lookup
            _ = _ := localOccurrenceEq
        have itemResult := encodeItemsCore items diagram 0 1 0
          (diagram.externalClasses + localWires)
          (WireMap.extend
            (fun external : Fin diagram.externalClasses => external.val)
            diagram.externalClasses localWires)
          BinderMap.empty nestedAllocated
          (by
            intro candidate member
            have included : candidate ∈ record :: itemRecords 1 0
                (diagram.externalClasses + localWires) items :=
              List.mem_cons_of_mem record member
            simpa [openRegionRecords, regionRecords, bodyEq, record]
              using included)
          (by
            intro relationArity relation
            exact Fin.elim0 relation.index)
          (rawDiagram diagram).root rfl (by omega)
          ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires)
          rootEquiv rootAgreement' rootExact Elaboration.BinderContext.empty
          (BinderMap.empty_contextAgreement diagram) rootCovers draftIndex
          (targetItems.get targetIndex) targetOriginAt
          (targetItems.valid_get targetItemsValidRoot targetIndex)
        have sourcePosition :
            Fin.cast (occurrenceDrafts_length items) draftIndex = sourceIndex := by
          apply Fin.ext
          rfl
        have targetPosition : positions sourceIndex =
            Fin.cast targetEraseLength.symm targetIndex := by
          apply Fin.ext
          rfl
        rw [sourcePosition] at itemResult
        rw [targetPosition]
        exact (Elaboration.CompiledItems.erase_get targetItems
          targetItemsValidRoot (rawDiagram_wellFormed diagram)
          ((rawOpen diagram).exposedWires ++ (rawOpen diagram).hiddenWires)
          [] Elaboration.BinderContext.empty rootExact rootCovers
          targetIndex).symm ▸ itemResult
      have bodyIso : RegionIso (externalEquiv diagram) []
          (.mk localWires items)
          (targetBody.erase targetValid (rawDiagram_wellFormed diagram)
            (rawOpen diagram).exposedWires (rawOpen diagram).hiddenWires []
            Elaboration.BinderContext.empty (by
              simpa [targetOrigin] using rootExact) (by
              simpa [targetOrigin] using rootCovers)) := by
        rw [Elaboration.CompiledRegion.erase_eq_items]
        apply regionIso_of_target_cast
          (List.length_append (as := (rawOpen diagram).exposedWires)
            (bs := (rawOpen diagram).hiddenWires))
          (externalEquiv diagram) hiddenEquiv items
        simpa [rootEquiv, targetItems, targetBody,
          Concrete.CheckedOpen.compilation_origin] using itemsIso
      have compiledBodyIso : RegionIso (externalEquiv diagram) []
          diagram.body checked.elaborate.body := by
        rw [bodyEq]
        exact bodyIso
      refine ⟨?_⟩
      apply OpenDiagramIso.ofArityEq (rawOpen_boundary_length diagram)
        (externalEquiv diagram).symm
      · intro position
        change (externalEquiv diagram).symm
            ((rawOpen diagram).boundaryClass position) =
          diagram.boundary
            (Fin.cast (rawOpen_boundary_length diagram) position)
        calc
          _ = (externalEquiv diagram).symm
              (externalEquiv diagram (diagram.boundary
                (Fin.cast (rawOpen_boundary_length diagram) position))) := by
                rw [externalEquiv_boundary]
          _ = _ := (externalEquiv diagram).left_inv _
      · exact compiledBodyIso.symm

end Encoding

def encode (diagram : VisualProof.Diagram.OpenDiagram arity) :
    Concrete.State arity where
  checked := ⟨Encoding.rawOpen diagram, Encoding.rawOpen_wellFormed diagram⟩
  boundary_length := Encoding.rawOpen_boundary_length diagram

theorem encode_elaborate_isomorphic
    (diagram : VisualProof.Diagram.OpenDiagram arity) :
    VisualProof.Diagram.OpenDiagram.Isomorphic
      (Concrete.encode diagram).checked.elaborate
      (diagram.castArity (Concrete.encode diagram).boundary_length.symm) := by
  exact Encoding.rawOpen_elaborate_isomorphic diagram

end VisualProof.Concrete
