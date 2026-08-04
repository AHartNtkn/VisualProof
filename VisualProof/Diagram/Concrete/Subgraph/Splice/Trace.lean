import VisualProof.Diagram.Concrete.Subgraph.Decomposition
import VisualProof.Diagram.Concrete.Elaboration.Compile
import VisualProof.Diagram.Concrete.Elaboration.Simulation
import VisualProof.Diagram.ContextReachability
import VisualProof.Diagram.Concrete.Semantics
import VisualProof.Diagram.Algebra

namespace VisualProof.Data.Finite.FinitePartition

open VisualProof.Diagram

/-- The stable dense carrier of normalized partition representatives. -/
def quotientDomain (partition : FinitePartition size) : SurvivorDomain size where
  survives index := decide (partition.representative index = index)

@[simp] theorem quotientDomain_survives_iff
    (partition : FinitePartition size)
    (index : Fin size) :
    partition.quotientDomain.survives index = true ↔
      partition.representative index = index := by
  simp [quotientDomain]

/-- The dense quotient class of an original finite identifier. -/
def classIndex (partition : FinitePartition size)
    (normalized : partition.Normalized) (index : Fin size) :
    partition.quotientDomain.Carrier :=
  partition.quotientDomain.index
    (partition.representative index) (by
      rw [quotientDomain_survives_iff]
      exact normalized index)

@[simp] theorem quotientOrigin_classIndex
    (partition : FinitePartition size) (normalized : partition.Normalized)
    (index : Fin size) :
    partition.quotientDomain.origin
        (partition.classIndex normalized index) =
      partition.representative index := by
  exact SurvivorDomain.origin_index _ _ _

theorem classIndex_eq_iff_related
    (partition : FinitePartition size) (normalized : partition.Normalized)
    (left right : Fin size) :
    partition.classIndex normalized left =
        partition.classIndex normalized right ↔
      partition.related left right = true := by
  constructor
  · intro heq
    apply (related_eq_true_iff partition left right).2
    have horigin := congrArg
      partition.quotientDomain.origin heq
    simpa only [quotientOrigin_classIndex] using horigin
  · intro hrelated
    apply partition.quotientDomain.origin_injective
    simp only [quotientOrigin_classIndex]
    exact (related_eq_true_iff partition left right).1 hrelated

theorem classIndex_surjective
    (partition : FinitePartition size) (normalized : partition.Normalized) :
    Function.Surjective (partition.classIndex normalized) := by
  intro quotient
  refine ⟨partition.quotientDomain.origin quotient, ?_⟩
  apply partition.quotientDomain.origin_injective
  rw [quotientOrigin_classIndex]
  have hsurvives :=
    partition.quotientDomain.origin_survives quotient
  exact (quotientDomain_survives_iff partition _).1 hsurvives

end VisualProof.Data.Finite.FinitePartition

namespace VisualProof.Diagram

open VisualProof.Data.Finite

namespace Splice

theorem compilerTrace_get_cast {left right : List α}
    (equality : left = right) (index : Fin right.length) :
    left.get (Fin.cast (congrArg List.length equality).symm index) =
      right.get index := by
  subst right
  rfl

noncomputable def finiteEquivOfBijective
    (map : α → β)
    (hmap : Function.Injective map ∧ Function.Surjective map) :
    FiniteEquiv α β where
  toFun := map
  invFun target := Classical.choose (hmap.2 target)
  left_inv source := hmap.1 (Classical.choose_spec (hmap.2 (map source)))
  right_inv target := Classical.choose_spec (hmap.2 target)

private noncomputable def listEmbeddingIndex [DecidableEq β]
    (map : α → β) (source : List α) (target : List β)
    (mapsTo : ∀ value, value ∈ source → map value ∈ target)
    (index : Fin source.length) : Fin target.length :=
  (indexOf? target (map (source.get index))).get (by
    rw [indexOf?_isSome_iff]
    exact mapsTo _ (List.get_mem source index))

private theorem listEmbeddingIndex_spec [DecidableEq β]
    (map : α → β) (source : List α) (target : List β)
    (mapsTo : ∀ value, value ∈ source → map value ∈ target)
    (index : Fin source.length) :
    target.get (listEmbeddingIndex map source target mapsTo index) =
      map (source.get index) := by
  unfold listEmbeddingIndex
  let hsome : (indexOf? target (map (source.get index))).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact mapsTo _ (List.get_mem source index)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    target.get ((indexOf? target (map (source.get index))).get _) =
        target.get found := congrArg target.get
          (Option.get_of_eq_some hsome hfound)
    _ = map (source.get index) := indexOf?_sound hfound

/-- Restrict an injective embedding to two duplicate-free lists that enumerate
the same image.  Unlike `FiniteEquiv.restrictLists`, the ambient carrier types
need not be equivalent. -/
noncomputable def listEmbeddingEquiv [DecidableEq α] [DecidableEq β]
    (map : α → β) (source : List α) (target : List β)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mapsTo : ∀ value, value ∈ source → map value ∈ target)
    (complete : ∀ value, value ∈ target →
      ∃ original, original ∈ source ∧ map original = value)
    (injectiveOn : ∀ left, left ∈ source → ∀ right, right ∈ source →
      map left = map right → left = right) :
    FiniteEquiv (Fin source.length) (Fin target.length) :=
  finiteEquivOfBijective
    (listEmbeddingIndex map source target mapsTo)
    ⟨by
      intro left right heq
      apply Fin.ext
      apply (List.getElem_inj sourceNodup).mp
      have hvalues := congrArg target.get heq
      rw [listEmbeddingIndex_spec, listEmbeddingIndex_spec] at hvalues
      simpa only [List.get_eq_getElem] using
        injectiveOn _ (List.get_mem source left) _
          (List.get_mem source right) hvalues,
    by
      intro targetIndex
      obtain ⟨original, horiginal, hmap⟩ :=
        complete (target.get targetIndex) (List.get_mem target targetIndex)
      obtain ⟨sourceIndex, hsourceIndex⟩ := indexOf?_complete horiginal
      refine ⟨sourceIndex, ?_⟩
      apply Fin.ext
      apply (List.getElem_inj targetNodup).mp
      have hvalue :
          target.get (listEmbeddingIndex map source target mapsTo sourceIndex) =
            target.get targetIndex := by
        rw [listEmbeddingIndex_spec]
        have hsourceGet : source.get sourceIndex = original := by
          simpa only [List.get_eq_getElem] using indexOf?_sound hsourceIndex
        rw [hsourceGet]
        exact hmap
      simpa only [List.get_eq_getElem] using hvalue⟩

theorem listEmbeddingEquiv_spec [DecidableEq α] [DecidableEq β]
    (map : α → β) (source : List α) (target : List β)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mapsTo : ∀ value, value ∈ source → map value ∈ target)
    (complete : ∀ value, value ∈ target →
      ∃ original, original ∈ source ∧ map original = value)
    (injectiveOn : ∀ left, left ∈ source → ∀ right, right ∈ source →
      map left = map right → left = right)
    (index : Fin source.length) :
    target.get (listEmbeddingEquiv map source target sourceNodup targetNodup
      mapsTo complete injectiveOn index) = map (source.get index) := by
  change target.get (listEmbeddingIndex map source target mapsTo index) = _
  exact listEmbeddingIndex_spec map source target mapsTo index

def regionPathAux (d : ConcreteDiagram) :
    Nat → Fin d.regionCount → Option (List Nat)
  | 0, region => if region = d.root then some [] else none
  | fuel + 1, region =>
      if region = d.root then some []
      else
        match (d.regions region).parent? with
        | none => none
        | some parent => do
            let prior ← regionPathAux d fuel parent
            let position ← indexOf? (ConcreteElaboration.localOccurrences d parent)
              (.child region)
            pure (prior ++ [position.val])

def regionPath? (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount) : Option (List Nat) :=
  regionPathAux checked.val checked.val.regionCount region

inductive RegionPath (d : ConcreteDiagram) :
    Fin d.regionCount → Fin d.regionCount → List Nat → Prop
  | here (region) : RegionPath d region region []
  | child {start parent child prior}
      (path : RegionPath d start parent prior)
      (hparent : (d.regions child).parent? = some parent)
      (position : Fin (ConcreteElaboration.localOccurrences d parent).length)
      (hposition : indexOf? (ConcreteElaboration.localOccurrences d parent)
        (.child child) = some position) :
      RegionPath d start child (prior ++ [position.val])

inductive RegionRoute (d : ConcreteDiagram) :
    Fin d.regionCount → Fin d.regionCount → List Nat → Prop
  | here (region) : RegionRoute d region region []
  | step {start child target rest}
      (hparent : (d.regions child).parent? = some start)
      (position : Fin (ConcreteElaboration.localOccurrences d start).length)
      (hposition : indexOf? (ConcreteElaboration.localOccurrences d start)
        (.child child) = some position)
      (tail : RegionRoute d child target rest) :
      RegionRoute d start target (position.val :: rest)

theorem RegionRoute.extend
    (route : RegionRoute d start parent prior)
    (hparent : (d.regions child).parent? = some parent)
    (position : Fin (ConcreteElaboration.localOccurrences d parent).length)
    (hposition : indexOf? (ConcreteElaboration.localOccurrences d parent)
      (.child child) = some position) :
    RegionRoute d start child (prior ++ [position.val]) := by
  induction route with
  | here =>
      simpa using RegionRoute.step hparent position hposition
        (RegionRoute.here child)
  | step firstParent firstPosition firstPositionEq tail ih =>
      simpa using RegionRoute.step firstParent firstPosition firstPositionEq
        (ih hparent position hposition)

theorem RegionRoute.trans
    (first : RegionRoute d start middle firstPath)
    (second : RegionRoute d middle target secondPath) :
    RegionRoute d start target (firstPath ++ secondPath) := by
  induction first with
  | here =>
      simpa using second
  | step hparent position hposition tail ih =>
      simpa [List.cons_append] using
        RegionRoute.step hparent position hposition (ih second)

def RegionRoute.castPath
    (route : RegionRoute d start target sourcePath)
    (pathEq : sourcePath = targetPath) :
    RegionRoute d start target targetPath :=
  pathEq ▸ route

/-- A concrete climb witness determines the corresponding forward compiler
route, including the exact local-occurrence position at every parent edge. -/
private theorem regionRoute_complete_of_climb
    (d : ConcreteDiagram) (steps : Nat)
    (start target : Fin d.regionCount)
    (hclimb : d.climb steps target = some start) :
    ∃ path, Nonempty (RegionRoute d start target path) := by
  induction steps generalizing target with
  | zero =>
      simp only [ConcreteDiagram.climb_zero, Option.some.injEq] at hclimb
      subst target
      exact ⟨[], ⟨.here start⟩⟩
  | succ steps ih =>
      simp only [ConcreteDiagram.climb] at hclimb
      split at hclimb
      · contradiction
      · rename_i parent hparent
        obtain ⟨path, ⟨route⟩⟩ := ih parent hclimb
        obtain ⟨position, hposition⟩ := indexOf?_complete
          ((ConcreteElaboration.mem_localOccurrences_child d parent target).2
            hparent)
        exact ⟨path ++ [position.val],
          ⟨route.extend hparent position hposition⟩⟩

/-- Every declared concrete enclosure has a route accepted by the compiler
trace machinery. -/
theorem regionRoute_complete_of_encloses
    (d : ConcreteDiagram) (start target : Fin d.regionCount)
    (hencloses : d.Encloses start target) :
    ∃ path, Nonempty (RegionRoute d start target path) := by
  obtain ⟨steps, hclimb⟩ := hencloses
  exact regionRoute_complete_of_climb d steps start target hclimb

/-- The proof-independent cut count certified by a concrete route. -/
inductive RegionRoute.HasCutDepth {d : ConcreteDiagram} :
    {start target : Fin d.regionCount} → {path : List Nat} →
      RegionRoute d start target path → Nat → Prop
  | here (region) : HasCutDepth (.here region) 0
  | cut {start child target rest depth}
      {hparent : (d.regions child).parent? = some start}
      {position : Fin (ConcreteElaboration.localOccurrences d start).length}
      {hposition : indexOf? (ConcreteElaboration.localOccurrences d start)
        (.child child) = some position}
      {tail : RegionRoute d child target rest}
      (child_is_cut : d.regions child = .cut start)
      (tail_depth : HasCutDepth tail depth) :
      HasCutDepth (.step hparent position hposition tail) (depth + 1)
  | bubble {start child target rest depth arity}
      {hparent : (d.regions child).parent? = some start}
      {position : Fin (ConcreteElaboration.localOccurrences d start).length}
      {hposition : indexOf? (ConcreteElaboration.localOccurrences d start)
        (.child child) = some position}
      {tail : RegionRoute d child target rest}
      (child_is_bubble : d.regions child = .bubble start arity)
      (tail_depth : HasCutDepth tail depth) :
      HasCutDepth (.step hparent position hposition tail) depth

theorem RegionRoute.hasCutDepth_exists
    (route : RegionRoute d start target path)
    (wellFormed : d.WellFormed signature) :
    ∃ depth, route.HasCutDepth depth := by
  induction route with
  | here =>
      exact ⟨0, .here _⟩
  | @step start child target rest hparent position hposition tail induction =>
      obtain ⟨depth, tailDepth⟩ := induction
      cases childKind : d.regions child with
      | sheet =>
          simp [childKind, CRegion.parent?] at hparent
      | cut parent =>
          have parentEq : parent = start := by
            simpa [childKind, CRegion.parent?] using hparent
          subst parent
          exact ⟨depth + 1,
            RegionRoute.HasCutDepth.cut
              (hparent := hparent) (hposition := hposition)
              childKind tailDepth⟩
      | bubble parent arity =>
          have parentEq : parent = start := by
            simpa [childKind, CRegion.parent?] using hparent
          subst parent
          exact ⟨depth,
            RegionRoute.HasCutDepth.bubble
              (hparent := hparent) (hposition := hposition)
              childKind tailDepth⟩

theorem RegionRoute.HasCutDepth.trans
    {first : RegionRoute d start middle firstPath}
    {second : RegionRoute d middle target secondPath}
    (firstDepth : first.HasCutDepth firstCutDepth)
    (secondDepth : second.HasCutDepth secondCutDepth) :
    (first.trans second).HasCutDepth (firstCutDepth + secondCutDepth) := by
  induction firstDepth with
  | here =>
      simpa using secondDepth
  | @cut start child target rest depth hparent position hposition tail
      child_is_cut tail_depth ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        RegionRoute.HasCutDepth.cut (hparent := hparent)
          (hposition := hposition) child_is_cut (ih secondDepth)
  | @bubble start child target rest depth arity hparent position hposition tail
      child_is_bubble tail_depth ih =>
      simpa [Nat.add_assoc] using
        RegionRoute.HasCutDepth.bubble (hparent := hparent)
          (hposition := hposition) child_is_bubble (ih secondDepth)

theorem RegionRoute.HasCutDepth.castPath
    {route : RegionRoute d start target sourcePath}
    (routeDepth : route.HasCutDepth depth)
    (pathEq : sourcePath = targetPath) :
    (route.castPath pathEq).HasCutDepth depth := by
  subst targetPath
  exact routeDepth

theorem RegionRoute.climb_length
    (route : RegionRoute d start target path) :
    d.climb path.length target = some start := by
  induction route with
  | here => simp
  | @step start child target rest hparent position hposition tail ih =>
      have childStep : d.climb 1 child = some start := by
        simp [ConcreteDiagram.climb, hparent]
      simpa using ConcreteElaboration.climb_add ih childStep

theorem RegionPath.toRoute
    (path : RegionPath d start target positions) :
    RegionRoute d start target positions := by
  induction path with
  | here => exact .here _
  | child priorPath hparent position hposition ih =>
      exact ih.extend hparent position hposition

theorem regionPathAux_complete
    (d : ConcreteDiagram)
    {steps fuel : Nat} {region : Fin d.regionCount}
    (hle : steps ≤ fuel)
    (hclimb : d.climb steps region = some d.root) :
    ∃ path, regionPathAux d fuel region = some path ∧
      RegionPath d d.root region path := by
  induction steps generalizing fuel region with
  | zero =>
      have hregion : region = d.root := Option.some.inj hclimb
      subst region
      cases fuel <;> exact ⟨[], by simp [regionPathAux], .here d.root⟩
  | succ steps ih =>
      by_cases hregion : region = d.root
      · subst region
        cases fuel with
        | zero => omega
        | succ fuel => exact ⟨[], by simp [regionPathAux], .here d.root⟩
      · cases fuel with
        | zero => omega
        | succ fuel =>
            cases hparent : (d.regions region).parent? with
            | none => simp [ConcreteDiagram.climb, hparent] at hclimb
            | some parent =>
                have htail : d.climb steps parent = some d.root := by
                  simpa [ConcreteDiagram.climb, hparent] using hclimb
                obtain ⟨prior, hprior, priorPath⟩ :=
                  ih (fuel := fuel) (region := parent) (by omega) htail
                have hmember : ConcreteElaboration.LocalOccurrence.child region ∈
                    ConcreteElaboration.localOccurrences d parent :=
                  (ConcreteElaboration.mem_localOccurrences_child d parent region).2
                    hparent
                obtain ⟨position, hposition⟩ := indexOf?_complete hmember
                refine ⟨prior ++ [position.val], ?_,
                  .child priorPath hparent position hposition⟩
                simp [regionPathAux, hregion, hparent, hprior, hposition]

theorem regionPath?_complete (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount) :
    ∃ path, regionPath? checked region = some path := by
  obtain ⟨steps, hsteps⟩ := checked.property.all_regions_reach_root region
  obtain ⟨path, hpath, _⟩ := regionPathAux_complete checked.val
    (Nat.le_of_lt_succ steps.isLt) hsteps
  exact ⟨path, hpath⟩

theorem regionPath?_sound (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount)
    (hpath : regionPath? checked region = some path) :
    RegionPath checked.val checked.val.root region path := by
  unfold regionPath? at hpath
  obtain ⟨steps, hsteps⟩ := checked.property.all_regions_reach_root region
  obtain ⟨found, hfound, hwitness⟩ := regionPathAux_complete checked.val
    (Nat.le_of_lt_succ steps.isLt) hsteps
  rw [hpath] at hfound
  cases hfound
  exact hwitness

theorem regionPath?_route (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount)
    (hpath : regionPath? checked region = some path) :
    RegionRoute checked.val checked.val.root region path :=
  (regionPath?_sound checked region hpath).toRoute

theorem compiledOccurrence_focus
    (d : ConcreteDiagram)
    (recurse : ∀ {rels : Theory.RelCtx},
      (region : Fin d.regionCount) →
      (context : ConcreteElaboration.WireContext d) →
      ConcreteElaboration.BinderContext d rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext d)
    (rels : Theory.RelCtx)
    (binders : ConcreteElaboration.BinderContext d rels)
    (occurrences : List
      (ConcreteElaboration.LocalOccurrence d.regionCount d.nodeCount))
    (items : ItemSeq signature context.length rels)
    (occurrence : ConcreteElaboration.LocalOccurrence d.regionCount d.nodeCount)
    (position : Fin occurrences.length)
    (hitems : ConcreteElaboration.compileOccurrencesWith? signature d recurse
      context binders occurrences = some items)
    (hposition : indexOf? occurrences occurrence = some position) :
    ∃ focus, items.focusAt? position.val = some focus ∧
      ConcreteElaboration.compileOccurrenceWith? signature d recurse
        context binders occurrence = some focus.item := by
  let itemPosition : Fin items.length := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length recurse context binders
      hitems).symm position
  obtain ⟨focus, hfocus, hfocusItem⟩ :=
    ItemSeq.focusAt?_complete items itemPosition
  have hcompiled := ConcreteElaboration.compileOccurrencesWith?_get
    recurse context binders hitems position
  have hoccurrence := indexOf?_sound hposition
  have hoccurrence' : occurrences.get position = occurrence := by
    simpa only [List.get_eq_getElem] using hoccurrence
  rw [hoccurrence'] at hcompiled
  refine ⟨focus, ?_, ?_⟩
  · simpa [itemPosition] using hfocus
  · simpa [itemPosition, hfocusItem] using hcompiled

/-- Lexical compiler data at the terminal region selected by an intrinsic
context path.  The existing context witness supplies location; this record
retains the concrete wire and binder environments needed by splice proofs. -/
structure Region.ContextPath.CompilerLeaf
    (diagram : ConcreteDiagram)
    (target : Fin diagram.regionCount)
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path) where
  inheritedWires : ConcreteElaboration.WireContext diagram
  inheritedLength : inheritedWires.length = witness.toFocus.holeWires
  binders : ConcreteElaboration.BinderContext diagram
    witness.toFocus.holeRels
  items : ItemSeq signature (inheritedWires.extend target).length
    witness.toFocus.holeRels
  fuel : Nat
  itemsComputation :
    ConcreteElaboration.compileOccurrencesWith? signature diagram
        (ConcreteElaboration.compileRegion? signature diagram fuel)
        (inheritedWires.extend target) binders
        (ConcreteElaboration.localOccurrences diagram target) = some items
  wiresExact : (inheritedWires.extend target).Exact target
  bindersCover : binders.Covers target
  binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
    diagram binders target
  bodyComputation : witness.toFocus.body =
    Region.castWiresEq inheritedLength
      (ConcreteElaboration.finishRegion diagram inheritedWires target items)

/-- Rebase terminal compiler evidence onto the focused region itself.  This
forgets only the enclosing intrinsic path; all authoritative lexical and
compilation evidence is retained definitionally. -/
def Region.ContextPath.CompilerLeaf.atFocus
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {body : Region signature outer rels} {path : List Nat}
    {witness : Region.ContextPath body path}
    (leaf : Region.ContextPath.CompilerLeaf diagram target witness) :
    Region.ContextPath.CompilerLeaf diagram target
      (.here witness.toFocus.body) where
  inheritedWires := leaf.inheritedWires
  inheritedLength := leaf.inheritedLength
  binders := leaf.binders
  items := leaf.items
  fuel := leaf.fuel
  itemsComputation := leaf.itemsComputation
  wiresExact := leaf.wiresExact
  bindersCover := leaf.bindersCover
  binderEnumeration := leaf.binderEnumeration
  bodyComputation := leaf.bodyComputation

/-- Transport a focused compiler leaf across an equality of its intrinsic
body presentation. -/
def Region.ContextPath.CompilerLeaf.castHereBodyEq
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {sourceBody targetBody : Region signature outer rels}
    (leaf : Region.ContextPath.CompilerLeaf diagram target
      (.here sourceBody))
    (equality : sourceBody = targetBody) :
    Region.ContextPath.CompilerLeaf diagram target (.here targetBody) := by
  subst targetBody
  exact leaf

@[simp] theorem Region.ContextPath.CompilerLeaf.castHereBodyEq_inheritedWires
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {sourceBody targetBody : Region signature outer rels}
    (leaf : Region.ContextPath.CompilerLeaf diagram target
      (.here sourceBody))
    (equality : sourceBody = targetBody) :
    (leaf.castHereBodyEq equality).inheritedWires = leaf.inheritedWires := by
  subst targetBody
  rfl

@[simp] theorem Region.ContextPath.CompilerLeaf.castHereBodyEq_binders
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {sourceBody targetBody : Region signature outer rels}
    (leaf : Region.ContextPath.CompilerLeaf diagram target
      (.here sourceBody))
    (equality : sourceBody = targetBody) :
    (leaf.castHereBodyEq equality).binders = leaf.binders := by
  subst targetBody
  rfl

/-- Package the actual focused compiler equation as a terminal `.here` leaf.
All lexical evidence comes from the authoritative semantic traversal; this
constructor performs no second compilation or route reconstruction. -/
def Region.ContextPath.CompilerLeaf.hereOfItemsComputation
    (diagram : ConcreteDiagram)
    (target : Fin diagram.regionCount)
    (inheritedWires : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    (fuel : Nat)
    (items : ItemSeq signature (inheritedWires.extend target).length rels)
    (itemsComputation :
      ConcreteElaboration.compileOccurrencesWith? signature diagram
        (ConcreteElaboration.compileRegion? signature diagram fuel)
        (inheritedWires.extend target) binders
        (ConcreteElaboration.localOccurrences diagram target) = some items)
    (wiresExact : (inheritedWires.extend target).Exact target)
    (bindersCover : binders.Covers target)
    (binderEnumeration :
      ConcreteElaboration.BinderContext.Enumeration diagram binders target) :
    Region.ContextPath.CompilerLeaf diagram target
      (.here (ConcreteElaboration.finishRegion diagram inheritedWires target
        items)) where
  inheritedWires := inheritedWires
  inheritedLength := rfl
  binders := binders
  items := items
  fuel := fuel
  itemsComputation := itemsComputation
  wiresExact := wiresExact
  bindersCover := bindersCover
  binderEnumeration := binderEnumeration
  bodyComputation := rfl

/-- Canonical compiler index of any concrete wire visible at the focused
region. -/
noncomputable def Region.ContextPath.CompilerLeaf.siteWireIndex
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (leaf : Region.ContextPath.CompilerLeaf diagram site witness)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope site) :
    Fin (leaf.inheritedWires.extend site).length :=
  Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete
      ((leaf.wiresExact.mem_iff wire).2 visible))

theorem Region.ContextPath.CompilerLeaf.siteWireIndex_spec
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (leaf : Region.ContextPath.CompilerLeaf diagram site witness)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope site) :
    (leaf.inheritedWires.extend site).get
        (leaf.siteWireIndex witness wire visible) = wire := by
  apply ConcreteElaboration.WireContext.lookup?_sound
  exact Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete
      ((leaf.wiresExact.mem_iff wire).2 visible))

/-- The inherited portion of a compiler leaf is exactly the visible wires
whose binders lie strictly outside the focused region.  The local portion is
the complementary exact-scope fiber. -/
theorem Region.ContextPath.CompilerLeaf.inherited_mem_iff
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (leaf : Region.ContextPath.CompilerLeaf diagram site witness)
    (wire : Fin diagram.wireCount) :
    wire ∈ leaf.inheritedWires ↔
      diagram.Encloses (diagram.wires wire).scope site ∧
        (diagram.wires wire).scope ≠ site := by
  have extendedNodup := leaf.wiresExact.nodup
  rw [ConcreteElaboration.WireContext.extend, List.nodup_append]
    at extendedNodup
  constructor
  · intro hinherited
    have hextended : wire ∈ leaf.inheritedWires.extend site :=
      List.mem_append_left _ hinherited
    refine ⟨(leaf.wiresExact.mem_iff wire).1 hextended, ?_⟩
    intro hscope
    have hlocal : wire ∈ ConcreteElaboration.exactScopeWires diagram site :=
      (ConcreteElaboration.mem_exactScopeWires diagram site wire).2 hscope
    exact extendedNodup.2.2 wire hinherited wire hlocal rfl
  · rintro ⟨hvisible, hnotLocal⟩
    have hextended : wire ∈ leaf.inheritedWires.extend site :=
      (leaf.wiresExact.mem_iff wire).2 hvisible
    rw [ConcreteElaboration.WireContext.extend, List.mem_append] at hextended
    exact hextended.resolve_right fun hlocal =>
      hnotLocal ((ConcreteElaboration.mem_exactScopeWires diagram site wire).1
        hlocal)

def Region.ContextPath.CompilerLeaf.castWiresEq
    {region : Region signature source rels} {path : List Nat}
    (witness : Region.ContextPath region path)
    (equality : source = targetWires)
    (leaf : Region.ContextPath.CompilerLeaf diagram site witness) :
    Region.ContextPath.CompilerLeaf diagram site
      (witness.castWiresEq equality) := by
  subst targetWires
  exact leaf

/-- The item sequence in the intrinsic body presentation of a compiler leaf.
This retains both casts performed by `finishRegion`: first from the appended
compiler context to an addition, then from the inherited compiler length to
the intrinsic outer-wire count. -/
def Region.ContextPath.CompilerLeaf.canonicalBodyItems
    {outer localWires : Nat} {rels : Theory.RelCtx}
    {items : ItemSeq signature (outer + localWires) rels}
    (state : Region.ContextPath.CompilerLeaf diagram site
      (.here (.mk localWires items))) :
    ItemSeq signature
      (outer + (ConcreteElaboration.exactScopeWires diagram site).length)
      rels :=
  (state.items.castWiresEq
      (ConcreteElaboration.WireContext.length_extend
        state.inheritedWires site)).castWiresEq
    (congrArg
      (fun inherited => inherited +
        (ConcreteElaboration.exactScopeWires diagram site).length)
      state.inheritedLength)

/-- Open-root compilation uses `finishRoot` at the sheet and `finishRegion`
below it.  The indices retain which of those two kernels produced the leaf. -/
inductive Region.ContextPath.OpenCompilerLeaf
    (checked : CheckedOpenDiagram signature) :
    (target : Fin checked.val.diagram.regionCount) →
      {body : Region signature checked.val.exposedWires.length []} →
      {path : List Nat} → Region.ContextPath body path → Type
  | root
      (items : ItemSeq signature
        (checked.val.exposedWires ++ checked.val.hiddenWires).length [])
      (itemsComputation :
        ConcreteElaboration.compileOccurrencesWith? signature
          checked.val.diagram
          (ConcreteElaboration.compileRegion? signature checked.val.diagram
            checked.val.diagram.regionCount)
          (checked.val.exposedWires ++ checked.val.hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences checked.val.diagram
            checked.val.diagram.root) = some items) :
      OpenCompilerLeaf checked checked.val.diagram.root
        (.here (ConcreteElaboration.finishRoot checked.val.exposedWires
          checked.val.hiddenWires items))
  | nested {target body path} {witness : Region.ContextPath body path}
      (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram target witness) :
      OpenCompilerLeaf checked target witness

theorem Region.ContextPath.OpenCompilerLeaf.root_or_nested
    {target : Fin checked.val.diagram.regionCount}
    {body : Region signature checked.val.exposedWires.length []}
    {path : List Nat} {witness : Region.ContextPath body path}
    (leaf : Region.ContextPath.OpenCompilerLeaf checked target witness) :
    target = checked.val.diagram.root ∨
      Nonempty (Region.ContextPath.CompilerLeaf checked.val.diagram target
        witness) := by
  cases leaf with
  | root items itemsComputation => exact Or.inl rfl
  | nested nestedLeaf => exact Or.inr ⟨nestedLeaf⟩

/-- A proper nested open-compiler target retains its ordinary compiler leaf
directly; no second witness choice is required. -/
noncomputable def Region.ContextPath.OpenCompilerLeaf.nestedOfNe
    {target : Fin checked.val.diagram.regionCount}
    {body : Region signature checked.val.exposedWires.length []}
    {path : List Nat} {witness : Region.ContextPath body path}
    (leaf : Region.ContextPath.OpenCompilerLeaf checked target witness)
    (hne : target ≠ checked.val.diagram.root) :
    Region.ContextPath.CompilerLeaf checked.val.diagram target witness := by
  cases leaf with
  | root items itemsComputation => exact False.elim (hne rfl)
  | nested nestedLeaf => exact nestedLeaf

/-- Every compiler frame retained along one concrete route. `state` is the
authoritative compiler state for the current intrinsic region; each recursive
constructor records the exact state transition used by compilation. -/
inductive CompilerTrace (signature : List Nat) (diagram : ConcreteDiagram) :
    {start target : Fin diagram.regionCount} → {path : List Nat} →
    {outer : Nat} → {rels : Theory.RelCtx} →
    {body : Region signature outer rels} →
    (route : RegionRoute diagram start target path) →
    (witness : Region.ContextPath body path) →
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body)) → Type
  | here
      (state : Region.ContextPath.CompilerLeaf diagram region (.here body)) :
      CompilerTrace signature diagram (.here region) (.here body) state
  | cut
      {start child target : Fin diagram.regionCount} {rest : List Nat}
      {hparent : (diagram.regions child).parent? = some start}
      {position : Fin
        (ConcreteElaboration.localOccurrences diagram start).length}
      {hposition : indexOf?
        (ConcreteElaboration.localOccurrences diagram start) (.child child) =
          some position}
      {tail : RegionRoute diagram child target rest}
      {outer localWires : Nat} {rels : Theory.RelCtx}
      {items : ItemSeq signature (outer + localWires) rels}
      {focus : ItemSeq.Focus items} {childBody : Region signature
        (outer + localWires) rels}
      {atIndex : items.focusAt? position.val = some focus}
      {isCut : focus.item = .cut childBody}
      {nested : Region.ContextPath childBody rest}
      (state : Region.ContextPath.CompilerLeaf diagram start
        (.here (.mk localWires items)))
      (localWiresCanonical : localWires =
        (ConcreteElaboration.exactScopeWires diagram start).length)
      (itemsCanonical : HEq items state.canonicalBodyItems)
      (childState : Region.ContextPath.CompilerLeaf diagram child
        (.here childBody))
      (childKind : diagram.regions child = .cut start)
      (inherited : childState.inheritedWires =
        state.inheritedWires.extend start)
      (binders : childState.binders = state.binders)
      (fuel : childState.fuel + 1 = state.fuel)
      (tailTrace : CompilerTrace signature diagram tail nested childState) :
      CompilerTrace signature diagram
        (.step hparent position hposition tail)
        (.cut focus atIndex isCut nested) state
  | bubble
      {start child target : Fin diagram.regionCount} {rest : List Nat}
      {hparent : (diagram.regions child).parent? = some start}
      {position : Fin
        (ConcreteElaboration.localOccurrences diagram start).length}
      {hposition : indexOf?
        (ConcreteElaboration.localOccurrences diagram start) (.child child) =
          some position}
      {tail : RegionRoute diagram child target rest}
      {outer localWires arity : Nat} {rels : Theory.RelCtx}
      {items : ItemSeq signature (outer + localWires) rels}
      {focus : ItemSeq.Focus items} {childBody : Region signature
        (outer + localWires) (arity :: rels)}
      {atIndex : items.focusAt? position.val = some focus}
      {isBubble : focus.item = .bubble arity childBody}
      {nested : Region.ContextPath childBody rest}
      (state : Region.ContextPath.CompilerLeaf diagram start
        (.here (.mk localWires items)))
      (localWiresCanonical : localWires =
        (ConcreteElaboration.exactScopeWires diagram start).length)
      (itemsCanonical : HEq items state.canonicalBodyItems)
      (childState : Region.ContextPath.CompilerLeaf diagram child
        (.here childBody))
      (childKind : diagram.regions child = .bubble start arity)
      (inherited : childState.inheritedWires =
        state.inheritedWires.extend start)
      (binders : childState.binders = state.binders.push child arity)
      (fuel : childState.fuel + 1 = state.fuel)
      (tailTrace : CompilerTrace signature diagram tail nested childState) :
      CompilerTrace signature diagram
        (.step hparent position hposition tail)
        (.bubble focus atIndex isBubble nested) state

def compilerLeafHereCastWiresEq
    {diagram : ConcreteDiagram} {start : Fin diagram.regionCount}
    {source targetWires : Nat} {rels : Theory.RelCtx}
    {body : Region signature source rels}
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body))
    (equality : source = targetWires) :
    Region.ContextPath.CompilerLeaf diagram start
      (.here (body.castWiresEq equality)) := by
  subst targetWires
  exact state

@[simp] theorem compilerLeafHereCastWiresEq_inheritedWires
    {diagram : ConcreteDiagram} {start : Fin diagram.regionCount}
    {source targetWires : Nat} {rels : Theory.RelCtx}
    {body : Region signature source rels}
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body))
    (equality : source = targetWires) :
    (compilerLeafHereCastWiresEq state equality).inheritedWires =
      state.inheritedWires := by
  subst targetWires
  rfl

@[simp] theorem compilerLeafHereCastWiresEq_binders
    {diagram : ConcreteDiagram} {start : Fin diagram.regionCount}
    {source targetWires : Nat} {rels : Theory.RelCtx}
    {body : Region signature source rels}
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body))
    (equality : source = targetWires) :
    (compilerLeafHereCastWiresEq state equality).binders = state.binders := by
  subst targetWires
  rfl

@[simp] theorem compilerLeafHereCastWiresEq_fuel
    {diagram : ConcreteDiagram} {start : Fin diagram.regionCount}
    {source targetWires : Nat} {rels : Theory.RelCtx}
    {body : Region signature source rels}
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body))
    (equality : source = targetWires) :
    (compilerLeafHereCastWiresEq state equality).fuel = state.fuel := by
  subst targetWires
  rfl

/-- Transport a retained trace across the same outer-wire cast as its
intrinsic context path, without recompiling or reconstructing a route. -/
def CompilerTrace.castWiresEq
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {source targetWires : Nat} {rels : Theory.RelCtx}
    {body : Region signature source rels}
    (route : RegionRoute diagram start target path)
    (witness : Region.ContextPath body path)
    (state : Region.ContextPath.CompilerLeaf diagram start (.here body))
    (trace : CompilerTrace signature diagram route witness state)
    (equality : source = targetWires) :
    CompilerTrace signature diagram route (witness.castWiresEq equality)
      (compilerLeafHereCastWiresEq state equality) := by
  subst targetWires
  exact trace

/-- The terminal compiler leaf is a projection of the retained trace. -/
noncomputable def CompilerTrace.leaf
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state) :
    Region.ContextPath.CompilerLeaf diagram target witness := by
  induction trace with
  | here state => exact state
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace ih =>
      exact {
        inheritedWires := ih.inheritedWires
        inheritedLength := ih.inheritedLength
        binders := ih.binders
        items := ih.items
        fuel := ih.fuel
        itemsComputation := ih.itemsComputation
        wiresExact := ih.wiresExact
        bindersCover := ih.bindersCover
        binderEnumeration := ih.binderEnumeration
        bodyComputation := ih.bodyComputation
      }
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace ih =>
      exact {
        inheritedWires := ih.inheritedWires
        inheritedLength := ih.inheritedLength
        binders := ih.binders
        items := ih.items
        fuel := ih.fuel
        itemsComputation := ih.itemsComputation
        wiresExact := ih.wiresExact
        bindersCover := ih.bindersCover
        binderEnumeration := ih.binderEnumeration
        bodyComputation := ih.bodyComputation
      }

/-- Concatenate retained compiler traces along the same intrinsic path
composition used by `RegionRoute.trans` and `Region.ContextPath.nest`. -/
noncomputable def CompilerTrace.trans
    {diagram : ConcreteDiagram}
    {start middle target : Fin diagram.regionCount}
    {firstPath secondPath : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {firstRoute : RegionRoute diagram start middle firstPath}
    {secondRoute : RegionRoute diagram middle target secondPath}
    {firstWitness : Region.ContextPath body firstPath}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (first : CompilerTrace signature diagram firstRoute firstWitness state)
    {secondWitness : Region.ContextPath firstWitness.toFocus.body secondPath}
    (second : CompilerTrace signature diagram secondRoute secondWitness
      first.leaf.atFocus) :
    CompilerTrace signature diagram (firstRoute.trans secondRoute)
      (firstWitness.nest secondWitness) state := by
  induction first with
  | here state => simpa using second
  | @cut start child middle rest hparent position hposition tail outer
      localWires rels items focus childBody atIndex isCut nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace induction =>
      simpa [RegionRoute.trans, Region.ContextPath.nest] using
        CompilerTrace.cut (hparent := hparent) (position := position)
          (hposition := hposition) state localWiresCanonical itemsCanonical
          childState childKind inherited binders fuel (induction second)
  | @bubble start child middle rest hparent position hposition tail outer
      localWires arity rels items focus childBody atIndex isBubble nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace induction =>
      simpa [RegionRoute.trans, Region.ContextPath.nest] using
        CompilerTrace.bubble (hparent := hparent) (position := position)
          (hposition := hposition) state localWiresCanonical itemsCanonical
          childState childKind inherited binders fuel (induction second)

/-- Every wire inherited at the start of a retained compiler trace remains
inherited at its terminal leaf. -/
noncomputable def CompilerTrace.inheritedIndex
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state) :
    Fin state.inheritedWires.length →
      Fin trace.leaf.inheritedWires.length := by
  induction trace with
  | here state =>
      exact id
  | @cut start child target rest hparent position hposition tail outer
      localWires rels items focus childBody atIndex isCut nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      exact fun index =>
        ih (Fin.cast (congrArg List.length inherited).symm
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              state.inheritedWires start).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires diagram start).length index)))
  | @bubble start child target rest hparent position hposition tail outer
      localWires arity rels items focus childBody atIndex isBubble nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      exact fun index =>
        ih (Fin.cast (congrArg List.length inherited).symm
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              state.inheritedWires start).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires diagram start).length index)))

theorem CompilerTrace.inheritedIndex_get
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state)
    (index : Fin state.inheritedWires.length) :
    trace.leaf.inheritedWires.get (trace.inheritedIndex index) =
      state.inheritedWires.get index := by
  induction trace with
  | here state =>
      rfl
  | @cut start child target rest hparent position hposition tail outer
      localWires rels items focus childBody atIndex isCut nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      change tailTrace.leaf.inheritedWires.get
          (tailTrace.inheritedIndex
            (Fin.cast (congrArg List.length inherited).symm
              (Fin.cast
                (ConcreteElaboration.WireContext.length_extend
                  state.inheritedWires start).symm
                (Fin.castAdd
                  (ConcreteElaboration.exactScopeWires diagram start).length
                  index)))) =
        state.inheritedWires.get index
      rw [ih]
      let extendedIndex :
          Fin (state.inheritedWires.extend start).length :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            state.inheritedWires start).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires diagram start).length index)
      calc
        childState.inheritedWires.get
            (Fin.cast (congrArg List.length inherited).symm extendedIndex) =
          (state.inheritedWires.extend start).get extendedIndex :=
            compilerTrace_get_cast inherited extendedIndex
        _ = state.inheritedWires.get index := by
          simp [extendedIndex, ConcreteElaboration.WireContext.extend]
  | @bubble start child target rest hparent position hposition tail outer
      localWires arity rels items focus childBody atIndex isBubble nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      change tailTrace.leaf.inheritedWires.get
          (tailTrace.inheritedIndex
            (Fin.cast (congrArg List.length inherited).symm
              (Fin.cast
                (ConcreteElaboration.WireContext.length_extend
                  state.inheritedWires start).symm
                (Fin.castAdd
                  (ConcreteElaboration.exactScopeWires diagram start).length
                  index)))) =
        state.inheritedWires.get index
      rw [ih]
      let extendedIndex :
          Fin (state.inheritedWires.extend start).length :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            state.inheritedWires start).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires diagram start).length index)
      calc
        childState.inheritedWires.get
            (Fin.cast (congrArg List.length inherited).symm extendedIndex) =
          (state.inheritedWires.extend start).get extendedIndex :=
            compilerTrace_get_cast inherited extendedIndex
        _ = state.inheritedWires.get index := by
          simp [extendedIndex, ConcreteElaboration.WireContext.extend]

/-- The retained concrete inherited index is the same index selected by the
intrinsic context's canonical outer-wire embedding. -/
theorem CompilerTrace.inheritedIndex_intrinsic
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state)
    (index : Fin state.inheritedWires.length) :
    Fin.cast trace.leaf.inheritedLength (trace.inheritedIndex index) =
      witness.toFocus.context.outerWire
        (Fin.cast state.inheritedLength index) := by
  induction trace with
  | here state =>
      apply Fin.ext
      rfl

  | @cut start child target rest hparent position hposition tail outer
      localWires rels items focus childBody atIndex isCut nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      let childIndex : Fin childState.inheritedWires.length :=
        Fin.cast (congrArg List.length inherited).symm
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              state.inheritedWires start).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires diagram start).length index))
      change Fin.cast tailTrace.leaf.inheritedLength
          (tailTrace.inheritedIndex childIndex) =
        nested.toFocus.context.outerWire
          (Fin.castAdd localWires (Fin.cast state.inheritedLength index))
      rw [ih childIndex]
      apply congrArg nested.toFocus.context.outerWire
      apply Fin.ext
      rfl

  | @bubble start child target rest hparent position hposition tail outer
      localWires arity rels items focus childBody atIndex isBubble nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      let childIndex : Fin childState.inheritedWires.length :=
        Fin.cast (congrArg List.length inherited).symm
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              state.inheritedWires start).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires diagram start).length index))
      change Fin.cast tailTrace.leaf.inheritedLength
          (tailTrace.inheritedIndex childIndex) =
        nested.toFocus.context.outerWire
          (Fin.castAdd localWires (Fin.cast state.inheritedLength index))
      rw [ih childIndex]
      apply congrArg nested.toFocus.context.outerWire
      apply Fin.ext
      rfl

theorem binderEnumeration_lookup_exact
    {diagram : ConcreteDiagram}
    {rels : Theory.RelCtx}
    {binders : ConcreteElaboration.BinderContext diagram rels}
    {region : Fin diagram.regionCount}
    (enumeration : ConcreteElaboration.BinderContext.Enumeration diagram
      binders region)
    {arity : Nat} (relation : Theory.RelVar rels arity) :
    binders (enumeration.binder relation.index) = some ⟨arity, relation⟩ := by
  rcases relation with ⟨index, hasArity⟩
  dsimp only at hasArity ⊢
  subst arity
  simpa using enumeration.lookup index

/-- Every relation visible at the start of a retained compiler trace is
looked up at the terminal leaf under the intrinsic context's canonical
outer-relation embedding. -/
theorem CompilerTrace.binder_lookup_outerRelation
    {diagram : ConcreteDiagram}
    (wellFormed : diagram.WellFormed signature)
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state)
    {arity : Nat} (relation : Theory.RelVar rels arity) :
    trace.leaf.binders (state.binderEnumeration.binder relation.index) =
      some ⟨arity, witness.toFocus.context.outerRelation relation⟩ := by
  induction trace with
  | here state =>
      simpa only [DiagramContext.outerRelation] using
        binderEnumeration_lookup_exact state.binderEnumeration relation
  | @cut start child target rest hparent position hposition tail outer
      localWires rels items focus childBody atIndex isCut nested state
      localWiresCanonical itemsCanonical childState childKind inherited binders
      fuel tailTrace ih =>
      let binder := state.binderEnumeration.binder relation.index
      have stateLookup : state.binders binder = some ⟨arity, relation⟩ :=
        binderEnumeration_lookup_exact state.binderEnumeration relation
      have childLookup : childState.binders binder = some ⟨arity, relation⟩ := by
        rw [binders]
        exact stateLookup
      have owner : childState.binderEnumeration.binder relation.index =
          binder :=
        childState.binderEnumeration.lookup_owner relation childLookup
      simpa only [DiagramContext.outerRelation, owner] using ih relation
  | @bubble start child target rest hparent position hposition tail outer
      localWires bubbleArity rels items focus childBody atIndex isBubble nested
      state localWiresCanonical itemsCanonical childState childKind inherited
      binders fuel tailTrace ih =>
      let binder := state.binderEnumeration.binder relation.index
      have stateLookup : state.binders binder = some ⟨arity, relation⟩ :=
        binderEnumeration_lookup_exact state.binderEnumeration relation
      have binderNe : binder ≠ child := by
        intro equal
        have binderEncloses := state.binderEnumeration.encloses relation.index
        have childParent : (diagram.regions child).parent? = some start := by
          simpa [childKind, CRegion.parent?]
        exact ConcreteElaboration.checked_direct_child_not_encloses_parent
          wellFormed childParent
          (by simpa [binder, equal] using binderEncloses)
      let lifted : Theory.RelVar (bubbleArity :: rels) arity :=
        ConcreteElaboration.BinderContext.liftVar bubbleArity relation
      have childLookup : childState.binders binder = some ⟨arity, lifted⟩ := by
        rw [binders,
          ConcreteElaboration.BinderContext.push_other state.binders
            bubbleArity binderNe,
          stateLookup]
        rfl
      have owner : childState.binderEnumeration.binder lifted.index = binder :=
        childState.binderEnumeration.lookup_owner lifted childLookup
      simpa only [DiagramContext.outerRelation, owner] using ih lifted

/-- Retarget a terminal compiler leaf through one enclosing cut frame.  The
terminal compiler state is unchanged; only its intrinsic path presentation is
extended. -/
def Region.ContextPath.CompilerLeaf.underCut
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {outer localWires : Nat} {rels : Theory.RelCtx}
    {items : ItemSeq signature (outer + localWires) rels}
    {focus : ItemSeq.Focus items}
    {childBody : Region signature (outer + localWires) rels}
    {atIndex : items.focusAt? position = some focus}
    {isCut : focus.item = .cut childBody}
    {path : List Nat} {nested : Region.ContextPath childBody path}
    (leaf : Region.ContextPath.CompilerLeaf diagram target nested) :
    Region.ContextPath.CompilerLeaf diagram target
      (.cut focus atIndex isCut nested) := {
  inheritedWires := leaf.inheritedWires
  inheritedLength := leaf.inheritedLength
  binders := leaf.binders
  items := leaf.items
  fuel := leaf.fuel
  itemsComputation := leaf.itemsComputation
  wiresExact := leaf.wiresExact
  bindersCover := leaf.bindersCover
  binderEnumeration := leaf.binderEnumeration
  bodyComputation := leaf.bodyComputation
}

/-- Bubble counterpart of `CompilerLeaf.underCut`. -/
def Region.ContextPath.CompilerLeaf.underBubble
    {diagram : ConcreteDiagram} {target : Fin diagram.regionCount}
    {outer localWires arity : Nat} {rels : Theory.RelCtx}
    {items : ItemSeq signature (outer + localWires) rels}
    {focus : ItemSeq.Focus items}
    {childBody : Region signature (outer + localWires) (arity :: rels)}
    {atIndex : items.focusAt? position = some focus}
    {isBubble : focus.item = .bubble arity childBody}
    {path : List Nat} {nested : Region.ContextPath childBody path}
    (leaf : Region.ContextPath.CompilerLeaf diagram target nested) :
    Region.ContextPath.CompilerLeaf diagram target
      (.bubble focus atIndex isBubble nested) := {
  inheritedWires := leaf.inheritedWires
  inheritedLength := leaf.inheritedLength
  binders := leaf.binders
  items := leaf.items
  fuel := leaf.fuel
  itemsComputation := leaf.itemsComputation
  wiresExact := leaf.wiresExact
  bindersCover := leaf.bindersCover
  binderEnumeration := leaf.binderEnumeration
  bodyComputation := leaf.bodyComputation
}

/-- Cut depth is derived from the same retained compiler trace. -/
def CompilerTrace.cutDepth
    {diagram : ConcreteDiagram}
    {start target : Fin diagram.regionCount} {path : List Nat}
    {outer : Nat} {rels : Theory.RelCtx}
    {body : Region signature outer rels}
    {route : RegionRoute diagram start target path}
    {witness : Region.ContextPath body path}
    {state : Region.ContextPath.CompilerLeaf diagram start (.here body)}
    (trace : CompilerTrace signature diagram route witness state) :
    route.HasCutDepth witness.toFocus.context.cutDepth := by
  induction trace with
  | here state => exact .here _
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace ih =>
      exact .cut (hparent := by assumption) (hposition := by assumption)
        childKind ih
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace ih =>
      exact .bubble (hparent := by assumption) (hposition := by assumption)
        childKind ih

/-- The compiler state at an open sheet root. -/
structure OpenRootCompilerState (checked : CheckedOpenDiagram signature)
    (body : Region signature checked.val.exposedWires.length []) where
  items : ItemSeq signature checked.val.rootWires.length []
  itemsComputation :
    ConcreteElaboration.compileOccurrencesWith? signature checked.val.diagram
      (ConcreteElaboration.compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) = some items
  bodyComputation : body =
    ConcreteElaboration.finishRoot checked.val.exposedWires
      checked.val.hiddenWires items

/-- The item sequence in the intrinsic body presentation of an open-root
compiler state. -/
def OpenRootCompilerState.canonicalBodyItems
    {localWires : Nat}
    {items : ItemSeq signature
      (checked.val.exposedWires.length + localWires) []}
    (state : OpenRootCompilerState checked (.mk localWires items)) :
    ItemSeq signature
      (checked.val.exposedWires.length + checked.val.hiddenWires.length) [] :=
  state.items.castWiresEq (by simp [OpenConcreteDiagram.rootWires])

/-- The retained open-root state followed by the ordinary route trace. -/
inductive OpenCompilerTrace (checked : CheckedOpenDiagram signature) :
    {target : Fin checked.val.diagram.regionCount} → {path : List Nat} →
    {body : Region signature checked.val.exposedWires.length []} →
    (route : RegionRoute checked.val.diagram checked.val.diagram.root target
      path) →
    (witness : Region.ContextPath body path) →
    (state : OpenRootCompilerState checked body) → Type
  | here
      (state : OpenRootCompilerState checked body) :
      OpenCompilerTrace checked (.here checked.val.diagram.root) (.here body)
        state
  | cut
      {child target : Fin checked.val.diagram.regionCount} {rest : List Nat}
      {hparent : (checked.val.diagram.regions child).parent? =
        some checked.val.diagram.root}
      {position : Fin (ConcreteElaboration.localOccurrences
        checked.val.diagram checked.val.diagram.root).length}
      {hposition : indexOf? (ConcreteElaboration.localOccurrences
        checked.val.diagram checked.val.diagram.root) (.child child) =
          some position}
      {tail : RegionRoute checked.val.diagram child target rest}
      {localWires : Nat}
      {items : ItemSeq signature
        (checked.val.exposedWires.length + localWires) []}
      {focus : ItemSeq.Focus items}
      {childBody : Region signature
        (checked.val.exposedWires.length + localWires) []}
      {atIndex : items.focusAt? position.val = some focus}
      {isCut : focus.item = .cut childBody}
      {nested : Region.ContextPath childBody rest}
      (state : OpenRootCompilerState checked (.mk localWires items))
      (localWiresCanonical : localWires = checked.val.hiddenWires.length)
      (itemsCanonical : HEq items state.canonicalBodyItems)
      (childState : Region.ContextPath.CompilerLeaf checked.val.diagram child
        (.here childBody))
      (childKind : checked.val.diagram.regions child =
        .cut checked.val.diagram.root)
      (inherited : childState.inheritedWires = checked.val.rootWires)
      (binders : childState.binders =
        ConcreteElaboration.BinderContext.empty)
      (fuel : childState.fuel + 1 = checked.val.diagram.regionCount)
      (tailTrace : CompilerTrace signature checked.val.diagram tail nested
        childState) :
      OpenCompilerTrace checked
        (.step hparent position hposition tail)
        (.cut focus atIndex isCut nested) state
  | bubble
      {child target : Fin checked.val.diagram.regionCount} {rest : List Nat}
      {hparent : (checked.val.diagram.regions child).parent? =
        some checked.val.diagram.root}
      {position : Fin (ConcreteElaboration.localOccurrences
        checked.val.diagram checked.val.diagram.root).length}
      {hposition : indexOf? (ConcreteElaboration.localOccurrences
        checked.val.diagram checked.val.diagram.root) (.child child) =
          some position}
      {tail : RegionRoute checked.val.diagram child target rest}
      {localWires arity : Nat}
      {items : ItemSeq signature
        (checked.val.exposedWires.length + localWires) []}
      {focus : ItemSeq.Focus items}
      {childBody : Region signature
        (checked.val.exposedWires.length + localWires) (arity :: [])}
      {atIndex : items.focusAt? position.val = some focus}
      {isBubble : focus.item = .bubble arity childBody}
      {nested : Region.ContextPath childBody rest}
      (state : OpenRootCompilerState checked (.mk localWires items))
      (localWiresCanonical : localWires = checked.val.hiddenWires.length)
      (itemsCanonical : HEq items state.canonicalBodyItems)
      (childState : Region.ContextPath.CompilerLeaf checked.val.diagram child
        (.here childBody))
      (childKind : checked.val.diagram.regions child =
        .bubble checked.val.diagram.root arity)
      (inherited : childState.inheritedWires = checked.val.rootWires)
      (binders : childState.binders =
        ConcreteElaboration.BinderContext.empty.push child arity)
      (fuel : childState.fuel + 1 = checked.val.diagram.regionCount)
      (tailTrace : CompilerTrace signature checked.val.diagram tail nested
        childState) :
      OpenCompilerTrace checked
        (.step hparent position hposition tail)
        (.bubble focus atIndex isBubble nested) state

noncomputable def OpenCompilerTrace.leaf
    {checked : CheckedOpenDiagram signature}
    {target : Fin checked.val.diagram.regionCount} {path : List Nat}
    {body : Region signature checked.val.exposedWires.length []}
    {route : RegionRoute checked.val.diagram checked.val.diagram.root target
      path}
    {witness : Region.ContextPath body path}
    {state : OpenRootCompilerState checked body}
    (trace : OpenCompilerTrace checked route witness state) :
    Region.ContextPath.OpenCompilerLeaf checked target witness := by
  induction trace with
  | here state =>
      rw [state.bodyComputation]
      exact .root state.items state.itemsComputation
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      exact .nested tailTrace.leaf.underCut
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      exact .nested tailTrace.leaf.underBubble

def OpenCompilerTrace.cutDepth
    {checked : CheckedOpenDiagram signature}
    {target : Fin checked.val.diagram.regionCount} {path : List Nat}
    {body : Region signature checked.val.exposedWires.length []}
    {route : RegionRoute checked.val.diagram checked.val.diagram.root target
      path}
    {witness : Region.ContextPath body path}
    {state : OpenRootCompilerState checked body}
    (trace : OpenCompilerTrace checked route witness state) :
    route.HasCutDepth witness.toFocus.context.cutDepth := by
  induction trace with
  | here state => exact .here _
  | cut state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      exact .cut (hparent := by assumption) (hposition := by assumption)
        childKind tailTrace.cutDepth
  | bubble state localWiresCanonical itemsCanonical childState childKind
      inherited binders fuel tailTrace =>
      exact .bubble (hparent := by assumption) (hposition := by assumption)
        childKind tailTrace.cutDepth

/-- Complete retained result of an ordinary route compilation. -/
structure CompilerTraceResult
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount} {path : List Nat}
    (route : RegionRoute checked.val start target path)
    {rels : Theory.RelCtx}
    (context : ConcreteElaboration.WireContext checked.val)
    (binders : ConcreteElaboration.BinderContext checked.val rels)
    (fuel : Nat) (body : Region signature context.length rels) where
  witness : Region.ContextPath body path
  state : Region.ContextPath.CompilerLeaf checked.val start (.here body)
  inherited_eq : state.inheritedWires = context
  binders_eq : state.binders = binders
  fuel_eq : state.fuel + 1 = fuel
  trace : CompilerTrace signature checked.val route witness state

/-- Complete retained result of open-root route compilation. -/
structure OpenCompilerTraceResult
    (checked : CheckedOpenDiagram signature)
    {target : Fin checked.val.diagram.regionCount} {path : List Nat}
    (route : RegionRoute checked.val.diagram checked.val.diagram.root target
      path)
    (body : Region signature checked.val.exposedWires.length []) where
  witness : Region.ContextPath body path
  state : OpenRootCompilerState checked body
  trace : OpenCompilerTrace checked route witness state

theorem compileRegion_route_context_complete
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount} {path : List Nat}
    (route : RegionRoute checked.val start target path)
    {fuel : Nat} {rels : Theory.RelCtx}
    {context : ConcreteElaboration.WireContext checked.val}
    {binders : ConcreteElaboration.BinderContext checked.val rels}
    {body : Region signature context.length rels}
    (hcompile : ConcreteElaboration.compileRegion? signature checked.val fuel
      start context binders = some body)
    (wiresExact : (context.extend start).Exact start)
    (bindersCover : binders.Covers start)
    (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
      checked.val binders start) :
    Nonempty (CompilerTraceResult checked route context binders fuel body) := by
  induction route generalizing fuel rels context binders body with
  | here region =>
      cases fuel with
      | zero => simp [ConcreteElaboration.compileRegion?] at hcompile
      | succ fuel =>
          simp only [ConcreteElaboration.compileRegion?] at hcompile
          cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
              checked.val (ConcreteElaboration.compileRegion? signature
                checked.val fuel)
              (context.extend region) binders
              (ConcreteElaboration.localOccurrences checked.val region) with
          | none => simp [hitems] at hcompile
          | some items =>
              simp [hitems] at hcompile
              subst body
              let state : Region.ContextPath.CompilerLeaf checked.val region
                  (.here (ConcreteElaboration.finishRegion checked.val context
                    region items)) := {
                inheritedWires := context
                inheritedLength := rfl
                binders := binders
                items := items
                fuel := fuel
                itemsComputation := hitems
                wiresExact := wiresExact
                bindersCover := bindersCover
                binderEnumeration := binderEnumeration
                bodyComputation := rfl
              }
              exact ⟨{
                witness := .here _
                state := state
                inherited_eq := rfl
                binders_eq := rfl
                fuel_eq := rfl
                trace := .here state
              }⟩
  | @step start child target rest hparent position hposition tail ih =>
      cases fuel with
      | zero => simp [ConcreteElaboration.compileRegion?] at hcompile
      | succ fuel =>
          simp only [ConcreteElaboration.compileRegion?] at hcompile
          cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
              checked.val (ConcreteElaboration.compileRegion? signature
                checked.val fuel)
              (context.extend start) binders
              (ConcreteElaboration.localOccurrences checked.val start) with
          | none => simp [hitems] at hcompile
          | some items =>
              simp [hitems] at hcompile
              subst body
              obtain ⟨itemFocus, hitemFocus, hitemCompiled⟩ :=
                compiledOccurrence_focus checked.val
                  (ConcreteElaboration.compileRegion? signature checked.val fuel)
                  (context.extend start) rels binders
                  (ConcreteElaboration.localOccurrences checked.val start) items
                  (.child child) position hitems hposition
              let wireEq :=
                ConcreteElaboration.WireContext.length_extend context start
              let castFocus := itemFocus.castWiresEq wireEq
              have hcastFocus :
                  (items.castWiresEq wireEq).focusAt? position.val =
                    some castFocus :=
                ItemSeq.focusAt?_castWiresEq wireEq items position.val
                  itemFocus hitemFocus
              have hcastItem :
                  castFocus.item = itemFocus.item.castWiresEq wireEq := by
                simp [castFocus]
              let state : Region.ContextPath.CompilerLeaf checked.val start
                  (.here (ConcreteElaboration.finishRegion checked.val context
                    start items)) := {
                inheritedWires := context
                inheritedLength := rfl
                binders := binders
                items := items
                fuel := fuel
                itemsComputation := hitems
                wiresExact := wiresExact
                bindersCover := bindersCover
                binderEnumeration := binderEnumeration
                bodyComputation := rfl
              }
              cases hchild : checked.val.regions child with
              | sheet => simp [hchild, CRegion.parent?] at hparent
              | cut parent =>
                  have hparentEq : parent = start := by
                    simpa [hchild, CRegion.parent?] using hparent
                  subst parent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, hchild]
                    at hitemCompiled
                  cases hchildBody : ConcreteElaboration.compileRegion? signature
                      checked.val fuel child (context.extend start) binders with
                  | none => simp [hchildBody] at hitemCompiled
                  | some childBody =>
                      simp [hchildBody] at hitemCompiled
                      have childWiresExact := wiresExact.extend_child
                        checked.property hparent
                      have childBindersCover :=
                        ConcreteElaboration.BinderContext.covers_cut_child
                          bindersCover hchild
                      have childBinderEnumeration :=
                        binderEnumeration.cutChild checked.property hchild
                      obtain ⟨childResult⟩ :=
                        ih hchildBody childWiresExact childBindersCover
                          childBinderEnumeration
                      let nested := childResult.witness
                      let castNested := nested.castWiresEq wireEq
                      have hcastCompiled :
                          Item.cut (childBody.castWiresEq wireEq) =
                            castFocus.item := by
                        calc
                          Item.cut (childBody.castWiresEq wireEq) =
                              (Item.cut childBody).castWiresEq wireEq := by simp
                          _ = itemFocus.item.castWiresEq wireEq :=
                            congrArg (Item.castWiresEq wireEq) hitemCompiled
                          _ = castFocus.item := hcastItem.symm
                      let witness := Region.ContextPath.cut castFocus hcastFocus
                        hcastCompiled.symm castNested
                      let castState := compilerLeafHereCastWiresEq
                        childResult.state wireEq
                      let castTrace := childResult.trace.castWiresEq tail nested
                        childResult.state wireEq
                      have castInherited : castState.inheritedWires =
                          state.inheritedWires.extend start := by
                        simpa [castState, state]
                          using childResult.inherited_eq
                      have castBinders : castState.binders = state.binders := by
                        simpa [castState, state]
                          using childResult.binders_eq
                      have castFuel : castState.fuel + 1 = state.fuel := by
                        simpa [castState, state]
                          using childResult.fuel_eq
                      exact ⟨{
                        witness := witness
                        state := state
                        inherited_eq := rfl
                        binders_eq := rfl
                        fuel_eq := rfl
                        trace := .cut (hparent := hparent)
                          (hposition := hposition) state rfl (by rfl)
                          castState hchild
                          castInherited castBinders castFuel castTrace
                      }⟩
              | bubble parent arity =>
                  have hparentEq : parent = start := by
                    simpa [hchild, CRegion.parent?] using hparent
                  subst parent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, hchild]
                    at hitemCompiled
                  cases hchildBody : ConcreteElaboration.compileRegion? signature
                      checked.val fuel child (context.extend start)
                      (binders.push child arity) with
                  | none => simp [hchildBody] at hitemCompiled
                  | some childBody =>
                      simp [hchildBody] at hitemCompiled
                      have childWiresExact := wiresExact.extend_child
                        checked.property hparent
                      have childBindersCover :=
                        ConcreteElaboration.BinderContext.push_covers_bubble_child
                          bindersCover hchild
                      have childBinderEnumeration :=
                        binderEnumeration.bubbleChild checked.property hchild
                      obtain ⟨childResult⟩ :=
                        ih hchildBody childWiresExact childBindersCover
                          childBinderEnumeration
                      let nested := childResult.witness
                      let castNested := nested.castWiresEq wireEq
                      have hcastCompiled :
                          Item.bubble arity (childBody.castWiresEq wireEq) =
                            castFocus.item := by
                        calc
                          Item.bubble arity (childBody.castWiresEq wireEq) =
                              (Item.bubble arity childBody).castWiresEq wireEq := by
                            simp
                          _ = itemFocus.item.castWiresEq wireEq :=
                            congrArg (Item.castWiresEq wireEq) hitemCompiled
                          _ = castFocus.item := hcastItem.symm
                      let witness := Region.ContextPath.bubble castFocus
                        hcastFocus hcastCompiled.symm castNested
                      let castState := compilerLeafHereCastWiresEq
                        childResult.state wireEq
                      let castTrace := childResult.trace.castWiresEq tail nested
                        childResult.state wireEq
                      have castInherited : castState.inheritedWires =
                          state.inheritedWires.extend start := by
                        simpa [castState, state]
                          using childResult.inherited_eq
                      have castBinders : castState.binders =
                          state.binders.push child arity := by
                        simpa [castState, state]
                          using childResult.binders_eq
                      have castFuel : castState.fuel + 1 = state.fuel := by
                        simpa [castState, state]
                          using childResult.fuel_eq
                      exact ⟨{
                        witness := witness
                        state := state
                        inherited_eq := rfl
                        binders_eq := rfl
                        fuel_eq := rfl
                        trace := .bubble (hparent := hparent)
                          (hposition := hposition) state rfl (by rfl)
                          castState hchild
                          castInherited castBinders castFuel castTrace
                      }⟩

theorem openRootWires_exact
    (checked : CheckedOpenDiagram signature) :
    ConcreteElaboration.WireContext.Exact
      (checked.val.exposedWires ++ checked.val.hiddenWires)
      checked.val.diagram.root := by
  constructor
  · exact checked.val.rootWires_nodup
  · intro wire
    constructor
    · intro hmem
      have hscope := (OpenConcreteDiagram.mem_rootWires_iff
        checked.val checked.property wire).mp (by
          change wire ∈ checked.val.rootWires
          exact hmem)
      rw [hscope]
      exact ConcreteDiagram.Encloses.refl _ _
    · intro hencloses
      have hscope := ConcreteElaboration.encloses_sheet_eq
        checked.property.diagram_well_formed.root_is_sheet hencloses
      change wire ∈ checked.val.rootWires
      exact (OpenConcreteDiagram.mem_rootWires_iff
        checked.val checked.property wire).mpr hscope

theorem compileOpenRoot_route_context_complete
    (checked : CheckedOpenDiagram signature)
    {target : Fin checked.val.diagram.regionCount} {path : List Nat}
    (route : RegionRoute checked.val.diagram checked.val.diagram.root target path)
    {body : Region signature checked.val.exposedWires.length []}
    (hcompile : ConcreteElaboration.compileRoot? signature checked.val.diagram
      checked.val.exposedWires checked.val.hiddenWires = some body) :
    Nonempty (OpenCompilerTraceResult checked route body) := by
  cases route with
  | here =>
      simp only [ConcreteElaboration.compileRoot?] at hcompile
      cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
          checked.val.diagram
          (ConcreteElaboration.compileRegion? signature checked.val.diagram
            checked.val.diagram.regionCount)
          (checked.val.exposedWires ++ checked.val.hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences checked.val.diagram
            checked.val.diagram.root) with
      | none => simp [hitems] at hcompile
      | some items =>
          simp [hitems] at hcompile
          subst body
          let state : OpenRootCompilerState checked
              (ConcreteElaboration.finishRoot checked.val.exposedWires
                checked.val.hiddenWires items) := {
            items := items
            itemsComputation := hitems
            bodyComputation := rfl
          }
          exact ⟨{
            witness := .here _
            state := state
            trace := .here state
          }⟩
  | @step start child target rest hparent position hposition tail =>
      simp only [ConcreteElaboration.compileRoot?] at hcompile
      cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
          checked.val.diagram
          (ConcreteElaboration.compileRegion? signature checked.val.diagram
            checked.val.diagram.regionCount)
          (checked.val.exposedWires ++ checked.val.hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences checked.val.diagram
            checked.val.diagram.root) with
      | none => simp [hitems] at hcompile
      | some items =>
          simp [hitems] at hcompile
          subst body
          obtain ⟨itemFocus, hitemFocus, hitemCompiled⟩ :=
            compiledOccurrence_focus checked.val.diagram
              (ConcreteElaboration.compileRegion? signature checked.val.diagram
                checked.val.diagram.regionCount)
              (checked.val.exposedWires ++ checked.val.hiddenWires) []
              ConcreteElaboration.BinderContext.empty
              (ConcreteElaboration.localOccurrences checked.val.diagram
                checked.val.diagram.root)
              items (.child child) position hitems hposition
          let wireEq :
              (checked.val.exposedWires ++ checked.val.hiddenWires).length =
                checked.val.exposedWires.length + checked.val.hiddenWires.length :=
            by simp
          let castFocus := itemFocus.castWiresEq wireEq
          have hcastFocus :
              (items.castWiresEq wireEq).focusAt? position.val =
                some castFocus :=
            ItemSeq.focusAt?_castWiresEq wireEq items position.val
              itemFocus hitemFocus
          have hcastItem :
              castFocus.item = itemFocus.item.castWiresEq wireEq := by
            simp [castFocus]
          let state : OpenRootCompilerState checked
              (ConcreteElaboration.finishRoot checked.val.exposedWires
                checked.val.hiddenWires items) := {
            items := items
            itemsComputation := hitems
            bodyComputation := rfl
          }
          let closed : CheckedDiagram signature :=
            ⟨checked.val.diagram, checked.property.diagram_well_formed⟩
          cases hchild : checked.val.diagram.regions child with
          | sheet => simp [hchild, CRegion.parent?] at hparent
          | cut parent =>
              have hparentEq : parent = checked.val.diagram.root := by
                simpa [hchild, CRegion.parent?] using hparent
              subst parent
              simp only [ConcreteElaboration.compileOccurrenceWith?, hchild]
                at hitemCompiled
              cases hchildBody : ConcreteElaboration.compileRegion? signature
                  checked.val.diagram checked.val.diagram.regionCount child
                  (checked.val.exposedWires ++ checked.val.hiddenWires)
                  ConcreteElaboration.BinderContext.empty with
              | none => simp [hchildBody] at hitemCompiled
              | some childBody =>
                  simp [hchildBody] at hitemCompiled
                  have rootWiresExact := openRootWires_exact checked
                  have childWiresExact := rootWiresExact.extend_child
                    checked.property.diagram_well_formed hparent
                  have rootBindersCover :=
                    ConcreteElaboration.BinderContext.empty_covers_root
                      checked.property.diagram_well_formed
                  have childBindersCover :=
                    ConcreteElaboration.BinderContext.covers_cut_child
                      rootBindersCover hchild
                  have childBinderEnumeration :=
                    (ConcreteElaboration.BinderContext.Enumeration.empty
                      checked.val.diagram).cutChild
                        checked.property.diagram_well_formed hchild
                  obtain ⟨childResult⟩ :=
                    compileRegion_route_context_complete closed tail hchildBody
                      childWiresExact childBindersCover childBinderEnumeration
                  let nested := childResult.witness
                  let castNested := nested.castWiresEq wireEq
                  have hcastCompiled :
                      Item.cut (childBody.castWiresEq wireEq) =
                        castFocus.item := by
                    calc
                      Item.cut (childBody.castWiresEq wireEq) =
                          (Item.cut childBody).castWiresEq wireEq := by simp
                      _ = itemFocus.item.castWiresEq wireEq :=
                        congrArg (Item.castWiresEq wireEq) hitemCompiled
                      _ = castFocus.item := hcastItem.symm
                  let witness := Region.ContextPath.cut castFocus hcastFocus
                    hcastCompiled.symm castNested
                  let castState := compilerLeafHereCastWiresEq
                    childResult.state wireEq
                  let castTrace := childResult.trace.castWiresEq tail nested
                    childResult.state wireEq
                  have castInherited : castState.inheritedWires =
                      checked.val.rootWires := by
                    simpa [castState]
                      using childResult.inherited_eq
                  have castBinders : castState.binders =
                      ConcreteElaboration.BinderContext.empty := by
                    simpa [castState]
                      using childResult.binders_eq
                  have castFuel : castState.fuel + 1 =
                      checked.val.diagram.regionCount := by
                    simpa [castState]
                      using childResult.fuel_eq
                  exact ⟨{
                    witness := witness
                    state := state
                    trace := .cut (hparent := hparent)
                      (hposition := hposition) state rfl (by rfl)
                      castState hchild
                      castInherited castBinders castFuel castTrace
                  }⟩
          | bubble parent arity =>
              have hparentEq : parent = checked.val.diagram.root := by
                simpa [hchild, CRegion.parent?] using hparent
              subst parent
              simp only [ConcreteElaboration.compileOccurrenceWith?, hchild]
                at hitemCompiled
              cases hchildBody : ConcreteElaboration.compileRegion? signature
                  checked.val.diagram checked.val.diagram.regionCount child
                  (checked.val.exposedWires ++ checked.val.hiddenWires)
                  (ConcreteElaboration.BinderContext.empty.push child arity) with
              | none => simp [hchildBody] at hitemCompiled
              | some childBody =>
                  simp [hchildBody] at hitemCompiled
                  have rootWiresExact := openRootWires_exact checked
                  have childWiresExact := rootWiresExact.extend_child
                    checked.property.diagram_well_formed hparent
                  have rootBindersCover :=
                    ConcreteElaboration.BinderContext.empty_covers_root
                      checked.property.diagram_well_formed
                  have childBindersCover :=
                    ConcreteElaboration.BinderContext.push_covers_bubble_child
                      rootBindersCover hchild
                  have childBinderEnumeration :=
                    (ConcreteElaboration.BinderContext.Enumeration.empty
                      checked.val.diagram).bubbleChild
                        checked.property.diagram_well_formed hchild
                  obtain ⟨childResult⟩ :=
                    compileRegion_route_context_complete closed tail hchildBody
                      childWiresExact childBindersCover childBinderEnumeration
                  let nested := childResult.witness
                  let castNested := nested.castWiresEq wireEq
                  have hcastCompiled :
                      Item.bubble arity (childBody.castWiresEq wireEq) =
                        castFocus.item := by
                    calc
                      Item.bubble arity (childBody.castWiresEq wireEq) =
                          (Item.bubble arity childBody).castWiresEq wireEq := by simp
                      _ = itemFocus.item.castWiresEq wireEq :=
                        congrArg (Item.castWiresEq wireEq) hitemCompiled
                      _ = castFocus.item := hcastItem.symm
                  let witness := Region.ContextPath.bubble castFocus hcastFocus
                    hcastCompiled.symm castNested
                  let castState := compilerLeafHereCastWiresEq
                    childResult.state wireEq
                  let castTrace := childResult.trace.castWiresEq tail nested
                    childResult.state wireEq
                  have castInherited : castState.inheritedWires =
                      checked.val.rootWires := by
                    simpa [castState]
                      using childResult.inherited_eq
                  have castBinders : castState.binders =
                      ConcreteElaboration.BinderContext.empty.push child arity := by
                    simpa [castState]
                      using childResult.binders_eq
                  have castFuel : castState.fuel + 1 =
                      checked.val.diagram.regionCount := by
                    simpa [castState]
                      using childResult.fuel_eq
                  exact ⟨{
                    witness := witness
                    state := state
                    trace := .bubble (hparent := hparent)
                      (hposition := hposition) state rfl (by rfl)
                      castState hchild
                      castInherited castBinders castFuel castTrace
                  }⟩

theorem contextPathAtRegion_complete (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount) :
    ∃ path, regionPath? checked region = some path ∧
      Nonempty (Region.ContextPath checked.elaborate path) := by
  obtain ⟨path, hpath⟩ := regionPath?_complete checked region
  have route := regionPath?_route checked region hpath
  obtain ⟨body, hroot, helaborate⟩ :=
    CheckedDiagram.elaborate_computation checked
  have hcompile :
      ConcreteElaboration.compileRegion? signature checked.val
          (checked.val.regionCount + 1) checked.val.root []
          ConcreteElaboration.BinderContext.empty = some body := by
    rw [← ConcreteElaboration.compileRoot?_closed_eq_compileRegion?]
    exact hroot
  obtain ⟨result⟩ :=
    compileRegion_route_context_complete checked route hcompile
      (ConcreteElaboration.WireContext.root_exact checked.property)
      (ConcreteElaboration.BinderContext.empty_covers_root checked.property)
      (ConcreteElaboration.BinderContext.Enumeration.empty checked.val)
  subst body
  exact ⟨path, hpath, ⟨result.witness⟩⟩

/--
The proof-relevant correspondence between a concrete region and its unique
intrinsic occurrence in the checked elaboration.  Semantic proofs consume this
record instead of comparing dependent proof fields returned by the executable
lookup.
-/
structure SiteView (checked : CheckedDiagram signature)
    (site : Fin checked.val.regionCount) where
  path : List Nat
  concretePath : regionPath? checked site = some path
  route : RegionRoute checked.val checked.val.root site path
  result : CompilerTraceResult checked route
    ([] : ConcreteElaboration.WireContext checked.val)
    ConcreteElaboration.BinderContext.empty (checked.val.regionCount + 1)
    checked.elaborate

def SiteView.intrinsicPath (view : SiteView checked site) :
    Region.ContextPath checked.elaborate view.path :=
  view.result.witness

def SiteView.cutDepth (view : SiteView checked site) :
    view.route.HasCutDepth view.intrinsicPath.toFocus.context.cutDepth :=
  view.result.trace.cutDepth

noncomputable def SiteView.compilerLeaf (view : SiteView checked site) :
    Region.ContextPath.CompilerLeaf checked.val site view.intrinsicPath :=
  view.result.trace.leaf

def SiteView.focus (view : SiteView checked site) :
    Region.ContextFocus checked.elaborate :=
  view.intrinsicPath.toFocus

theorem SiteView.rebuild (view : SiteView checked site) :
    view.focus.context.fill view.focus.body = checked.elaborate :=
  view.focus.rebuild

theorem siteView_complete (checked : CheckedDiagram signature)
    (site : Fin checked.val.regionCount) : Nonempty (SiteView checked site) := by
  obtain ⟨path, concretePath⟩ := regionPath?_complete checked site
  let route := regionPath?_route checked site concretePath
  obtain ⟨body, rootComputation, elaborates⟩ :=
    CheckedDiagram.elaborate_computation checked
  have regionComputation :
      ConcreteElaboration.compileRegion? signature checked.val
          (checked.val.regionCount + 1) checked.val.root []
          ConcreteElaboration.BinderContext.empty = some body := by
    rw [← ConcreteElaboration.compileRoot?_closed_eq_compileRegion?]
    exact rootComputation
  obtain ⟨result⟩ :=
    compileRegion_route_context_complete checked route regionComputation
      (ConcreteElaboration.WireContext.root_exact checked.property)
      (ConcreteElaboration.BinderContext.empty_covers_root checked.property)
      (ConcreteElaboration.BinderContext.Enumeration.empty checked.val)
  subst body
  exact ⟨{
    path
    concretePath
    route
    result
  }⟩

private def checkedBodyDiagram (checked : CheckedOpenDiagram signature) :
    CheckedDiagram signature :=
  ⟨checked.val.diagram, checked.property.diagram_well_formed⟩

/-- An intrinsic context view inside the body of an open concrete diagram. -/
structure OpenSiteView (checked : CheckedOpenDiagram signature)
    (site : Fin checked.val.diagram.regionCount) where
  path : List Nat
  concretePath : regionPath? (checkedBodyDiagram checked) site = some path
  route : RegionRoute checked.val.diagram checked.val.diagram.root site path
  result : OpenCompilerTraceResult checked route checked.elaborate.body

def OpenSiteView.intrinsicPath (view : OpenSiteView checked site) :
    Region.ContextPath checked.elaborate.body view.path :=
  view.result.witness

def OpenSiteView.cutDepth (view : OpenSiteView checked site) :
    view.route.HasCutDepth view.intrinsicPath.toFocus.context.cutDepth :=
  view.result.trace.cutDepth

noncomputable def OpenSiteView.compilerLeaf
    (view : OpenSiteView checked site) :
    Region.ContextPath.OpenCompilerLeaf checked site view.intrinsicPath :=
  view.result.trace.leaf

def OpenSiteView.focus (view : OpenSiteView checked site) :
    Region.ContextFocus checked.elaborate.body :=
  view.intrinsicPath.toFocus

theorem OpenSiteView.rebuild (view : OpenSiteView checked site) :
    view.focus.context.fill view.focus.body = checked.elaborate.body :=
  view.focus.rebuild

theorem openSiteView_complete (checked : CheckedOpenDiagram signature)
    (site : Fin checked.val.diagram.regionCount) :
    Nonempty (OpenSiteView checked site) := by
  obtain ⟨path, concretePath⟩ :=
    regionPath?_complete (checkedBodyDiagram checked) site
  let route := regionPath?_route (checkedBodyDiagram checked) site concretePath
  obtain ⟨body, rootComputation, elaborates⟩ :=
    CheckedOpenDiagram.elaborate_body_computation checked
  obtain ⟨result⟩ :=
    compileOpenRoot_route_context_complete checked route rootComputation
  subst body
  exact ⟨{
    path
    concretePath
    route
    result
  }⟩

/-- The checked closed-root compiler exposes its item sequence directly.
This is the witness-elimination entry point used by checked-success wrappers. -/
theorem checkedRootItems_complete (checked : CheckedDiagram signature) :
    ∃ items : ItemSeq signature
        (ConcreteElaboration.exactScopeWires checked.val
          checked.val.root).length [],
      ConcreteElaboration.compileOccurrencesWith? signature checked.val
        (ConcreteElaboration.compileRegion? signature checked.val
          checked.val.regionCount)
        (ConcreteElaboration.exactScopeWires checked.val checked.val.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences checked.val checked.val.root) =
          some items := by
  obtain ⟨body, hroot, _⟩ := CheckedDiagram.elaborate_computation checked
  simp only [ConcreteElaboration.compileRoot?] at hroot
  cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
      checked.val
      (ConcreteElaboration.compileRegion? signature checked.val
        checked.val.regionCount)
      (ConcreteElaboration.exactScopeWires checked.val checked.val.root)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val checked.val.root) with
  | none => simp [hitems] at hroot
  | some items => exact ⟨items, rfl⟩

/-- Open-root counterpart of `checkedRootItems_complete`. -/
theorem checkedOpenRootItems_complete
    (checked : CheckedOpenDiagram signature) :
    ∃ items : ItemSeq signature checked.val.rootWires.length [],
      ConcreteElaboration.compileOccurrencesWith? signature
        checked.val.diagram
        (ConcreteElaboration.compileRegion? signature checked.val.diagram
          checked.val.diagram.regionCount)
        checked.val.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences checked.val.diagram
          checked.val.diagram.root) = some items := by
  obtain ⟨body, hroot, _⟩ :=
    CheckedOpenDiagram.elaborate_body_computation checked
  simp only [ConcreteElaboration.compileRoot?] at hroot
  cases hitems : ConcreteElaboration.compileOccurrencesWith? signature
      checked.val.diagram
      (ConcreteElaboration.compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      (checked.val.exposedWires ++ checked.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences checked.val.diagram
        checked.val.diagram.root) with
  | none => simp [hitems] at hroot
  | some items =>
      refine ⟨items, ?_⟩
      simpa only [OpenConcreteDiagram.rootWires] using hitems

theorem contextFocusAtRegion_complete (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount) :
    ∃ path, regionPath? checked region = some path ∧
      Nonempty (Region.ContextFocus checked.elaborate) := by
  obtain ⟨path, hpath, ⟨witness⟩⟩ :=
    contextPathAtRegion_complete checked region
  exact ⟨path, hpath, ⟨witness.toFocus⟩⟩

/-- A local region isomorphism remains denotationally valid after its source is
transported to the target wire carrier and the two regions are placed in any
common diagram context.  This is the generic ancestry-lifting step used by the
whole-root splice/compiler commuting theorems below. -/
theorem regionIso_fill_denotation
    {sourceWires targetWires outerWires : Nat}
    {rels outerRels : Theory.RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (hiso : RegionIso signature wire rels source target)
    (context : DiagramContext signature outerWires targetWires outerRels rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (relEnv : RelEnv model.Carrier outerRels) :
    denoteRegion model named env relEnv
        (context.fill (source.renameWires wire)) ↔
      denoteRegion model named env relEnv (context.fill target) := by
  apply DiagramContext.fill_equiv
  intro holeEnv holeRelEnv
  rw [denoteRegion_renameWires]
  exact hiso.denotation model named (holeEnv ∘ wire) holeEnv holeRelEnv
    (fun _ => rfl)

/-- Version of `RegionIso.fill_denotation` where the compiler records the
target region on a propositionally equal wire carrier. -/
theorem regionIso_fill_denotation_cast
    {sourceWires targetWires holeWires outerWires : Nat}
    {rels outerRels : Theory.RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (hiso : RegionIso signature wire rels source target)
    (targetWiresEq : targetWires = holeWires)
    (context : DiagramContext signature outerWires holeWires outerRels rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outerWires → model.Carrier)
    (relEnv : RelEnv model.Carrier outerRels) :
    denoteRegion model named env relEnv
        (context.fill
          (source.renameWires
            (wire.trans (FiniteEquiv.finCast targetWiresEq)))) ↔
      denoteRegion model named env relEnv
        (context.fill (target.castWiresEq targetWiresEq)) := by
  have hcast := RegionIso.renameWiresEquiv target
    (FiniteEquiv.finCast targetWiresEq)
  have hcomposed := hiso.trans hcast
  simpa only [Region.castWiresEq_eq_renameWires] using
    regionIso_fill_denotation hcomposed context model named env relEnv

/-- Replace only the body of an open diagram, retaining its external carrier
and its ordered (possibly repeated) boundary-class map definitionally. -/
def replaceOpenBody (diagram : OpenDiagram signature arity)
    (body : Region signature diagram.externalClasses []) :
    OpenDiagram signature arity where
  externalClasses := diagram.externalClasses
  boundary := diagram.boundary
  boundary_surjective := diagram.boundary_surjective
  body := body

/-- Pointwise body implication lifts through an unchanged open interface.
The external carrier and ordered boundary map are definitionally shared, so
repeated aliases retain exactly the same argument-equality obligations. -/
theorem denote_replaceOpenBody_mono
    (diagram : OpenDiagram signature arity)
    (before after : Region signature diagram.externalClasses [])
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier)
    (entails : ∀ env : Fin diagram.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named env PUnit.unit before →
        denoteRegion (relCtx := []) model named env PUnit.unit after) :
    denoteOpen model named (replaceOpenBody diagram before) args →
      denoteOpen model named (replaceOpenBody diagram after) args := by
  rintro ⟨sourceAssignment, hargs, hbody⟩
  let targetAssignment : BoundaryAssignment
      (replaceOpenBody diagram after) model.Carrier := {
    args := sourceAssignment.args
    classes := sourceAssignment.classes
    agrees := sourceAssignment.agrees
  }
  exact ⟨targetAssignment, hargs, entails sourceAssignment.classes hbody⟩

/-- Pointwise body equivalence lifts to open denotation without changing the
ordered boundary interface.  In particular repeated boundary aliases are
preserved because both assignments use the same class and argument maps. -/
theorem denote_replaceOpenBody_iff
    (diagram : OpenDiagram signature arity)
    (body : Region signature diagram.externalClasses [])
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier)
    (hequiv : ∀ env : Fin diagram.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named env PUnit.unit body ↔
        denoteRegion (relCtx := []) model named env PUnit.unit diagram.body) :
    denoteOpen model named (replaceOpenBody diagram body) args ↔
      denoteOpen model named diagram args := by
  constructor
  · rintro ⟨sourceAssignment, hargs, hbody⟩
    let targetAssignment : BoundaryAssignment diagram model.Carrier := {
      args := sourceAssignment.args
      classes := sourceAssignment.classes
      agrees := sourceAssignment.agrees
    }
    refine ⟨targetAssignment, hargs, ?_⟩
    exact (hequiv sourceAssignment.classes).mp hbody
  · rintro ⟨targetAssignment, hargs, hbody⟩
    let sourceAssignment : BoundaryAssignment
        (replaceOpenBody diagram body) model.Carrier := {
      args := targetAssignment.args
      classes := targetAssignment.classes
      agrees := targetAssignment.agrees
    }
    refine ⟨sourceAssignment, hargs, ?_⟩
    exact (hequiv targetAssignment.classes).mpr hbody

def contextAtRegion? (checked : CheckedDiagram signature)
    (region : Fin checked.val.regionCount) :
    Option (Region.ContextFocus checked.elaborate) := do
  let path ← regionPath? checked region
  checked.elaborate.contextAtPath? path

theorem splice_climb_prefix_exists {d : ConcreteDiagram}
    {start finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfinish : d.climb second start = some finish) :
    ∃ middle, d.climb first start = some middle := by
  induction first generalizing start second with
  | zero => exact ⟨start, rfl⟩
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfinish
          | some parent =>
              have htail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hfinish
              obtain ⟨middle, hmiddle⟩ :=
                ih (Nat.le_of_succ_le_succ hle) htail
              exact ⟨middle, by
                simpa [ConcreteDiagram.climb, hparent] using hmiddle⟩

theorem splice_climb_cancel_prefix {d : ConcreteDiagram}
    {start middle finish : Fin d.regionCount} {first second : Nat}
    (hle : first ≤ second)
    (hfirst : d.climb first start = some middle)
    (hsecond : d.climb second start = some finish) :
    d.climb (second - first) middle = some finish := by
  induction first generalizing start second with
  | zero =>
      have heq : start = middle := Option.some.inj hfirst
      subst middle
      simpa using hsecond
  | succ first ih =>
      cases second with
      | zero => omega
      | succ second =>
          cases hparent : (d.regions start).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at hfirst
          | some parent =>
              have hfirstTail : d.climb first parent = some middle := by
                simpa [ConcreteDiagram.climb, hparent] using hfirst
              have hsecondTail : d.climb second parent = some finish := by
                simpa [ConcreteDiagram.climb, hparent] using hsecond
              simpa using ih (Nat.le_of_succ_le_succ hle)
                hfirstTail hsecondTail

/-- A nonempty proxy spine leaves no hidden root-local wire behind: every
root wire is one of the open boundary identities. -/
theorem BinderSpine.TerminalBodyContract.hiddenWires_eq_nil_of_nonempty
    {openDiagram : OpenConcreteDiagram}
    {spine : BinderSpine openDiagram.diagram}
    (contract : spine.TerminalBodyContract openDiagram)
    (hnonempty : spine.proxyCount ≠ 0) :
    openDiagram.hiddenWires = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hhidden
  have hidden := (OpenConcreteDiagram.mem_hiddenWires openDiagram wire).mp hhidden
  have notBoundary : wire ∉ openDiagram.boundary := by
    intro hboundary
    exact hidden.2 ((OpenConcreteDiagram.mem_exposedWires openDiagram wire).2
      hboundary)
  exact contract.root_has_no_nonboundary_wires hnonempty wire notBoundary
    hidden.1

/-- Every proper proxy-prefix container contributes no wire binder. The
terminal proxy is excluded because it owns the actual material. -/
theorem BinderSpine.TerminalBodyContract.nonterminal_exactScopeWires_eq_nil
    {openDiagram : OpenConcreteDiagram}
    {spine : BinderSpine openDiagram.diagram}
    (contract : spine.TerminalBodyContract openDiagram)
    (proxy : Fin spine.proxyCount)
    (hnonterminal : proxy.val + 1 < spine.proxyCount) :
    ConcreteElaboration.exactScopeWires openDiagram.diagram
      (spine.proxy proxy) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire hwire
  have scope := (ConcreteElaboration.mem_exactScopeWires openDiagram.diagram
    (spine.proxy proxy) wire).mp hwire
  by_cases hboundary : wire ∈ openDiagram.boundary
  · have rootScope := contract.boundary_is_root_scoped wire hboundary
    exact spine.proxy_ne_root proxy (scope.symm.trans rootScope)
  · exact contract.nonterminal_has_no_nonboundary_wires proxy hnonterminal
      wire hboundary scope

theorem BinderSpine.enclosing_proxy_aux
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram) :
    ∀ (value : Nat) (bound : value < spine.proxyCount)
      {ancestor : Fin checked.val.diagram.regionCount},
      checked.val.diagram.Encloses ancestor (spine.proxy ⟨value, bound⟩) →
        ancestor = checked.val.diagram.root ∨
          ∃ prior : Fin spine.proxyCount,
            prior.val ≤ value ∧ ancestor = spine.proxy prior
  | 0, bound, ancestor, hencloses => by
      have parent :
          (checked.val.diagram.regions (spine.proxy ⟨0, bound⟩)).parent? =
            some checked.val.diagram.root := by
        rw [spine.proxy_region]
        simp [CRegion.parent?]
      rcases ConcreteElaboration.encloses_direct_child parent hencloses with
        heq | hroot
      · right
        exact ⟨⟨0, bound⟩, Nat.le_refl 0, heq⟩
      · left
        exact ConcreteElaboration.encloses_sheet_eq
          checked.property.diagram_well_formed.root_is_sheet hroot
  | value + 1, bound, ancestor, hencloses => by
      let prior : Fin spine.proxyCount := ⟨value, by omega⟩
      let current : Fin spine.proxyCount := ⟨value + 1, bound⟩
      have parent :
          (checked.val.diagram.regions (spine.proxy current)).parent? =
            some (spine.proxy prior) := by
        rw [spine.proxy_region]
        simp [current, prior, CRegion.parent?]
      rcases ConcreteElaboration.encloses_direct_child parent hencloses with
        heq | hprior
      · right
        exact ⟨current, Nat.le_refl _, heq⟩
      · rcases BinderSpine.enclosing_proxy_aux checked spine value prior.isLt
          hprior with
          hroot | ⟨found, hle, heq⟩
        · exact Or.inl hroot
        · exact Or.inr ⟨found, Nat.le_trans hle (by omega), heq⟩

/-- The only regions enclosing a proxy are the sheet and its earlier proxy
prefix. This turns the stored spine into a complete lexical-scope fact. -/
theorem BinderSpine.enclosing_proxy_is_root_or_proxy
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (index : Fin spine.proxyCount)
    {ancestor : Fin checked.val.diagram.regionCount}
    (hencloses : checked.val.diagram.Encloses ancestor (spine.proxy index)) :
    ancestor = checked.val.diagram.root ∨
      ∃ prior : Fin spine.proxyCount,
        prior.val ≤ index.val ∧ ancestor = spine.proxy prior :=
  BinderSpine.enclosing_proxy_aux checked spine index.val index.isLt hencloses

/-- At the terminal proxy, the compiler's inherited wire context is exactly
the open pattern's exposed identities. This is the wire half of the lexical
interface needed by capture-avoiding splice elaboration. -/
theorem Region.ContextPath.CompilerLeaf.inherited_mem_iff_exposed
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (contract : spine.TerminalBodyContract checked.val)
    (hnonempty : spine.proxyCount ≠ 0)
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (terminal : Fin spine.proxyCount)
    (terminal_is_last : terminal.val = spine.proxyCount - 1)
    (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram
      (spine.proxy terminal) witness)
    (wire : Fin checked.val.diagram.wireCount) :
    wire ∈ leaf.inheritedWires ↔ wire ∈ checked.val.exposedWires := by
  have extendedNodup := leaf.wiresExact.nodup
  rw [ConcreteElaboration.WireContext.extend,
    List.nodup_append] at extendedNodup
  have notLocal : wire ∈ leaf.inheritedWires →
      (checked.val.diagram.wires wire).scope ≠ spine.proxy terminal := by
    intro hinherited hscope
    have hlocal : wire ∈ ConcreteElaboration.exactScopeWires
        checked.val.diagram (spine.proxy terminal) :=
      (ConcreteElaboration.mem_exactScopeWires checked.val.diagram
        (spine.proxy terminal) wire).2 hscope
    exact extendedNodup.2.2 wire hinherited wire hlocal rfl
  constructor
  · intro hinherited
    have hextended : wire ∈ leaf.inheritedWires.extend
        (spine.proxy terminal) := by
      exact List.mem_append_left _ hinherited
    have hencloses : checked.val.diagram.Encloses
        (checked.val.diagram.wires wire).scope (spine.proxy terminal) :=
      (leaf.wiresExact.mem_iff wire).1 hextended
    rcases BinderSpine.enclosing_proxy_is_root_or_proxy checked spine terminal
        hencloses with
      hroot | ⟨prior, hle, hscope⟩
    · by_cases hexposed : wire ∈ checked.val.exposedWires
      · exact hexposed
      · have hhidden : wire ∈ checked.val.hiddenWires :=
          (OpenConcreteDiagram.mem_hiddenWires checked.val wire).2
            ⟨hroot, hexposed⟩
        rw [BinderSpine.TerminalBodyContract.hiddenWires_eq_nil_of_nonempty
          contract hnonempty] at hhidden
        contradiction
    · by_cases heq : prior.val = terminal.val
      · have priorEq : prior = terminal := Fin.ext heq
        subst prior
        exact False.elim ((notLocal hinherited) hscope)
      · have hnonterminal : prior.val + 1 < spine.proxyCount := by
          omega
        by_cases hboundary : wire ∈ checked.val.boundary
        · have rootScope := contract.boundary_is_root_scoped wire hboundary
          exact False.elim (spine.proxy_ne_root prior
            (hscope.symm.trans rootScope))
        · exact False.elim
            (contract.nonterminal_has_no_nonboundary_wires prior
              hnonterminal wire hboundary hscope)
  · intro hexposed
    have rootScope := checked.property.boundary_is_root_scoped wire
      ((OpenConcreteDiagram.mem_exposedWires checked.val wire).1 hexposed)
    have rootEncloses : checked.val.diagram.Encloses
        checked.val.diagram.root (spine.proxy terminal) :=
      checked.property.diagram_well_formed.all_regions_reach_root
        (spine.proxy terminal)
    have hextended : wire ∈ leaf.inheritedWires.extend
        (spine.proxy terminal) :=
      (leaf.wiresExact.mem_iff wire).2 (by simpa [rootScope] using rootEncloses)
    rw [ConcreteElaboration.WireContext.extend, List.mem_append] at hextended
    rcases hextended with hinherited | hlocal
    · exact hinherited
    · have localScope :=
        (ConcreteElaboration.mem_exactScopeWires checked.val.diagram
          (spine.proxy terminal) wire).1 hlocal
      exact False.elim (spine.proxy_ne_root terminal
        (localScope.symm.trans rootScope))

/-- Canonical finite reindexing between the compiler's terminal inherited
context and the pattern's exposed-wire carrier. -/
def Region.ContextPath.CompilerLeaf.inheritedExposedEquiv
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (contract : spine.TerminalBodyContract checked.val)
    (hnonempty : spine.proxyCount ≠ 0)
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (terminal : Fin spine.proxyCount)
    (terminal_is_last : terminal.val = spine.proxyCount - 1)
    (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram
      (spine.proxy terminal) witness) :
    FiniteEquiv (Fin leaf.inheritedWires.length)
      (Fin checked.val.exposedWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin checked.val.diagram.wireCount))
    leaf.inheritedWires checked.val.exposedWires
    (by
      have extendedNodup := leaf.wiresExact.nodup
      rw [ConcreteElaboration.WireContext.extend,
        List.nodup_append] at extendedNodup
      exact extendedNodup.1)
    checked.val.exposedWires_nodup
    (fun wire => (leaf.inherited_mem_iff_exposed checked spine contract
      hnonempty witness terminal terminal_is_last wire).symm)

theorem Region.ContextPath.CompilerLeaf.inheritedExposedEquiv_spec
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (contract : spine.TerminalBodyContract checked.val)
    (hnonempty : spine.proxyCount ≠ 0)
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (terminal : Fin spine.proxyCount)
    (terminal_is_last : terminal.val = spine.proxyCount - 1)
    (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram
      (spine.proxy terminal) witness)
    (index : Fin leaf.inheritedWires.length) :
    checked.val.exposedWires.get
        (leaf.inheritedExposedEquiv checked spine contract hnonempty witness
          terminal terminal_is_last index) =
      leaf.inheritedWires.get index :=
  FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin checked.val.diagram.wireCount))
    leaf.inheritedWires checked.val.exposedWires _ _ _ index

/-- Every relation variable in the terminal compiler context is owned by one
of the designated proxy bubbles.  This is the relation half of the terminal
lexical interface; the sheet alternative is impossible because enumeration
binders are bubbles. -/
theorem Region.ContextPath.CompilerLeaf.binder_is_proxy
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (terminal : Fin spine.proxyCount)
    (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram
      (spine.proxy terminal) witness)
    (index : Fin witness.toFocus.holeRels.length) :
    ∃ proxy : Fin spine.proxyCount,
      leaf.binderEnumeration.binder index = spine.proxy proxy := by
  have hencloses := leaf.binderEnumeration.encloses index
  rcases BinderSpine.enclosing_proxy_is_root_or_proxy checked spine terminal
      hencloses with
    hroot | ⟨proxy, _, hproxy⟩
  · obtain ⟨parent, hbubble⟩ := leaf.binderEnumeration.bubble index
    have hsheet := checked.property.diagram_well_formed.root_is_sheet
    rw [hroot, hsheet] at hbubble
    contradiction
  · exact ⟨proxy, hproxy⟩

/-- A terminal relation variable and its owning proxy carry definitionally
the same arity. -/
theorem Region.ContextPath.CompilerLeaf.binder_proxy_arity
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    {site : Fin checked.val.diagram.regionCount}
    {body : Region signature outer rels} {path : List Nat}
    (witness : Region.ContextPath body path)
    (leaf : Region.ContextPath.CompilerLeaf checked.val.diagram site witness)
    (index : Fin witness.toFocus.holeRels.length)
    (proxy : Fin spine.proxyCount)
    (hproxy : leaf.binderEnumeration.binder index = spine.proxy proxy) :
    witness.toFocus.holeRels.get index = spine.arity proxy := by
  obtain ⟨parent, hbubble⟩ := leaf.binderEnumeration.bubble index
  rw [hproxy, spine.proxy_region] at hbubble
  exact (CRegion.bubble.inj hbubble |>.2).symm

end Splice

end VisualProof.Diagram
