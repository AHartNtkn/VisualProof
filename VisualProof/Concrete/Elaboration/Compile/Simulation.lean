import VisualProof.Concrete.Elaboration.Compile.Region

/-! Generic local simulation of concrete compiler calls. -/

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- The recursive-call signature consumed by the direct occurrence compiler. -/
abbrev RegionCompiler (diagram : Diagram) :=
  ∀ {rels : RelCtx}, (region : Fin diagram.regionCount) →
    (context : WireContext diagram) → BinderContext diagram rels →
      Option (Region context.length rels)

/-- Replace one exact recursive compiler call family.  The replacement is an
explicit caller input; this definition performs no compilation or search. -/
def RegionCompiler.overrideAt (base : RegionCompiler diagram)
    (terminal : Fin diagram.regionCount)
    (replacement : ∀ {rels : RelCtx}, (context : WireContext diagram) →
      BinderContext diagram rels → Option (Region context.length rels)) :
    RegionCompiler diagram :=
  fun region context binders =>
    if region = terminal then replacement context binders
    else base region context binders

@[simp] theorem RegionCompiler.overrideAt_terminal
    (base : RegionCompiler diagram) (terminal : Fin diagram.regionCount)
    (replacement : ∀ {rels : RelCtx}, (context : WireContext diagram) →
      BinderContext diagram rels → Option (Region context.length rels))
    (context : WireContext diagram) (binders : BinderContext diagram rels) :
    base.overrideAt terminal replacement terminal context binders =
      replacement context binders := by
  simp [RegionCompiler.overrideAt]

@[simp] theorem RegionCompiler.overrideAt_away
    (base : RegionCompiler diagram) (terminal : Fin diagram.regionCount)
    (replacement : ∀ {rels : RelCtx}, (context : WireContext diagram) →
      BinderContext diagram rels → Option (Region context.length rels))
    (region : Fin diagram.regionCount) (away : region ≠ terminal)
    (context : WireContext diagram) (binders : BinderContext diagram rels) :
    base.overrideAt terminal replacement region context binders =
      base region context binders := by
  simp [RegionCompiler.overrideAt, away]

/-- One unfuelled region-compiler layer over an explicit recursive compiler. -/
def compileRegionStep? (diagram : Diagram)
    (recurse : RegionCompiler diagram) (region : Fin diagram.regionCount)
    (context : WireContext diagram) (binders : BinderContext diagram rels) :
    Option (Region context.length rels) := do
  let items ← compileOccurrencesWith? diagram recurse
    (context.extend region) binders (localOccurrences diagram region)
  pure (finishRegion diagram context region items)

theorem compileRegion?_succ_eq_step (diagram : Diagram) (fuel : Nat)
    (region : Fin diagram.regionCount) (context : WireContext diagram)
    (binders : BinderContext diagram rels) :
    compileRegion? diagram (fuel + 1) region context binders =
      compileRegionStep? diagram (compileRegion? diagram fuel) region context
        binders := by
  rfl

/-- Concrete identity maps used by a local compiler simulation.  Region and
binder maps are distinct because an inserted node's lexical binder need not
be the image of its containing region. -/
structure CompilerDiagramMap (source target : Diagram) where
  regionMap : Fin source.regionCount → Fin target.regionCount
  binderMap : Fin source.regionCount → Fin target.regionCount
  nodeMap : Fin source.nodeCount → Fin target.nodeCount

def CompilerDiagramMap.mapOccurrence
    (mapping : CompilerDiagramMap source target) :
    LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount
  | .node node => .node (mapping.nodeMap node)
  | .child child => .child (mapping.regionMap child)

/-- Exact laws for simulating one fixed direct-occurrence call.  Laws are
required only for members of the source list being transported, allowing a
caller to reserve its terminal occurrence for a separate derivation fold. -/
structure CompilerCallSimulation
    {source target : Diagram} (mapping : CompilerDiagramMap source target)
    {sourceRels targetRels : RelCtx}
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (sourceOccurrences :
      List (LocalOccurrence source.regionCount source.nodeCount)) where
  wireMap : Fin sourceContext.length → Fin targetContext.length
  relationMap : RelationRenaming sourceRels targetRels
  node_eq : ∀ node, .node node ∈ sourceOccurrences →
    target.nodes (mapping.nodeMap node) =
      match source.nodes node with
      | .atom region binder =>
          .atom (mapping.regionMap region) (mapping.binderMap binder)
      | .identity region arity =>
          .identity (mapping.regionMap region) arity
  region_eq : ∀ child, .child child ∈ sourceOccurrences →
    target.regions (mapping.regionMap child) =
      match source.regions child with
      | .sheet => .sheet
      | .cut parent => .cut (mapping.regionMap parent)
      | .bubble parent arity => .bubble (mapping.regionMap parent) arity
  ports_eq : ∀ node, .node node ∈ sourceOccurrences → ∀ port,
    resolvePort? target targetContext (mapping.nodeMap node) port =
      (resolvePort? source sourceContext node port).map wireMap
  binders_eq : ∀ node, .node node ∈ sourceOccurrences →
    ∀ region binder, source.nodes node = .atom region binder →
      targetBinders (mapping.binderMap binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relationMap relation.2⟩

namespace CompilerCallSimulation

variable {source target : Diagram}
variable {mapping : CompilerDiagramMap source target}
variable {sourceRels targetRels : RelCtx}
variable {sourceContext : WireContext source}
variable {targetContext : WireContext target}
variable {sourceBinders : BinderContext source sourceRels}
variable {targetBinders : BinderContext target targetRels}
variable {sourceOccurrences :
  List (LocalOccurrence source.regionCount source.nodeCount)}

def mapItem
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (item : Item sourceContext.length sourceRels) :
    Item targetContext.length targetRels :=
  (item.renameWires simulation.wireMap).renameRelations
    simulation.relationMap

def mapItems
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (items : ItemSeq sourceContext.length sourceRels) :
    ItemSeq targetContext.length targetRels :=
  (items.renameWires simulation.wireMap).renameRelations
    simulation.relationMap

def mapRegion
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (body : Region sourceContext.length sourceRels) :
    Region targetContext.length targetRels :=
  (body.renameWires simulation.wireMap).renameRelations
    simulation.relationMap

/-- Node compilation is the kernel map theorem instantiated with the exact
local simulation laws. -/
theorem compileNode?_map
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (node : Fin source.nodeCount) (member : .node node ∈ sourceOccurrences) :
    compileNode? target targetContext targetBinders (mapping.nodeMap node) =
      (compileNode? source sourceContext sourceBinders node).map
        simulation.mapItem := by
  apply VisualProof.Concrete.Elaboration.compileNode?_map sourceContext
    targetContext sourceBinders targetBinders node (mapping.nodeMap node)
    mapping.regionMap mapping.binderMap simulation.wireMap
    simulation.relationMap
  · exact simulation.node_eq node member
  · exact simulation.ports_eq node member
  · exact simulation.binders_eq node member

/-- Recursive child calls commute with one fixed call simulation.  Bubble
children lift the supplied relation map under their locally bound relation. -/
def RecursiveCallsMapped
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target) : Prop :=
  ∀ child, .child child ∈ sourceOccurrences →
    match source.regions child with
    | .sheet => True
    | .cut _ =>
        targetRecurse (mapping.regionMap child) targetContext targetBinders =
          (sourceRecurse child sourceContext sourceBinders).map
            simulation.mapRegion
    | .bubble _ arity =>
        targetRecurse (mapping.regionMap child) targetContext
            (targetBinders.push (mapping.regionMap child) arity) =
          (sourceRecurse child sourceContext
            (sourceBinders.push child arity)).map fun body =>
              (body.renameWires simulation.wireMap).renameRelations
                (RelationRenaming.lift simulation.relationMap arity)

/-- One mapped occurrence commutes when its recursive child call does. -/
theorem compileOccurrenceWith?_map
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target)
    (recursive : simulation.RecursiveCallsMapped sourceRecurse targetRecurse)
    (occurrence : LocalOccurrence source.regionCount source.nodeCount)
    (member : occurrence ∈ sourceOccurrences) :
    compileOccurrenceWith? target targetRecurse targetContext targetBinders
        (mapping.mapOccurrence occurrence) =
      (compileOccurrenceWith? source sourceRecurse sourceContext sourceBinders
        occurrence).map simulation.mapItem := by
  cases occurrence with
  | node node =>
      exact simulation.compileNode?_map node member
  | child child =>
      have targetKind := simulation.region_eq child member
      have recursiveCall := recursive child member
      cases sourceKind : source.regions child with
      | sheet =>
          simp only [sourceKind] at targetKind recursiveCall
          simp [compileOccurrenceWith?, CompilerDiagramMap.mapOccurrence,
            sourceKind, targetKind]
      | cut parent =>
          simp only [sourceKind] at targetKind recursiveCall
          simp only [compileOccurrenceWith?, CompilerDiagramMap.mapOccurrence,
            sourceKind, targetKind]
          rw [recursiveCall]
          cases sourceRecurse child sourceContext sourceBinders <;>
            simp [mapItem, mapRegion, Item.renameWires,
              Item.renameRelations]
      | bubble parent arity =>
          simp only [sourceKind] at targetKind recursiveCall
          simp only [compileOccurrenceWith?, CompilerDiagramMap.mapOccurrence,
            sourceKind, targetKind]
          rw [recursiveCall]
          cases sourceRecurse child sourceContext
              (sourceBinders.push child arity) <;>
            simp [mapItem, Item.renameWires, Item.renameRelations]

end CompilerCallSimulation

/-- Sequence compilation with simultaneous wire and relation transport.  This
is the relation-general local-list boundary missing from the kernel theorem. -/
theorem compileOccurrencesWith?_mapBoth
    {source target : Diagram} {sourceRels targetRels : RelCtx}
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target)
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (mapOccurrence : LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceOccurrences :
      List (LocalOccurrence source.regionCount source.nodeCount))
    (occurrenceMapped : ∀ occurrence, occurrence ∈ sourceOccurrences →
      compileOccurrenceWith? target targetRecurse targetContext targetBinders
          (mapOccurrence occurrence) =
        (compileOccurrenceWith? source sourceRecurse sourceContext
          sourceBinders occurrence).map fun item =>
            (item.renameWires wireMap).renameRelations relationMap) :
    compileOccurrencesWith? target targetRecurse targetContext targetBinders
        (sourceOccurrences.map mapOccurrence) =
      (compileOccurrencesWith? source sourceRecurse sourceContext sourceBinders
        sourceOccurrences).map fun items =>
          (items.renameWires wireMap).renameRelations relationMap := by
  induction sourceOccurrences with
  | nil => rfl
  | cons occurrence tail inductionHypothesis =>
      have head := occurrenceMapped occurrence (by simp)
      have tailMapped : ∀ current, current ∈ tail →
          compileOccurrenceWith? target targetRecurse targetContext
              targetBinders (mapOccurrence current) =
            (compileOccurrenceWith? source sourceRecurse sourceContext
              sourceBinders current).map fun item =>
                (item.renameWires wireMap).renameRelations relationMap := by
        intro current member
        exact occurrenceMapped current (by simp [member])
      specialize inductionHypothesis tailMapped
      cases sourceHead : compileOccurrenceWith? source sourceRecurse
          sourceContext sourceBinders occurrence with
      | none =>
          simp [sourceHead] at head
          simp [compileOccurrencesWith?, sourceHead, head]
      | some sourceItem =>
          simp [sourceHead] at head
          cases sourceTail : compileOccurrencesWith? source sourceRecurse
              sourceContext sourceBinders tail with
          | none =>
              simp [sourceTail] at inductionHypothesis
              simp [compileOccurrencesWith?, sourceHead, sourceTail, head,
                inductionHypothesis]
          | some sourceItems =>
              simp [sourceTail] at inductionHypothesis
              simp [compileOccurrencesWith?, sourceHead, sourceTail, head,
                inductionHypothesis, ItemSeq.renameWires,
                ItemSeq.renameRelations]

namespace CompilerCallSimulation

variable {source target : Diagram}
variable {mapping : CompilerDiagramMap source target}
variable {sourceRels targetRels : RelCtx}
variable {sourceContext : WireContext source}
variable {targetContext : WireContext target}
variable {sourceBinders : BinderContext source sourceRels}
variable {targetBinders : BinderContext target targetRels}
variable {sourceOccurrences :
  List (LocalOccurrence source.regionCount source.nodeCount)}

/-- Transport the entire local occurrence list through one exact call
simulation. -/
theorem compileOccurrencesWith?_map
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      sourceBinders targetBinders sourceOccurrences)
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target)
    (recursive : simulation.RecursiveCallsMapped sourceRecurse targetRecurse) :
    compileOccurrencesWith? target targetRecurse targetContext targetBinders
        (sourceOccurrences.map mapping.mapOccurrence) =
      (compileOccurrencesWith? source sourceRecurse sourceContext sourceBinders
        sourceOccurrences).map simulation.mapItems := by
  apply VisualProof.Concrete.Elaboration.compileOccurrencesWith?_mapBoth
  intro occurrence member
  exact simulation.compileOccurrenceWith?_map sourceRecurse targetRecurse
    recursive occurrence member

/-- At an unchanged relation context, the kernel's wire-only list map is the
exact specialization of a call simulation. -/
theorem compileOccurrencesWith?_map_sameRels
    {rels : RelCtx}
    {sourceBinders' : BinderContext source rels}
    {targetBinders' : BinderContext target rels}
    (simulation : CompilerCallSimulation mapping sourceContext targetContext
      (sourceRels := rels) (targetRels := rels)
      sourceBinders' targetBinders' sourceOccurrences)
    (relationEq : (simulation.relationMap : RelationRenaming rels rels) =
      (fun {arity} (relation : RelVar rels arity) => relation))
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target)
    (recursive : simulation.RecursiveCallsMapped sourceRecurse targetRecurse) :
    compileOccurrencesWith? target targetRecurse targetContext targetBinders'
        (sourceOccurrences.map mapping.mapOccurrence) =
      (compileOccurrencesWith? source sourceRecurse sourceContext sourceBinders'
        sourceOccurrences).map (ItemSeq.renameWires simulation.wireMap) := by
  apply VisualProof.Concrete.Elaboration.compileOccurrencesWith?_map
  intro occurrence member
  have mapped := simulation.compileOccurrenceWith?_map sourceRecurse
    targetRecurse recursive occurrence member
  have mapItemEq : simulation.mapItem =
      Item.renameWires simulation.wireMap := by
    funext item
    unfold mapItem
    rw [relationEq]
    exact Item.renameRelations_id _
  rw [mapItemEq] at mapped
  exact mapped

/-- Simulate one complete region layer.  The recursive compilers are explicit,
so a later route fold may supply an unrelated terminal computation while this
theorem handles only the locally mapped occurrence list. -/
theorem compileRegionStep?_map
    {sourceRegion : Fin source.regionCount}
    {targetRegion : Fin target.regionCount}
    (sourceContext : WireContext source) (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (simulation : CompilerCallSimulation mapping
      (sourceContext.extend sourceRegion) (targetContext.extend targetRegion)
      sourceBinders targetBinders (localOccurrences source sourceRegion))
    (sourceRecurse : RegionCompiler source)
    (targetRecurse : RegionCompiler target)
    (recursive : simulation.RecursiveCallsMapped sourceRecurse targetRecurse)
    (targetOccurrences : localOccurrences target targetRegion =
      (localOccurrences source sourceRegion).map mapping.mapOccurrence) :
    compileRegionStep? target targetRecurse targetRegion targetContext
        targetBinders =
      (compileOccurrencesWith? source sourceRecurse
        (sourceContext.extend sourceRegion) sourceBinders
        (localOccurrences source sourceRegion)).map fun items =>
          finishRegion target targetContext targetRegion
            (simulation.mapItems items) := by
  unfold compileRegionStep?
  rw [targetOccurrences]
  rw [simulation.compileOccurrencesWith?_map sourceRecurse targetRecurse
    recursive]
  cases compileOccurrencesWith? source sourceRecurse
      (sourceContext.extend sourceRegion) sourceBinders
      (localOccurrences source sourceRegion) <;> rfl

end CompilerCallSimulation

end VisualProof.Concrete.Elaboration
