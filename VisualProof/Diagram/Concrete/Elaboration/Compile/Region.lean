import VisualProof.Diagram.Concrete.Elaboration.Compile.Kernel

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

/-- Package compiled direct occurrences with the wires locally bound here. -/
def finishRegion (d : ConcreteDiagram)
    (context : WireContext d) (region : Fin d.regionCount)
    (items : ItemSeq signature (context.extend region).length rels) :
    Region signature context.length rels :=
  .mk (exactScopeWires d region).length
    (items.castWiresEq (WireContext.length_extend context region))

/-- Package the root after separating ambient from locally bound wires. -/
def finishRoot (ambient locals : WireContext d)
    (items : ItemSeq signature (ambient ++ locals).length []) :
    Region signature ambient.length [] :=
  .mk locals.length (items.castWiresEq (by simp))

theorem regionIso_of_cast
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq signature sourceExtended rels)
    (targetItems : ItemSeq signature targetExtended rels)
    (hitems : ItemSeqIso signature
      (castFinEquiv sourceEq targetEq
        (extendWireEquiv ambient localEquiv)) rels
      sourceItems targetItems) :
    RegionIso signature ambient rels
      (.mk sourceLocal (sourceItems.castWiresEq sourceEq))
      (.mk targetLocal (targetItems.castWiresEq targetEq)) := by
  subst sourceExtended
  subst targetExtended
  simpa using RegionIso.mk localEquiv hitems

/-- Fuelled region kernel of the sole concrete elaborator. -/
def compileRegion? (signature : List Nat) (d : ConcreteDiagram) :
    Nat -> (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (Region signature context.length rels)
  | 0, _, _, _ => none
  | fuel + 1, region, context, binders => do
      let extended := context.extend region
      let items <- compileOccurrencesWith? signature d
        (compileRegion? signature d fuel) extended binders
        (localOccurrences d region)
      pure (finishRegion d context region items)

/--
The single proof-independent sheet compiler. `ambient` wires become the outer
interface and `locals` become the root region's locally bound wires. Descendant
regions are compiled only by `compileRegion?`.
-/
def compileRoot? (signature : List Nat) (d : ConcreteDiagram)
    (ambient locals : WireContext d) :
    Option (Region signature ambient.length []) := do
  let rootWires := ambient ++ locals
  let items <- compileOccurrencesWith? signature d
    (compileRegion? signature d d.regionCount)
    rootWires BinderContext.empty (localOccurrences d d.root)
  pure (finishRoot ambient locals items)

theorem compileRegion?_appendRight
    (hwf : d.WellFormed signature) (suffix : List Nat) :
    ∀ {rels : RelCtx} (fuel : Nat) (region : Fin d.regionCount)
      (context : WireContext d) (binders : BinderContext d rels),
      compileRegion? (signature ++ suffix) d fuel region context binders =
        (compileRegion? signature d fuel region context binders).map
          (Region.renameNamed (NamedRenaming.appendRight signature suffix)) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region context binders
      rfl
  | succ fuel ih =>
      intro region context binders
      have hitems := compileOccurrencesWith?_appendRight hwf suffix
        (compileRegion? signature d fuel)
        (compileRegion? (signature ++ suffix) d fuel)
        (fun child childContext childBinders =>
          ih child childContext childBinders)
        (context.extend region) binders (localOccurrences d region)
      cases hsource : compileOccurrencesWith? signature d
          (compileRegion? signature d fuel) (context.extend region) binders
          (localOccurrences d region) with
      | none =>
          simp [hsource] at hitems
          simp [compileRegion?, hsource, hitems]
      | some items =>
          simp [hsource] at hitems
          simp [compileRegion?, hsource, hitems, finishRegion,
            Region.renameNamed]

theorem compileRoot?_appendRight
    (hwf : d.WellFormed signature) (suffix : List Nat)
    (ambient locals : WireContext d) :
    compileRoot? (signature ++ suffix) d ambient locals =
      (compileRoot? signature d ambient locals).map
        (Region.renameNamed (NamedRenaming.appendRight signature suffix)) := by
  have hitems := compileOccurrencesWith?_appendRight hwf suffix
    (compileRegion? signature d d.regionCount)
    (compileRegion? (signature ++ suffix) d d.regionCount)
    (fun region context binders =>
      compileRegion?_appendRight hwf suffix d.regionCount region context binders)
    (ambient ++ locals) BinderContext.empty (localOccurrences d d.root)
  cases hsource : compileOccurrencesWith? signature d
      (compileRegion? signature d d.regionCount) (ambient ++ locals)
      BinderContext.empty (localOccurrences d d.root) with
  | none =>
      simp [hsource] at hitems
      simp [compileRoot?, hsource, hitems]
  | some items =>
      simp [hsource] at hitems
      simp [compileRoot?, hsource, hitems, finishRoot, Region.renameNamed]

theorem compileRoot?_closed_eq_compileRegion?
    (signature : List Nat) (d : ConcreteDiagram) :
    compileRoot? signature d [] (exactScopeWires d d.root) =
      compileRegion? signature d (d.regionCount + 1) d.root []
        BinderContext.empty := by
  rfl

theorem compileRegion?_equivariant {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceFuel targetFuel : Nat} {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length)}
    (hwires : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetExact : (targetContext.extend (iso.regions region)).Exact
      (iso.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : BinderContextsAgree iso sourceBinders targetBinders)
    {sourceBody : Region signature sourceContext.length rels}
    {targetBody : Region signature targetContext.length rels}
    (hsource : compileRegion? signature source sourceFuel region sourceContext
      sourceBinders = some sourceBody)
    (htargetResult : compileRegion? signature target targetFuel
      (iso.regions region)
      targetContext targetBinders = some targetBody) :
    RegionIso signature ambient rels sourceBody targetBody := by
  induction sourceFuel generalizing targetFuel region sourceContext
      targetContext rels sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [compileRegion?] at hsource
  | succ sourceFuel ih =>
      cases targetFuel with
      | zero => simp [compileRegion?] at htargetResult
      | succ targetFuel =>
          let sourceExtended := sourceContext.extend region
          let targetExtended := targetContext.extend (iso.regions region)
          let extended := extendedContextEquiv iso sourceContext targetContext
            ambient region
          have hwiresExtended : WireContextsAgree iso sourceExtended targetExtended
              extended := by
            exact WireContextsAgree.extend hwires region
          have hoccurrence : forall
              (occurrence : LocalOccurrence source.regionCount source.nodeCount)
              (_ : occurrence ∈ localOccurrences source region)
              (sourceItem : Item signature sourceExtended.length rels)
              (targetItem : Item signature targetExtended.length rels),
              compileOccurrenceWith? signature source
                  (compileRegion? signature source sourceFuel) sourceExtended
                  sourceBinders
                  occurrence = some sourceItem →
              compileOccurrenceWith? signature target
                  (compileRegion? signature target targetFuel) targetExtended
                  targetBinders
                  (renameOccurrence iso occurrence) = some targetItem →
              ItemIso signature extended rels sourceItem targetItem := by
            intro occurrence hoccurrenceMem sourceItem targetItem
              hsourceItem htargetItem
            cases occurrence with
            | node node =>
                exact compileNode?_equivariant iso htarget hwiresExtended
                  htargetExact.nodup hbinders node
                  (by simpa [compileOccurrenceWith?] using hsourceItem)
                  (by simpa [compileOccurrenceWith?, renameOccurrence] using htargetItem)
            | child child =>
                simp only [renameOccurrence, compileOccurrenceWith?]
                  at hsourceItem htargetItem
                have hregionEq := iso.regions_eq child
                cases hchild : source.regions child with
                | sheet =>
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    simp [hchild] at hsourceItem
                | cut parent =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        hoccurrenceMem
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparentSource
                    subst parent
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    have hparentTarget :
                        (target.regions (iso.regions child)).parent? =
                          some (iso.regions region) := by
                      rw [<- hregionEq]
                      rfl
                    have hchildExact := htargetExact.extend_child htarget hparentTarget
                    rw [<- hregionEq] at htargetItem
                    simp only [hchild] at hsourceItem htargetItem
                    cases hsourceBody : compileRegion? signature source sourceFuel child
                        sourceExtended sourceBinders with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion? signature target targetFuel
                            (iso.regions child) targetExtended targetBinders with
                        | none => simp [htargetBody] at htargetItem
                        | some compiledTarget =>
                            simp [htargetBody] at htargetItem
                            subst targetItem
                            apply ItemIso.cut
                            exact ih hwiresExtended hchildExact hbinders
                              hsourceBody htargetBody
                | bubble parent arity =>
                    have hparentSource :=
                      (mem_localOccurrences_child source region child).mp
                        hoccurrenceMem
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparentSource
                    subst parent
                    rw [hchild] at hregionEq
                    simp only [CRegion.rename] at hregionEq
                    have hparentTarget :
                        (target.regions (iso.regions child)).parent? =
                          some (iso.regions region) := by
                      rw [<- hregionEq]
                      rfl
                    have hchildExact := htargetExact.extend_child htarget hparentTarget
                    have hchildBinders := hbinders.push child arity
                    rw [<- hregionEq] at htargetItem
                    simp only [hchild] at hsourceItem htargetItem
                    cases hsourceBody : compileRegion? signature source sourceFuel child
                        sourceExtended (sourceBinders.push child arity) with
                    | none => simp [hsourceBody] at hsourceItem
                    | some compiledSource =>
                        simp [hsourceBody] at hsourceItem
                        subst sourceItem
                        cases htargetBody : compileRegion? signature target targetFuel
                            (iso.regions child) targetExtended
                            (targetBinders.push (iso.regions child) arity) with
                        | none => simp [htargetBody] at htargetItem
                        | some compiledTarget =>
                            simp [htargetBody] at htargetItem
                            subst targetItem
                            apply ItemIso.bubble
                            exact ih hwiresExtended hchildExact hchildBinders
                              hsourceBody htargetBody
          simp only [compileRegion?] at hsource htargetResult
          cases hsourceItems : compileOccurrencesWith? signature source
              (compileRegion? signature source sourceFuel) sourceExtended sourceBinders
              (localOccurrences source region) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : compileOccurrencesWith? signature target
                  (compileRegion? signature target targetFuel) targetExtended
                  targetBinders
                  (localOccurrences target (iso.regions region)) with
              | none => simp [targetExtended, htargetItems] at htargetResult
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htargetResult
                  subst targetBody
                  have hsourceLength := compileOccurrencesWith?_length
                    (compileRegion? signature source sourceFuel) sourceExtended
                    sourceBinders hsourceItems
                  have htargetLength := compileOccurrencesWith?_length
                    (compileRegion? signature target targetFuel) targetExtended
                    targetBinders htargetItems
                  let positions : FiniteEquiv (Fin sourceItems.length)
                      (Fin targetItems.length) :=
                    castFinEquiv hsourceLength htargetLength
                      (localOccurrenceEquiv iso region)
                  have hitems : ItemSeqIso signature extended rels
                      sourceItems targetItems := by
                    apply ItemSeqIso.permute positions
                    intro sourceIndex
                    let occurrenceIndex : Fin (localOccurrences source region).length :=
                      Fin.cast hsourceLength sourceIndex
                    let targetOccurrenceIndex :=
                      localOccurrenceEquiv iso region occurrenceIndex
                    have hsourceGet := compileOccurrencesWith?_get
                      (compileRegion? signature source sourceFuel) sourceExtended
                      sourceBinders hsourceItems occurrenceIndex
                    have htargetGet := compileOccurrencesWith?_get
                      (compileRegion? signature target targetFuel) targetExtended
                      targetBinders htargetItems targetOccurrenceIndex
                    rw [localOccurrenceEquiv_spec iso region occurrenceIndex] at htargetGet
                    have hsourcePosition : Fin.cast hsourceLength.symm
                        occurrenceIndex = sourceIndex := by
                      apply Fin.ext
                      rfl
                    have htargetPosition : Fin.cast htargetLength.symm
                        targetOccurrenceIndex = positions sourceIndex := by
                      apply Fin.ext
                      rfl
                    rw [hsourcePosition] at hsourceGet
                    rw [htargetPosition] at htargetGet
                    exact hoccurrence _ (List.get_mem _ _) _ _
                      hsourceGet htargetGet
                  simpa only [finishRegion, sourceExtended, targetExtended,
                    extended, extendedContextEquiv] using
                    regionIso_of_cast
                      (WireContext.length_extend sourceContext region)
                      (WireContext.length_extend targetContext (iso.regions region))
                      ambient (localWireEquiv iso region) sourceItems targetItems hitems

/-- Equivariance of one compiled direct occurrence, with recursive child
regions discharged by the public region-kernel theorem. -/
theorem compileOccurrenceWith?_equivariant
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceFuel targetFuel : Nat} {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetExact : targetContext.Exact (iso.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : BinderContextsAgree iso sourceBinders targetBinders)
    (occurrence : LocalOccurrence source.regionCount source.nodeCount)
    (hoccurrence : occurrence ∈ localOccurrences source region)
    {sourceItem : Item signature sourceContext.length rels}
    {targetItem : Item signature targetContext.length rels}
    (hsource : compileOccurrenceWith? signature source
      (compileRegion? signature source sourceFuel) sourceContext sourceBinders
      occurrence = some sourceItem)
    (htargetResult : compileOccurrenceWith? signature target
      (compileRegion? signature target targetFuel) targetContext targetBinders
      (renameOccurrence iso occurrence) = some targetItem) :
    ItemIso signature ambient rels sourceItem targetItem := by
  cases occurrence with
  | node node =>
      exact compileNode?_equivariant iso htarget hwires htargetExact.nodup
        hbinders node
        (by simpa [compileOccurrenceWith?] using hsource)
        (by simpa [compileOccurrenceWith?, renameOccurrence] using htargetResult)
  | child child =>
      simp only [renameOccurrence, compileOccurrenceWith?]
        at hsource htargetResult
      have hregionEq := iso.regions_eq child
      cases hchild : source.regions child with
      | sheet =>
          simp [hchild] at hsource
      | cut parent =>
          have hparentSource :=
            (mem_localOccurrences_child source region child).mp hoccurrence
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparentSource
          subst parent
          rw [hchild] at hregionEq
          simp only [CRegion.rename] at hregionEq
          have hparentTarget :
              (target.regions (iso.regions child)).parent? =
                some (iso.regions region) := by
            rw [← hregionEq]
            rfl
          have hchildExact := htargetExact.extend_child htarget hparentTarget
          rw [← hregionEq] at htargetResult
          simp only [hchild] at hsource htargetResult
          cases hsourceBody : compileRegion? signature source sourceFuel child
              sourceContext sourceBinders with
          | none => simp [hsourceBody] at hsource
          | some compiledSource =>
              simp [hsourceBody] at hsource
              subst sourceItem
              cases htargetBody : compileRegion? signature target targetFuel
                  (iso.regions child) targetContext targetBinders with
              | none => simp [htargetBody] at htargetResult
              | some compiledTarget =>
                  simp [htargetBody] at htargetResult
                  subst targetItem
                  apply ItemIso.cut
                  exact compileRegion?_equivariant iso htarget hwires
                    hchildExact hbinders hsourceBody htargetBody
      | bubble parent arity =>
          have hparentSource :=
            (mem_localOccurrences_child source region child).mp hoccurrence
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparentSource
          subst parent
          rw [hchild] at hregionEq
          simp only [CRegion.rename] at hregionEq
          have hparentTarget :
              (target.regions (iso.regions child)).parent? =
                some (iso.regions region) := by
            rw [← hregionEq]
            rfl
          have hchildExact := htargetExact.extend_child htarget hparentTarget
          have hchildBinders := hbinders.push child arity
          rw [← hregionEq] at htargetResult
          simp only [hchild] at hsource htargetResult
          cases hsourceBody : compileRegion? signature source sourceFuel child
              sourceContext (sourceBinders.push child arity) with
          | none => simp [hsourceBody] at hsource
          | some compiledSource =>
              simp [hsourceBody] at hsource
              subst sourceItem
              cases htargetBody : compileRegion? signature target targetFuel
                  (iso.regions child) targetContext
                  (targetBinders.push (iso.regions child) arity) with
              | none => simp [htargetBody] at htargetResult
              | some compiledTarget =>
                  simp [htargetBody] at htargetResult
                  subst targetItem
                  apply ItemIso.bubble
                  exact compileRegion?_equivariant iso htarget hwires
                    hchildExact hchildBinders hsourceBody htargetBody

/-- Equivariance of any compiled sublist of direct occurrences.  The caller
supplies membership in one concrete region; occurrence order is retained. -/
theorem compileOccurrencesWith?_equivariant
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceFuel targetFuel : Nat} {region : Fin source.regionCount}
    {sourceContext : WireContext source} {targetContext : WireContext target}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : WireContextsAgree iso sourceContext targetContext ambient)
    (htargetExact : targetContext.Exact (iso.regions region))
    {sourceBinders : BinderContext source rels}
    {targetBinders : BinderContext target rels}
    (hbinders : BinderContextsAgree iso sourceBinders targetBinders)
    (occurrences : List (LocalOccurrence source.regionCount source.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences source region)
    {sourceItems : ItemSeq signature sourceContext.length rels}
    {targetItems : ItemSeq signature targetContext.length rels}
    (hsource : compileOccurrencesWith? signature source
      (compileRegion? signature source sourceFuel) sourceContext sourceBinders
      occurrences = some sourceItems)
    (htargetResult : compileOccurrencesWith? signature target
      (compileRegion? signature target targetFuel) targetContext targetBinders
      (occurrences.map (renameOccurrence iso)) = some targetItems) :
    ItemSeqIso signature ambient rels sourceItems targetItems := by
  let positions : FiniteEquiv (Fin occurrences.length)
      (Fin (occurrences.map (renameOccurrence iso)).length) :=
    FiniteEquiv.finCast (List.length_map (renameOccurrence iso)).symm
  apply compileOccurrencesWith?_iso
    (compileRegion? signature source sourceFuel)
    (compileRegion? signature target targetFuel)
    sourceContext targetContext sourceBinders targetBinders occurrences
    (occurrences.map (renameOccurrence iso)) hsource htargetResult positions
    ambient
  intro index
  have sourceGet := compileOccurrencesWith?_get
    (compileRegion? signature source sourceFuel) sourceContext sourceBinders
    hsource index
  have targetGet := compileOccurrencesWith?_get
    (compileRegion? signature target targetFuel) targetContext targetBinders
    htargetResult (positions index)
  have targetOccurrence :
      (occurrences.map (renameOccurrence iso)).get (positions index) =
        renameOccurrence iso (occurrences.get index) := by
    simp only [List.get_eq_getElem, List.getElem_map]
    congr 1
  rw [targetOccurrence] at targetGet
  exact compileOccurrenceWith?_equivariant iso htarget hwires htargetExact
    hbinders (occurrences.get index) (hlocal _ (List.get_mem _ _))
    sourceGet targetGet

/-- Public same-diagram region-kernel equivariance.  The caller supplies only
the observable wire-list correspondence and equality of lexical binder
contexts; the private concrete-isomorphism machinery remains encapsulated. -/
theorem compileRegion?_equivariant_sameDiagram
    (hwf : d.WellFormed signature)
    {sourceFuel targetFuel : Nat} {region : Fin d.regionCount}
    {sourceContext targetContext : WireContext d}
    {ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)}
    (hwires : ∀ index,
      targetContext.get (ambient index) = sourceContext.get index)
    (htargetExact : (targetContext.extend region).Exact region)
    {sourceBinders targetBinders : BinderContext d rels}
    (hbinders : targetBinders = sourceBinders)
    {sourceBody : Region signature sourceContext.length rels}
    {targetBody : Region signature targetContext.length rels}
    (hsource : compileRegion? signature d sourceFuel region sourceContext
      sourceBinders = some sourceBody)
    (htarget : compileRegion? signature d targetFuel region targetContext
      targetBinders = some targetBody) :
    RegionIso signature ambient rels sourceBody targetBody := by
  apply compileRegion?_equivariant (ConcreteIso.refl d) hwf hwires
    htargetExact
  · intro binder
    exact congrFun hbinders binder
  · exact hsource
  · exact htarget

/-- Every well-formed node compiles in wire and binder contexts covering its
containing region.  Public for graph-surgery commuting proofs. -/
theorem compileNode?_complete
    (hwf : d.WellFormed signature)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (hwires : context.Covers region) (hbinders : binders.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region) :
    exists item, compileNode? signature d context binders node = some item := by
  cases hnode : d.nodes node with
  | term nodeRegion freePorts term =>
      obtain ⟨output, houtput⟩ := checked_resolvePort?_complete hwf hwires
        (node := node) hregion (port := .output) (by
          simp [ConcreteDiagram.RequiresPort, hnode])
      obtain ⟨free, hfree⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion freePorts (fun index => .free index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.equation output (term.mapFree free), by
        simp [compileNode?, hnode, houtput, hfree]⟩
  | atom nodeRegion binder =>
      have hnodeRegion : nodeRegion = region := by simpa [hnode] using hregion
      subst nodeRegion
      obtain ⟨parent, arity, hbubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf hnode
      obtain ⟨relation, hrelation⟩ :=
        BinderContext.checked_atom_binder_available hwf hbinders hnode hbubble
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode, hbubble]
          exact ⟨index, rfl⟩)
      exact ⟨Item.atom relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩
  | named nodeRegion definition arity =>
      obtain ⟨relation, hrelation⟩ := checked_namedRel?_complete hwf hnode
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf hwires
        (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [ConcreteDiagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨Item.named relation arguments, by
        simp [compileNode?, hnode, hrelation, harguments]⟩

private theorem child_depth
    {d : ConcreteDiagram} {child parent : Fin d.regionCount} {depth : Nat}
    (hparent : (d.regions child).parent? = some parent)
    (hdepth : d.climb depth parent = some d.root) :
    d.climb (depth + 1) child = some d.root := by
  change d.climb (Nat.succ depth) child = some d.root
  simpa [ConcreteDiagram.climb, hparent] using hdepth

/-- A covered region with sufficient traversal fuel has a successful
intrinsic compilation.  Public because semantic simulations may need to
compare the same child under two exact presentations of its lexical wire
context. -/
theorem compileRegion?_complete
    (hwf : d.WellFormed signature)
    {fuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + fuel = d.regionCount + 1)
    (hwires : (context.extend region).Exact region)
    (hbinders : binders.Covers region) :
    exists body, compileRegion? signature d fuel region context binders = some body := by
  induction fuel generalizing depth region context rels with
  | zero =>
      have hpositive : 0 < d.regionCount + 1 - depth := by
        have hle := ParentTraversal.climb_to_root_steps_le_regionCount d
          hwf.root_is_sheet hwf.all_regions_reach_root hdepth
        omega
      exfalso
      omega
  | succ fuel ih =>
      let extended := context.extend region
      have hextended : extended.Exact region := by simpa [extended] using hwires
      have hoccurrence : forall occurrence,
          occurrence ∈ localOccurrences d region ->
          exists item,
            compileOccurrenceWith? signature d
              (compileRegion? signature d fuel) extended binders occurrence =
                some item := by
        intro occurrence hmem
        cases occurrence with
        | node node =>
            have hnodeRegion :=
              (mem_localOccurrences_node d region node).mp hmem
            simpa [compileOccurrenceWith?] using
              compileNode?_complete hwf hextended.covers hbinders hnodeRegion
        | child child =>
            have hparent :=
              (mem_localOccurrences_child d region child).mp hmem
            cases hchild : d.regions child with
            | sheet =>
                have hchildRoot : child = d.root :=
                  hwf.only_root_is_sheet child hchild
                subst child
                rw [hwf.root_is_sheet] at hparent
                simp [CRegion.parent?] at hparent
            | cut parent =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.covers_cut_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.cut body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
            | bubble parent arity =>
                have hparentEq : parent = region := by
                  simpa [hchild, CRegion.parent?] using hparent
                subst parent
                have hchildDepth := child_depth hparent hdepth
                have hchildFuel : depth + 1 + fuel = d.regionCount + 1 := by
                  omega
                have hchildWires := hextended.extend_child hwf hparent
                have hchildBinders :=
                  BinderContext.push_covers_bubble_child hbinders hchild
                obtain ⟨body, hbody⟩ := ih hchildDepth hchildFuel
                  hchildWires hchildBinders
                exact ⟨Item.bubble arity body, by
                  simp [compileOccurrenceWith?, hchild, hbody]⟩
      have hoccurrences : exists items,
          compileOccurrencesWith? signature d (compileRegion? signature d fuel)
            extended binders (localOccurrences d region) = some items := by
        exact compileOccurrencesWith?_complete
          (compileRegion? signature d fuel) extended binders _ hoccurrence
      obtain ⟨items, hitems⟩ := hoccurrences
      refine ⟨finishRegion d context region items, ?_⟩
      simp only [compileRegion?]
      change (compileOccurrencesWith? signature d (compileRegion? signature d fuel)
        extended binders (localOccurrences d region)).bind
          (fun result => some (finishRegion d context region result)) =
        some (finishRegion d context region items)
      rw [hitems]
      rfl

/-- Compile any chosen sublist of a region's direct occurrences from an exact
lexical context.  The fuel equation is the one required by recursive child
compilation; no whole-region recompilation is exposed to callers. -/
theorem compileDirectOccurrences?_complete
    (hwf : d.WellFormed signature)
    {fuel depth : Nat} {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (hdepth : d.climb depth region = some d.root)
    (hfuel : depth + 1 + fuel = d.regionCount + 1)
    (hwires : context.Exact region)
    (hbinders : binders.Covers region)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (hlocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d region) :
    ∃ items,
      compileOccurrencesWith? signature d (compileRegion? signature d fuel)
        context binders occurrences = some items := by
  apply compileOccurrencesWith?_complete
  intro occurrence occurrenceMember
  have direct := hlocal occurrence occurrenceMember
  cases occurrence with
  | node node =>
      have hnodeRegion := (mem_localOccurrences_node d region node).mp direct
      simpa [compileOccurrenceWith?] using
        compileNode?_complete hwf hwires.covers hbinders hnodeRegion
  | child child =>
      have hparent := (mem_localOccurrences_child d region child).mp direct
      cases hchild : d.regions child with
      | sheet =>
          have hchildRoot : child = d.root :=
            hwf.only_root_is_sheet child hchild
          subst child
          rw [hwf.root_is_sheet] at hparent
          simp [CRegion.parent?] at hparent
      | cut parent =>
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have hchildDepth := child_depth hparent hdepth
          have hchildWires := hwires.extend_child hwf hparent
          have hchildBinders := BinderContext.covers_cut_child hbinders hchild
          obtain ⟨body, hbody⟩ := compileRegion?_complete hwf hchildDepth
            hfuel hchildWires hchildBinders
          exact ⟨Item.cut body, by
            simp [compileOccurrenceWith?, hchild, hbody]⟩
      | bubble parent arity =>
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have hchildDepth := child_depth hparent hdepth
          have hchildWires := hwires.extend_child hwf hparent
          have hchildBinders :=
            BinderContext.push_covers_bubble_child hbinders hchild
          obtain ⟨body, hbody⟩ := compileRegion?_complete hwf hchildDepth
            hfuel hchildWires hchildBinders
          exact ⟨Item.bubble arity body, by
            simp [compileOccurrenceWith?, hchild, hbody]⟩

theorem openRootWires_exact
    {d : OpenConcreteDiagram} (hwf : d.WellFormed signature) :
    WireContext.Exact d.rootWires d.diagram.root := by
  constructor
  · exact d.rootWires_nodup
  · intro wire
    rw [OpenConcreteDiagram.mem_rootWires_iff d hwf]
    constructor
    · intro hscope
      rw [hscope]
      exact ConcreteDiagram.Encloses.refl d.diagram d.diagram.root
    · exact encloses_sheet_eq hwf.diagram_well_formed.root_is_sheet

theorem closedRootWires_exact (hwf : d.WellFormed signature) :
    WireContext.Exact
      (([] : WireContext d) ++ exactScopeWires d d.root) d.root := by
  simpa [WireContext.extend] using WireContext.root_exact hwf

theorem compileRoot?_complete
    (hwf : d.WellFormed signature)
    (ambient locals : WireContext d)
    (hwires : WireContext.Exact (ambient ++ locals) d.root) :
    exists body, compileRoot? signature d ambient locals = some body := by
  have hbinders : (BinderContext.empty : BinderContext d []).Covers d.root :=
    BinderContext.empty_covers_root hwf
  have hoccurrence : forall occurrence,
      occurrence ∈ localOccurrences d d.root →
      exists item,
        compileOccurrenceWith? signature d
            (compileRegion? signature d d.regionCount)
            (ambient ++ locals) BinderContext.empty occurrence = some item := by
    intro occurrence hmem
    cases occurrence with
    | node node =>
        have hnodeRegion :=
          (mem_localOccurrences_node d d.root node).mp hmem
        simpa [compileOccurrenceWith?] using
          compileNode?_complete hwf hwires.covers hbinders hnodeRegion
    | child child =>
        have hparent :=
          (mem_localOccurrences_child d d.root child).mp hmem
        cases hchild : d.regions child with
        | sheet =>
            have hchildRoot : child = d.root :=
              hwf.only_root_is_sheet child hchild
            subst child
            rw [hwf.root_is_sheet] at hparent
            simp [CRegion.parent?] at hparent
        | cut parent =>
            have hparentEq : parent = d.root := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            have hchildDepth : d.climb 1 child = some d.root := by
              simp [ConcreteDiagram.climb, hparent]
            have hchildWires := hwires.extend_child hwf hparent
            have hchildBinders :=
              BinderContext.covers_cut_child hbinders hchild
            obtain ⟨body, hbody⟩ := compileRegion?_complete hwf
              (depth := 1) (fuel := d.regionCount)
              hchildDepth (by omega) hchildWires hchildBinders
            exact ⟨Item.cut body, by
              simp [compileOccurrenceWith?, hchild, hbody]⟩
        | bubble parent arity =>
            have hparentEq : parent = d.root := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            have hchildDepth : d.climb 1 child = some d.root := by
              simp [ConcreteDiagram.climb, hparent]
            have hchildWires := hwires.extend_child hwf hparent
            have hchildBinders :=
              BinderContext.push_covers_bubble_child hbinders hchild
            obtain ⟨body, hbody⟩ := compileRegion?_complete hwf
              (depth := 1) (fuel := d.regionCount)
              hchildDepth (by omega) hchildWires hchildBinders
            exact ⟨Item.bubble arity body, by
              simp [compileOccurrenceWith?, hchild, hbody]⟩
  obtain ⟨items, hitems⟩ := compileOccurrencesWith?_complete
    (compileRegion? signature d d.regionCount)
    (ambient ++ locals) BinderContext.empty _ hoccurrence
  exact ⟨finishRoot ambient locals items, by
    simp only [compileRoot?]
    rw [hitems]
    rfl⟩

private theorem compileRoot?_equivariant_with_items
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : WireContextsAgree iso (sourceAmbient ++ sourceLocal)
      (targetAmbient ++ targetLocal) (appendContextEquiv ambient localEquiv))
    (htargetExact : WireContext.Exact (targetAmbient ++ targetLocal) target.root)
    {sourceBody : Region signature sourceAmbient.length []}
    {targetBody : Region signature targetAmbient.length []}
    (hsource : compileRoot? signature source sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? signature target targetAmbient targetLocal =
      some targetBody) :
    RegionIso signature ambient [] sourceBody targetBody ∧
      ∃ (sourceItems : ItemSeq signature
          (sourceAmbient ++ sourceLocal).length [])
        (targetItems : ItemSeq signature
          (targetAmbient ++ targetLocal).length []),
        sourceBody = finishRoot sourceAmbient sourceLocal sourceItems ∧
        targetBody = finishRoot targetAmbient targetLocal targetItems ∧
        compileOccurrencesWith? signature source
            (compileRegion? signature source source.regionCount)
            (sourceAmbient ++ sourceLocal) BinderContext.empty
            (localOccurrences source source.root) = some sourceItems ∧
        compileOccurrencesWith? signature target
            (compileRegion? signature target source.regionCount)
            (targetAmbient ++ targetLocal) BinderContext.empty
            (localOccurrences target target.root) = some targetItems ∧
        ItemSeqIso signature (appendContextEquiv ambient localEquiv) []
          sourceItems targetItems := by
  let sourceRoot := sourceAmbient ++ sourceLocal
  let targetRoot := targetAmbient ++ targetLocal
  let rootEquiv := appendContextEquiv ambient localEquiv
  have htargetExactMapped : WireContext.Exact targetRoot
      (iso.regions source.root) := by
    simpa only [targetRoot, iso.root_eq] using htargetExact
  have hbinders : BinderContextsAgree iso
      (BinderContext.empty : BinderContext source [])
      (BinderContext.empty : BinderContext target []) := by
    intro _
    rfl
  have hoccurrence : forall
      (occurrence : LocalOccurrence source.regionCount source.nodeCount)
      (_ : occurrence ∈ localOccurrences source source.root)
      (sourceItem : Item signature sourceRoot.length [])
      (targetItem : Item signature targetRoot.length []),
      compileOccurrenceWith? signature source
          (compileRegion? signature source source.regionCount)
          sourceRoot BinderContext.empty occurrence = some sourceItem ->
      compileOccurrenceWith? signature target
          (compileRegion? signature target source.regionCount)
          targetRoot BinderContext.empty
          (renameOccurrence iso occurrence) = some targetItem ->
      ItemIso signature rootEquiv [] sourceItem targetItem := by
    intro occurrence hoccurrenceMem sourceItem targetItem
      hsourceItem htargetItem
    cases occurrence with
    | node node =>
        exact compileNode?_equivariant iso htarget hwires
          htargetExact.nodup hbinders node
          (by simpa [sourceRoot, compileOccurrenceWith?] using hsourceItem)
          (by simpa [targetRoot, compileOccurrenceWith?, renameOccurrence]
            using htargetItem)
    | child child =>
        simp only [renameOccurrence, compileOccurrenceWith?]
          at hsourceItem htargetItem
        have hregionEq := iso.regions_eq child
        cases hchild : source.regions child with
        | sheet =>
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            simp [hchild] at hsourceItem
        | cut parent =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                hoccurrenceMem
            have hparentEq : parent = source.root := by
              simpa [hchild, CRegion.parent?] using hparentSource
            subst parent
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            have hparentTarget :
                (target.regions (iso.regions child)).parent? =
                  some (iso.regions source.root) := by
              rw [<- hregionEq]
              rfl
            have hchildExact :=
              htargetExactMapped.extend_child htarget hparentTarget
            rw [<- hregionEq] at htargetItem
            simp only [hchild] at hsourceItem htargetItem
            cases hsourceBody : compileRegion? signature source
                source.regionCount child sourceRoot BinderContext.empty with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion? signature target
                    source.regionCount (iso.regions child) targetRoot
                    BinderContext.empty with
                | none => simp [htargetBody] at htargetItem
                | some compiledTarget =>
                    simp [htargetBody] at htargetItem
                    subst targetItem
                    apply ItemIso.cut
                    exact compileRegion?_equivariant iso htarget hwires
                      hchildExact hbinders hsourceBody htargetBody
        | bubble parent arity =>
            have hparentSource :=
              (mem_localOccurrences_child source source.root child).mp
                hoccurrenceMem
            have hparentEq : parent = source.root := by
              simpa [hchild, CRegion.parent?] using hparentSource
            subst parent
            rw [hchild] at hregionEq
            simp only [CRegion.rename] at hregionEq
            have hparentTarget :
                (target.regions (iso.regions child)).parent? =
                  some (iso.regions source.root) := by
              rw [<- hregionEq]
              rfl
            have hchildExact :=
              htargetExactMapped.extend_child htarget hparentTarget
            have hchildBinders := hbinders.push child arity
            rw [<- hregionEq] at htargetItem
            simp only [hchild] at hsourceItem htargetItem
            cases hsourceBody : compileRegion? signature source
                source.regionCount child sourceRoot
                (BinderContext.empty.push child arity) with
            | none => simp [hsourceBody] at hsourceItem
            | some compiledSource =>
                simp [hsourceBody] at hsourceItem
                subst sourceItem
                cases htargetBody : compileRegion? signature target
                    source.regionCount (iso.regions child) targetRoot
                    (BinderContext.empty.push (iso.regions child) arity) with
                | none => simp [htargetBody] at htargetItem
                | some compiledTarget =>
                    simp [htargetBody] at htargetItem
                    subst targetItem
                    apply ItemIso.bubble
                    exact compileRegion?_equivariant iso htarget hwires
                      hchildExact hchildBinders hsourceBody htargetBody
  simp only [compileRoot?] at hsource htargetResult
  rw [<- iso.regionCount_eq, <- iso.root_eq] at htargetResult
  cases hsourceItems : compileOccurrencesWith? signature source
      (compileRegion? signature source source.regionCount)
      sourceRoot BinderContext.empty
      (localOccurrences source source.root) with
  | none => simp [sourceRoot, hsourceItems] at hsource
  | some sourceItems =>
      simp [sourceRoot, hsourceItems] at hsource
      subst sourceBody
      cases htargetItems : compileOccurrencesWith? signature target
          (compileRegion? signature target source.regionCount)
          targetRoot BinderContext.empty
          (localOccurrences target (iso.regions source.root)) with
      | none => simp [targetRoot, htargetItems] at htargetResult
      | some targetItems =>
          simp [targetRoot, htargetItems] at htargetResult
          subst targetBody
          have hsourceLength := compileOccurrencesWith?_length
            (compileRegion? signature source source.regionCount)
            sourceRoot BinderContext.empty hsourceItems
          have htargetLength := compileOccurrencesWith?_length
            (compileRegion? signature target source.regionCount)
            targetRoot BinderContext.empty htargetItems
          let positions : FiniteEquiv (Fin sourceItems.length)
              (Fin targetItems.length) :=
            castFinEquiv hsourceLength htargetLength
              (localOccurrenceEquiv iso source.root)
          have hitems : ItemSeqIso signature rootEquiv []
              sourceItems targetItems := by
            apply ItemSeqIso.permute positions
            intro sourceIndex
            let occurrenceIndex :
                Fin (localOccurrences source source.root).length :=
              Fin.cast hsourceLength sourceIndex
            let targetOccurrenceIndex :=
              localOccurrenceEquiv iso source.root occurrenceIndex
            have hsourceGet := compileOccurrencesWith?_get
              (compileRegion? signature source source.regionCount)
              sourceRoot BinderContext.empty hsourceItems occurrenceIndex
            have htargetGet := compileOccurrencesWith?_get
              (compileRegion? signature target source.regionCount)
              targetRoot BinderContext.empty htargetItems targetOccurrenceIndex
            rw [localOccurrenceEquiv_spec iso source.root occurrenceIndex]
              at htargetGet
            have hsourcePosition : Fin.cast hsourceLength.symm
                occurrenceIndex = sourceIndex := by
              apply Fin.ext
              rfl
            have htargetPosition : Fin.cast htargetLength.symm
                targetOccurrenceIndex = positions sourceIndex := by
              apply Fin.ext
              rfl
            rw [hsourcePosition] at hsourceGet
            rw [htargetPosition] at htargetGet
            exact hoccurrence _ (List.get_mem _ _) _ _
              hsourceGet htargetGet
          have hregion : RegionIso signature ambient []
              (finishRoot sourceAmbient sourceLocal sourceItems)
              (finishRoot targetAmbient targetLocal targetItems) := by
            simpa only [finishRoot, sourceRoot, targetRoot, rootEquiv] using
              regionIso_of_cast (by simp [sourceRoot]) (by simp [targetRoot])
                ambient localEquiv sourceItems targetItems hitems
          have hsourceItems' : compileOccurrencesWith? signature source
              (compileRegion? signature source source.regionCount)
              (sourceAmbient ++ sourceLocal) BinderContext.empty
              (localOccurrences source source.root) = some sourceItems := by
            simpa only [sourceRoot] using hsourceItems
          have htargetItems' : compileOccurrencesWith? signature target
              (compileRegion? signature target source.regionCount)
              (targetAmbient ++ targetLocal) BinderContext.empty
              (localOccurrences target target.root) = some targetItems := by
            simpa only [targetRoot, iso.root_eq] using htargetItems
          exact ⟨hregion, sourceItems, targetItems, rfl, rfl,
            rfl, htargetItems', hitems⟩

theorem compileRoot?_equivariant
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    {sourceAmbient : WireContext source} {targetAmbient : WireContext target}
    {sourceLocal : WireContext source} {targetLocal : WireContext target}
    {ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length)}
    {localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length)}
    (hwires : WireContextsAgree iso (sourceAmbient ++ sourceLocal)
      (targetAmbient ++ targetLocal) (appendContextEquiv ambient localEquiv))
    (htargetExact : WireContext.Exact (targetAmbient ++ targetLocal) target.root)
    {sourceBody : Region signature sourceAmbient.length []}
    {targetBody : Region signature targetAmbient.length []}
    (hsource : compileRoot? signature source sourceAmbient sourceLocal =
      some sourceBody)
    (htargetResult : compileRoot? signature target targetAmbient targetLocal =
      some targetBody) :
    RegionIso signature ambient [] sourceBody targetBody :=
  (compileRoot?_equivariant_with_items iso htarget hwires htargetExact
    hsource htargetResult).1

/-- Public root-context equivariance with every supplied root wire treated as
ambient.  Unlike `compileRoot?_equivariant`, its interface mentions only the
observable agreement of the two root lists and no private compiler relations.
It is the canonical bridge for pointwise open-root simulations. -/
theorem compileRoot?_equivariant_allAmbient
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    (sourceRoot : WireContext source) (targetRoot : WireContext target)
    (rootEquiv : FiniteEquiv (Fin sourceRoot.length) (Fin targetRoot.length))
    (hwires : ∀ index,
      targetRoot.get (rootEquiv index) = iso.wires (sourceRoot.get index))
    (htargetExact : WireContext.Exact targetRoot target.root)
    {sourceBody : Region signature sourceRoot.length []}
    {targetBody : Region signature targetRoot.length []}
    (hsource : compileRoot? signature source sourceRoot [] = some sourceBody)
    (htargetResult : compileRoot? signature target targetRoot [] =
      some targetBody) :
    RegionIso signature rootEquiv [] sourceBody targetBody := by
  have hroot : WireContextsAgree iso sourceRoot targetRoot rootEquiv := hwires
  have hempty : WireContextsAgree iso ([] : WireContext source)
      ([] : WireContext target) (FiniteEquiv.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have hall := appendContextsAgree hroot hempty
  exact compileRoot?_equivariant iso htarget
    (sourceAmbient := sourceRoot) (targetAmbient := targetRoot)
    (sourceLocal := []) (targetLocal := [])
    (ambient := rootEquiv) (localEquiv := FiniteEquiv.refl (Fin 0))
    hall (by simpa using htargetExact) hsource htargetResult

/-- Public item-sequence form of root-context equivariance.  This exposes the
compiler's context-sensitive payload independently of how a caller later
splits the complete root context into ambient and locally bound wires. -/
theorem compileRootItems?_equivariant
    {source target : ConcreteDiagram}
    (iso : ConcreteIso source target)
    (htarget : target.WellFormed signature)
    (sourceRoot : WireContext source) (targetRoot : WireContext target)
    (rootEquiv : FiniteEquiv (Fin sourceRoot.length) (Fin targetRoot.length))
    (hwires : ∀ index,
      targetRoot.get (rootEquiv index) = iso.wires (sourceRoot.get index))
    (htargetExact : WireContext.Exact targetRoot target.root)
    {sourceItems : ItemSeq signature sourceRoot.length []}
    {targetItems : ItemSeq signature targetRoot.length []}
    (hsource : compileOccurrencesWith? signature source
      (compileRegion? signature source source.regionCount)
      sourceRoot BinderContext.empty (localOccurrences source source.root) =
        some sourceItems)
    (htargetItems : compileOccurrencesWith? signature target
      (compileRegion? signature target target.regionCount)
      targetRoot BinderContext.empty (localOccurrences target target.root) =
        some targetItems) :
    ItemSeqIso signature rootEquiv [] sourceItems targetItems := by
  have hsourceRoot : compileRoot? signature source [] sourceRoot =
      some (finishRoot [] sourceRoot sourceItems) := by
    change (do
      let items ← compileOccurrencesWith? signature source
        (compileRegion? signature source source.regionCount)
        sourceRoot BinderContext.empty (localOccurrences source source.root)
      pure (finishRoot [] sourceRoot items)) =
        some (finishRoot [] sourceRoot sourceItems)
    rw [hsource]
    rfl
  have htargetRoot : compileRoot? signature target [] targetRoot =
      some (finishRoot [] targetRoot targetItems) := by
    change (do
      let items ← compileOccurrencesWith? signature target
        (compileRegion? signature target target.regionCount)
        targetRoot BinderContext.empty (localOccurrences target target.root)
      pure (finishRoot [] targetRoot items)) =
        some (finishRoot [] targetRoot targetItems)
    rw [htargetItems]
    rfl
  have hroot : WireContextsAgree iso sourceRoot targetRoot rootEquiv := hwires
  have hempty : WireContextsAgree iso ([] : WireContext source)
      ([] : WireContext target) (FiniteEquiv.refl (Fin 0)) := by
    intro index
    exact Fin.elim0 index
  have hall := appendContextsAgree hempty hroot
  have hcore := compileRoot?_equivariant_with_items iso htarget
    (sourceAmbient := []) (targetAmbient := [])
    (sourceLocal := sourceRoot) (targetLocal := targetRoot)
    (ambient := FiniteEquiv.refl (Fin 0)) (localEquiv := rootEquiv)
    hall (by simpa using htargetExact) hsourceRoot htargetRoot
  obtain ⟨_, compiledSource, compiledTarget, _, _,
      hcompiledSource, hcompiledTarget, hitems⟩ := hcore
  have hsourceEq : sourceItems = compiledSource := by
    apply Option.some.inj
    exact hsource.symm.trans (by simpa using hcompiledSource)
  have htargetComputation : compileOccurrencesWith? signature target
      (compileRegion? signature target source.regionCount)
      targetRoot BinderContext.empty (localOccurrences target target.root) =
        some targetItems := by
    simpa only [iso.regionCount_eq] using htargetItems
  have htargetEq : targetItems = compiledTarget := by
    apply Option.some.inj
    exact htargetComputation.symm.trans (by simpa using hcompiledTarget)
  subst compiledSource
  subst compiledTarget
  have hequiv :
      appendContextEquiv
          (sourceAmbient := ([] : WireContext source))
          (targetAmbient := ([] : WireContext target))
          (sourceLocal := sourceRoot) (targetLocal := targetRoot)
          (FiniteEquiv.refl (Fin 0)) rootEquiv =
        rootEquiv := by
    apply FiniteEquiv.ext
    intro index
    let sumIndex : Fin (0 + sourceRoot.length) := Fin.cast (by simp) index
    have hindex : Fin.cast (by simp) sumIndex = index := by
      apply Fin.ext
      rfl
    rw [← hindex]
    refine Fin.addCases (fun outer => Fin.elim0 outer) (fun localIndex => ?_)
      sumIndex
    apply Fin.ext
    simp [appendContextEquiv, castFinEquiv, extendWireEquiv]
    have hlocal : Fin.cast (by simp) localIndex =
        Fin.natAdd 0 localIndex := by
      apply Fin.ext
      simp
    rw [hlocal, Fin.addCases_right]
    rfl
  rw [hequiv] at hitems
  exact hitems

end VisualProof.Diagram.ConcreteElaboration
